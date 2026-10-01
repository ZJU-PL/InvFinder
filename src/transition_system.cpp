#include "transition_system.h"

#include <filesystem>
#include <stdexcept>
#include <unordered_set>
#include <utility>

namespace invfinder {
namespace {

z3::expr fresh(z3::context& ctx, const std::string& prefix, const z3::sort& sort) {
    return z3::expr(ctx, Z3_mk_fresh_const(ctx, prefix.c_str(), sort));
}

bool same(const z3::expr& a, const z3::expr& b) { return z3::eq(a, b); }

bool contains(const std::vector<z3::expr>& values, const z3::expr& value) {
    for (const auto& item : values) if (same(item, value)) return true;
    return false;
}

z3::expr_vector as_vector(z3::context& ctx, const std::vector<z3::expr>& values) {
    z3::expr_vector result(ctx);
    for (const auto& value : values) result.push_back(value);
    return result;
}

// Check both public native-Z3 inputs and the normalized reader output. Bound
// de Bruijn variables are allowed; all unbound symbols must be state variables.
void check_formula(const z3::expr& expression,
                   const std::vector<z3::expr>& allowed,
                   const std::string& label,
                   unsigned depth = 0) {
    if (expression.is_var()) {
        if (Z3_get_index_value(expression.ctx(), expression) >= depth)
            throw std::invalid_argument(label + ": unbound de Bruijn variable");
        return;
    }
    if (expression.is_quantifier()) {
        if (!expression.is_forall() && !expression.is_exists())
            throw std::invalid_argument(label + ": lambda terms are unsupported");
        const unsigned count = Z3_get_quantifier_num_bound(expression.ctx(), expression);
        check_formula(expression.body(), allowed, label, depth + count);
        return;
    }
    if (!expression.is_app()) return;
    if (expression.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
        if (expression.num_args() || !contains(allowed, expression))
            throw std::invalid_argument(label + ": unexpected free symbol " +
                                        expression.decl().name().str());
    }
    for (unsigned i = 0; i < expression.num_args(); ++i)
        check_formula(expression.arg(i), allowed, label, depth);
}

void collect_relations(const z3::expr& expression,
                       std::vector<z3::func_decl>& relations) {
    if (expression.is_quantifier()) {
        collect_relations(expression.body(), relations);
        return;
    }
    if (!expression.is_app()) return;
    if (expression.decl().decl_kind() == Z3_OP_UNINTERPRETED && expression.num_args()) {
        if (!expression.is_bool())
            throw std::runtime_error("CHC reader: uninterpreted theory functions are unsupported");
        bool present = false;
        for (const auto& relation : relations)
            if (z3::eq(relation, expression.decl())) present = true;
        if (!present) relations.push_back(expression.decl());
    }
    for (unsigned i = 0; i < expression.num_args(); ++i)
        collect_relations(expression.arg(i), relations);
}

bool is_relation(const z3::expr& expression, const z3::func_decl& relation) {
    return expression.is_app() && z3::eq(expression.decl(), relation);
}

bool has_relation(const z3::expr& expression, const z3::func_decl& relation) {
    if (is_relation(expression, relation)) return true;
    if (expression.is_quantifier()) return has_relation(expression.body(), relation);
    if (expression.is_app())
        for (unsigned i = 0; i < expression.num_args(); ++i)
            if (has_relation(expression.arg(i), relation)) return true;
    return false;
}

void conjuncts(const z3::expr& expression, std::vector<z3::expr>& output) {
    if (expression.is_and()) {
        for (unsigned i = 0; i < expression.num_args(); ++i)
            conjuncts(expression.arg(i), output);
    } else {
        output.push_back(expression);
    }
}

z3::expr open_universals(z3::expr clause, std::vector<z3::expr>& locals) {
    while (clause.is_forall()) {
        auto& ctx = clause.ctx();
        const unsigned count = Z3_get_quantifier_num_bound(ctx, clause);
        std::vector<z3::expr> opened;
        for (unsigned i = 0; i < count; ++i) {
            z3::sort sort(ctx, Z3_get_quantifier_bound_sort(ctx, clause, i));
            z3::expr value = fresh(ctx, "chc_local", sort);
            opened.push_back(value);
            locals.push_back(value);
        }
        z3::expr_vector replacement(ctx);
        // SMT-LIB binder order is the reverse of de Bruijn index order.
        for (auto it = opened.rbegin(); it != opened.rend(); ++it)
            replacement.push_back(*it);
        clause = clause.body().substitute(replacement);
    }
    return clause;
}

// Each link relates an interface state variable to a relation argument.
// Substitute plain local arguments first to avoid gratuitous quantifiers in
// ordinary CHCs. Repeated arguments remain equality constraints, as required.
z3::expr project(z3::expr condition,
                 const std::vector<z3::expr>& locals,
                 const std::vector<std::pair<z3::expr, z3::expr>>& links) {
    auto& ctx = condition.ctx();
    z3::expr_vector from(ctx), to(ctx);
    std::vector<z3::expr> mapped;
    for (const auto& link : links) {
        condition = condition && (link.first == link.second);
        if (contains(locals, link.second) && !contains(mapped, link.second)) {
            mapped.push_back(link.second);
            from.push_back(link.second);
            to.push_back(link.first);
        }
    }
    condition = condition.substitute(from, to).simplify();
    z3::expr_vector remaining(ctx);
    for (const auto& local : locals)
        if (!contains(mapped, local)) remaining.push_back(local);
    if (!remaining.empty()) condition = z3::exists(remaining, condition).simplify();
    return condition;
}

void append_links(std::vector<std::pair<z3::expr, z3::expr>>& links,
                  const std::vector<z3::expr>& vars,
                  const z3::expr& relation_application) {
    for (unsigned i = 0; i < vars.size(); ++i)
        links.emplace_back(vars[i], relation_application.arg(i));
}

} // namespace

transitionSystem::transitionSystem(z3::expr pre_, z3::expr trans_, z3::expr post_,
                                   std::vector<z3::expr> vars_,
                                   std::vector<z3::expr> vars_bar_,
                                   std::string logic_)
    : ctx(pre_.ctx()), pre(std::move(pre_)), trans(std::move(trans_)),
      post(std::move(post_)), vars(std::move(vars_)), vars_bar(std::move(vars_bar_)),
      logic(std::move(logic_)) {
    if (&trans.ctx() != &ctx || &post.ctx() != &ctx)
        throw std::invalid_argument("transition system: formulas must share a Z3 context");
    if (!pre.is_bool() || !trans.is_bool() || !post.is_bool())
        throw std::invalid_argument("transition system: pre/trans/post must be Boolean");
    if (vars.empty() || vars.size() != vars_bar.size())
        throw std::invalid_argument("transition system: matching nonempty state vectors required");
    std::vector<z3::expr> all;
    for (unsigned i = 0; i < vars.size(); ++i) {
        for (const auto& value : {vars[i], vars_bar[i]}) {
            if (&value.ctx() != &ctx || !value.is_const() || !value.is_bv() ||
                value.decl().decl_kind() != Z3_OP_UNINTERPRETED)
                throw std::invalid_argument("transition system: state must consist of bit-vector constants in one context");
            if (contains(all, value))
                throw std::invalid_argument("transition system: state and next-state variables must be distinct");
            all.push_back(value);
        }
        if (!z3::eq(vars[i].get_sort(), vars_bar[i].get_sort()))
            throw std::invalid_argument("transition system: current/next-state sort mismatch");
    }
    check_formula(pre, vars, "pre");
    check_formula(trans, all, "trans");
    check_formula(post, vars, "post");
}

z3::expr_vector transitionSystem::get_ori_consts() const { return as_vector(ctx, vars); }
z3::expr_vector transitionSystem::get_bar_consts() const { return as_vector(ctx, vars_bar); }
z3::expr_vector transitionSystem::get_all_consts() const {
    z3::expr_vector result(ctx);
    for (unsigned i = 0; i < vars.size(); ++i) {
        result.push_back(vars[i]);
        result.push_back(vars_bar[i]);
    }
    return result;
}

transitionSystem load_chc(z3::context& ctx, const std::string& filename) {
    if (!std::filesystem::is_regular_file(filename))
        throw std::runtime_error("CHC reader: input is not a regular file: " + filename);
    z3::expr_vector assertions(ctx);
    try {
        // The fixedpoint parser exposes commands that context::parse_file
        // silently omits. Use it only for parsing, never for solving, so mixed
        // assert/rule input cannot accidentally lose its transition rules.
        z3::fixedpoint parser(ctx);
        const auto queries = parser.from_file(filename.c_str());
        if (!parser.rules().empty() || !queries.empty())
            throw std::runtime_error("CHC reader: rule/query commands are unsupported; use assert/forall/=> clauses");
        assertions = parser.assertions();
    } catch (const z3::exception& error) {
        throw std::runtime_error("CHC reader: Z3 could not parse " + filename + ": " + error.msg());
    }
    if (assertions.empty())
        throw std::runtime_error("CHC reader: no assertions (use assert/forall/=> CHCs)");
    std::vector<z3::func_decl> relations;
    for (const auto& assertion : assertions) collect_relations(assertion, relations);
    if (relations.size() != 1)
        throw std::runtime_error("CHC reader: exactly one positive-arity relation is supported");
    const auto& relation = relations.front();
    std::vector<z3::expr> vars, vars_bar;
    for (unsigned i = 0; i < relation.arity(); ++i) {
        const auto sort = relation.domain(i);
        if (!sort.is_bv())
            throw std::runtime_error("CHC reader: non-bit-vector relation state is unsupported");
        vars.push_back(fresh(ctx, "x" + std::to_string(i), sort));
        vars_bar.push_back(fresh(ctx, "x" + std::to_string(i) + "_next", sort));
    }
    z3::expr pre = ctx.bool_val(false), trans = ctx.bool_val(false), post = ctx.bool_val(true);
    unsigned clause_number = 0;
    for (const auto& assertion : assertions) {
        ++clause_number;
        const std::string prefix = "CHC reader: clause " + std::to_string(clause_number) + ": ";
        std::vector<z3::expr> locals;
        const auto clause = open_universals(assertion, locals);
        z3::expr body = ctx.bool_val(true), head = clause;
        if (clause.is_implies()) {
            body = clause.arg(0);
            head = clause.arg(1);
        } else if (!is_relation(clause, relation)) {
            throw std::runtime_error(prefix + "expected an implication or relation fact");
        }
        std::vector<z3::expr> parts, body_relations;
        conjuncts(body, parts);
        z3::expr theory = ctx.bool_val(true);
        for (const auto& part : parts) {
            if (is_relation(part, relation)) body_relations.push_back(part);
            else if (has_relation(part, relation))
                throw std::runtime_error(prefix + "relation must be a positive body conjunct");
            else theory = theory && part;
        }
        if (body_relations.size() > 1)
            throw std::runtime_error(prefix + "nonlinear CHCs (multiple body relations) are unsupported");
        const bool relation_head = is_relation(head, relation);
        if (!relation_head && has_relation(head, relation))
            throw std::runtime_error(prefix + "unsupported relation occurrence in head");
        std::vector<std::pair<z3::expr, z3::expr>> links;
        if (relation_head && body_relations.empty()) {
            append_links(links, vars, head);
            pre = pre || project(theory, locals, links);
        } else if (relation_head) {
            append_links(links, vars, body_relations.front());
            append_links(links, vars_bar, head);
            trans = trans || project(theory, locals, links);
        } else if (body_relations.size() == 1) {
            append_links(links, vars, body_relations.front());
            post = post && !project(theory && !head, locals, links);
        } else {
            throw std::runtime_error(prefix + "theory-only assertions are unsupported");
        }
    }
    try {
        return transitionSystem(pre.simplify(), trans.simplify(), post.simplify(),
                                std::move(vars), std::move(vars_bar), "BV");
    } catch (const std::invalid_argument& error) {
        throw std::runtime_error(std::string("CHC reader: ") + error.what());
    }
}

} // namespace invfinder
