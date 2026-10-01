#include "invariant.h"
#include "k_induction.h"
#include <algorithm>
#include <functional>
#include <iostream>
#include <stdexcept>
#include <vector>

using namespace invfinder;
using State = std::vector<unsigned>;
void require(bool value, const std::string& what) {
    if (!value) throw std::runtime_error(what);
}
const std::vector<std::string> tactics = {
    "efsolve", "bitwise", "bounded", "optimal", "bitbase", "bsearch", "bilater", "fixbsrh"};

// Independent finite-state oracle: repeatedly abstract Init union Post(gamma(A)).
// This enumerates concrete states and transitions; it does not call a synthesis
// procedure or solve for template bounds.
void check_against_finite_oracle(const std::string& domain, const std::string& tactic, unsigned n) {
    z3::context ctx;
    std::vector<z3::expr> vars, next;
    z3::expr init = ctx.bool_val(true), transition = ctx.bool_val(true);
    for (unsigned i = 0; i < n; ++i) {
        vars.push_back(ctx.bv_const(("v" + std::to_string(i)).c_str(), 2));
        next.push_back(ctx.bv_const(("n" + std::to_string(i)).c_str(), 2));
        init = init && vars.back() == 0;
        transition = transition && next.back() == vars.back() + ctx.bv_val(i + 1, 2);
    }
    transition = transition && z3::ult(vars[0], ctx.bv_val(2, 2));
    transitionSystem ts(init, transition, ctx.bool_val(true), vars, next);
    UBVInvariant result(ts, domain);
    const unsigned count = 1u << (2 * n);
    std::vector<State> states;
    std::vector<std::vector<unsigned>> rows;
    for (unsigned mask = 0; mask < count; ++mask) {
        State state(n);
        z3::expr_vector from(ctx), to(ctx);
        for (unsigned i = 0; i < n; ++i) {
            state[i] = (mask >> (2 * i)) & 3;
            from.push_back(vars[i]); to.push_back(ctx.bv_val(state[i], 2));
        }
        states.push_back(state);
        std::vector<unsigned> values;
        for (auto row : result.var) values.push_back(row.substitute(from, to).simplify().get_numeral_uint());
        rows.push_back(values);
    }
    auto lower = rows[0], upper = rows[0];
    bool changed;
    do {
        changed = false;
        auto new_lower = lower, new_upper = upper;
        for (unsigned s = 0; s < count; ++s) {
            bool inside = true;
            for (std::size_t r = 0; r < lower.size(); ++r)
                inside = inside && lower[r] <= rows[s][r] && rows[s][r] <= upper[r];
            if (!inside || states[s][0] >= 2) continue;
            unsigned successor = 0;
            for (unsigned i = 0; i < n; ++i)
                successor |= ((states[s][i] + i + 1) & 3) << (2 * i);
            for (std::size_t r = 0; r < lower.size(); ++r) {
                new_lower[r] = std::min(new_lower[r], rows[successor][r]);
                new_upper[r] = std::max(new_upper[r], rows[successor][r]);
            }
        }
        changed = new_lower != lower || new_upper != upper;
        lower = new_lower; upper = new_upper;
    } while (changed);
    result.set_timer(10); result.runTactic(tactic);
    const auto name = domain + "/" + tactic;
    require(result.complete && !result.bad_solve, name + " did not complete: " + result.unknown_reason);
    unsigned total_width = 0;
    for (const auto& row : result.var) total_width += row.get_sort().bv_size();
    // The preliminary Init-emptiness check is outside the synthesis algorithms.
    if (tactic == "bitwise")
        require(result.smt_count - 1 <= static_cast<int>(2 * total_width),
                name + " exceeded the 2W query bound");
    if (tactic == "optimal") {
        require(result.smt_count - 1 <= static_cast<int>(4 * total_width),
                name + " exceeded the 4W query bound");
        require(result.iterations <= 2 * total_width &&
                    result.smt_count - 1 >= result.iterations &&
                    result.smt_count - 1 <= 2 * result.iterations,
                name + " did not group each standard query with at most one bounded leap");
    }
    for (std::size_t r = 0; r < lower.size(); ++r) {
        require(result.l_val[r].get_numeral_uint() == lower[r], name + " wrong lower bound at row " + std::to_string(r));
        require(result.u_val[r].get_numeral_uint() == upper[r], name + " wrong upper bound at row " + std::to_string(r));
    }
    z3::solver validator(ctx);
    validator.add(ts.pre && !result.get_inv_with_var(vars));
    require(validator.check() == z3::unsat, name + " invalid initiation");
    validator.reset();
    validator.add(result.get_inv_with_var(vars) && ts.trans && !result.get_inv_with_var(next));
    require(validator.check() == z3::unsat, name + " invalid consecution");
}

void edge_cases() {
    for (const auto& tactic : tactics) {
        z3::context ctx;
        auto x = ctx.bv_const("x", 128), next = ctx.bv_const("next", 128);
        auto value = ctx.bv_val("170141183460469231731687303715884105731", 128);
        transitionSystem ts(x == value, next == x, ctx.bool_val(true), {x}, {next});
        UBVInvariant inv(ts, "interval"); inv.set_timer(10); inv.runTactic(tactic);
        require(inv.complete && !inv.bad_solve, "128-bit " + tactic + " incomplete");
        require((inv.l_val[0] == value).simplify().is_true() &&
                (inv.u_val[0] == value).simplify().is_true(), "128-bit numeral truncated: " + tactic);
        UBVInvariant timed(ts, "interval"); timed.set_timer(0); timed.runTactic(tactic);
        require(!timed.complete && timed.bad_solve, "zero timeout claimed completion: " + tactic);
        require(timed.get_inv_with_var({x}).simplify().is_true(), "timeout lost safe top: " + tactic);
        transitionSystem empty(ctx.bool_val(false), next == x, ctx.bool_val(true), {x}, {next});
        UBVInvariant bottom(empty, "interval"); bottom.set_timer(10); bottom.runTactic(tactic);
        require(bottom.complete && bottom.get_inv_with_var({x}).simplify().is_false(), "empty init mishandled: " + tactic);
    }
}

void verification() {
    z3::context ctx;
    auto x = ctx.bv_const("x", 3), next = ctx.bv_const("next", 3);
    transitionSystem safe(x == 0, z3::ult(x, ctx.bv_val(3, 3)) && next == x + 1,
                          z3::ule(x, ctx.bv_val(3, 3)), {x}, {next});
    KInductionOptions o; o.max_k = 8; o.timeout_seconds = 5;
    require(k_induction(safe, o).status == VerificationStatus::Safe, "safe loop unproved");
    transitionSystem unsafe(x == 0, next == x + 1, z3::ule(x, ctx.bv_val(3, 3)), {x}, {next});
    require(k_induction(unsafe, o).status == VerificationStatus::Unsafe, "reachable violation missed");
    o.max_k = 1;
    require(k_induction(unsafe, o).status == VerificationStatus::Unknown, "depth limit called unsafe");
    o.timeout_seconds = 0;
    require(k_induction(safe, o).status == VerificationStatus::Unknown, "timeout called safe/unsafe");
    o.timeout_seconds = 5;
    z3::expr invalid = ctx.bool_val(false);
    require(k_induction(unsafe, o, &invalid).status == VerificationStatus::Unknown, "invalid auxiliary accepted");
    UBVInvariant inv(safe, "interval"); inv.set_timer(5); inv.runTactic("optimal");
    auto auxiliary = inv.get_inv_with_var({x});
    require(k_induction(safe, o, &auxiliary).status == VerificationStatus::Safe, "valid auxiliary rejected");

    auto reject_auxiliary = [&](const transitionSystem& ts, const z3::expr& candidate) {
        try {
            k_induction(ts, o, &candidate);
        } catch (const std::invalid_argument&) {
            return;
        }
        throw std::runtime_error("auxiliary with an unexpected free symbol was accepted");
    };
    // A next-state symbol must not double as a fixed auxiliary parameter:
    // I(x,next) = x<2 || next=x would make I(next,next) tautological and could
    // otherwise turn this reachable depth-three violation into a false proof.
    auto a = ctx.bv_const("a", 2), an = ctx.bv_const("an", 2);
    transitionSystem alias(a == 0, an == a + 1, z3::ult(a, ctx.bv_val(3, 2)), {a}, {an});
    auto malicious = z3::ult(a, ctx.bv_val(2, 2)) || an == a;
    reject_auxiliary(alias, malicious);
    auto ghost = ctx.bool_const("ghost");
    reject_auxiliary(safe, auxiliary && ghost);
    auto predicate = ctx.function("unbound_predicate", x.get_sort(), ctx.bool_sort());
    reject_auxiliary(safe, auxiliary && predicate(x));
    auto quantified = z3::forall(x, x == x) && auxiliary;
    require(k_induction(safe, o, &quantified).status == VerificationStatus::Safe,
            "quantifier-bound auxiliary variables were rejected");
}

void octagon_orientation() {
    z3::context ctx;
    auto x = ctx.bv_const("x", 8), y = ctx.bv_const("y", 8);
    auto xn = ctx.bv_const("xn", 8), yn = ctx.bv_const("yn", 8);
    transitionSystem ts(ctx.bool_val(true), xn == x && yn == y, ctx.bool_val(true),
                        {x, y}, {xn, yn});
    const std::vector<z3::expr> expected = {x, y, x + y, x - y};
    for (const auto& domain : {"octagon", "octagon-forward"}) {
        UBVInvariant invariant(ts, domain);
        require(invariant.var.size() == expected.size(),
                std::string(domain) + " contains an unexpected set of template rows");
        for (std::size_t i = 0; i < expected.size(); ++i) {
            z3::solver checker(ctx);
            checker.add(invariant.var[i] != expected[i]);
            require(checker.check() == z3::unsat,
                    std::string(domain) + " must use x_i-x_j with i<j");
        }
    }
}

int main() {
    try {
        for (const auto& domain : {"interval", "zones", "octagon", "octagon-forward", "knownbits"})
            for (const auto& tactic : tactics) check_against_finite_oracle(domain, tactic, 2);
        for (const auto& tactic : tactics) check_against_finite_oracle("polyhedra", tactic, 3);
        edge_cases(); verification(); octagon_orientation();
        std::cout << "Passed finite-state oracle, 128-bit, timeout, bottom, and verification checks\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "FAILED: " << e.what() << '\n'; return 1;
    }
}
