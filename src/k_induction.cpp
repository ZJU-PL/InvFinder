#include "k_induction.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <limits>
#include <stdexcept>
#include <utility>
#include <vector>

namespace invfinder {
namespace {

using Clock = std::chrono::steady_clock;

void validate_auxiliary_symbols(const z3::expr& expression,
                                const std::vector<z3::expr>& state,
                                unsigned bound_depth = 0) {
    if (expression.is_var()) {
        if (Z3_get_index_value(expression.ctx(), expression) >= bound_depth)
            throw std::invalid_argument("auxiliary invariant contains an unbound variable");
        return;
    }
    if (expression.is_quantifier()) {
        if (!expression.is_forall() && !expression.is_exists())
            throw std::invalid_argument("auxiliary invariant contains an unsupported lambda");
        validate_auxiliary_symbols(expression.body(), state, bound_depth +
            Z3_get_quantifier_num_bound(expression.ctx(), expression));
        return;
    }
    if (!expression.is_app()) return;
    if (expression.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
        const bool allowed = expression.num_args() == 0 && std::any_of(
            state.begin(), state.end(), [&](const z3::expr& variable) {
                return z3::eq(variable, expression);
            });
        if (!allowed)
            throw std::invalid_argument("auxiliary invariant contains an unexpected free symbol: " +
                                        expression.decl().name().str());
    }
    for (unsigned i = 0; i < expression.num_args(); ++i)
        validate_auxiliary_symbols(expression.arg(i), state, bound_depth);
}

z3::expr rename(const z3::expr& formula,
                const std::vector<z3::expr>& from,
                const std::vector<z3::expr>& to) {
    z3::expr_vector source(formula.ctx()), target(formula.ctx());
    for (std::size_t i = 0; i < from.size(); ++i) {
        source.push_back(from[i]);
        target.push_back(to[i]);
    }
    z3::expr copy = formula;
    return copy.substitute(source, target);
}

std::vector<z3::expr> fresh_state(const transitionSystem& ts) {
    std::vector<z3::expr> state;
    state.reserve(ts.vars.size());
    for (const auto& variable : ts.vars) {
        state.emplace_back(ts.ctx,
                           Z3_mk_fresh_const(ts.ctx, "kind", variable.get_sort()));
    }
    return state;
}

z3::expr transition_at(const transitionSystem& ts,
                       const std::vector<z3::expr>& current,
                       const std::vector<z3::expr>& next) {
    std::vector<z3::expr> source = ts.vars;
    source.insert(source.end(), ts.vars_bar.begin(), ts.vars_bar.end());
    std::vector<z3::expr> target = current;
    target.insert(target.end(), next.begin(), next.end());
    return rename(ts.trans, source, target);
}

} // namespace

const char* verification_status_name(VerificationStatus status) {
    switch (status) {
    case VerificationStatus::Safe: return "safe";
    case VerificationStatus::Unsafe: return "unsafe";
    case VerificationStatus::Unknown: return "unknown";
    }
    return "unknown";
}

KInductionResult k_induction(const transitionSystem& ts,
                            const KInductionOptions& options,
                            const z3::expr* auxiliary) {
    if (!std::isfinite(options.timeout_seconds)) {
        throw std::invalid_argument("k-induction timeout must be finite");
    }
    if (ts.vars.size() != ts.vars_bar.size()) {
        throw std::invalid_argument("transition-system state vectors differ in size");
    }
    for (std::size_t i = 0; i < ts.vars.size(); ++i) {
        if (!z3::eq(ts.vars[i].get_sort(), ts.vars_bar[i].get_sort())) {
            throw std::invalid_argument("current and next-state variable sorts differ");
        }
    }
    if (auxiliary && (&auxiliary->ctx() != &ts.ctx || !auxiliary->is_bool())) {
        throw std::invalid_argument("auxiliary invariant must be Boolean in the system context");
    }
    if (auxiliary) validate_auxiliary_symbols(*auxiliary, ts.vars);

    const auto started = Clock::now();
    KInductionResult result;
    auto elapsed = [&]() {
        return std::chrono::duration<double>(Clock::now() - started).count();
    };
    auto finish = [&](VerificationStatus status, const std::string& reason) {
        result.status = status;
        result.reason = reason;
        result.elapsed_seconds = elapsed();
        return result;
    };
    auto check = [&](z3::solver& solver, unsigned& count, const char* stage) {
        unsigned timeout_ms = 0; // Z3 uses zero for an unlimited timeout.
        if (options.timeout_seconds >= 0.0) {
            const double remaining = options.timeout_seconds - elapsed();
            if (remaining <= 0.0) {
                result.reason = std::string(stage) + ": verification timeout";
                return z3::unknown;
            }
            const double millis = std::max(1.0, std::ceil(remaining * 1000.0));
            timeout_ms = static_cast<unsigned>(std::min(
                millis, static_cast<double>(std::numeric_limits<unsigned>::max())));
        }
        z3::params parameters(ts.ctx);
        parameters.set("timeout", timeout_ms);
        solver.set(parameters);
        ++count;
        const auto status = solver.check();
        if (status == z3::unknown) {
            result.reason = std::string(stage) + ": " + solver.reason_unknown();
        }
        return status;
    };

    const z3::expr invariant = auxiliary ? *auxiliary : ts.ctx.bool_val(true);
    if (auxiliary) {
        z3::solver validation(ts.ctx);
        validation.add(ts.pre && !invariant);
        auto status = check(validation, result.auxiliary_checks, "auxiliary initiation");
        if (status == z3::unknown) {
            return finish(VerificationStatus::Unknown, result.reason);
        }
        if (status == z3::sat) {
            return finish(VerificationStatus::Unknown, "auxiliary invariant fails initiation");
        }
        validation.reset();
        validation.add(invariant && ts.trans && !rename(invariant, ts.vars, ts.vars_bar));
        status = check(validation, result.auxiliary_checks, "auxiliary consecution");
        if (status == z3::unknown) {
            return finish(VerificationStatus::Unknown, result.reason);
        }
        if (status == z3::sat) {
            return finish(VerificationStatus::Unknown, "auxiliary invariant fails consecution");
        }
    }

    z3::solver base(ts.ctx), step(ts.ctx);
    std::vector<z3::expr> current = fresh_state(ts);
    base.add(rename(ts.pre, ts.vars, current));
    step.add(rename(invariant, ts.vars, current));

    for (unsigned k = 0;; ++k) {
        result.k = k;
        const z3::expr property = rename(ts.post, ts.vars, current);

        // The base query contains only Init and the unrolled transition
        // relation, so a SAT result is a reachable violation of the property.
        base.push();
        base.add(!property);
        auto status = check(base, result.base_checks, "base check");
        base.pop();
        if (status == z3::sat) {
            return finish(VerificationStatus::Unsafe, "reachable counterexample");
        }
        if (status == z3::unknown) {
            return finish(VerificationStatus::Unknown, result.reason);
        }

        // At depth k, step has T(s_0,s_1),...,T(s_{k-1},s_k), the
        // property at depths 0,...,k-1, and the validated auxiliary at all
        // depths. UNSAT proves the induction step after the base cases above.
        step.push();
        step.add(!property);
        status = check(step, result.induction_checks, "induction check");
        step.pop();
        if (status == z3::unsat) {
            return finish(VerificationStatus::Safe, "induction proof");
        }
        if (status == z3::unknown) {
            return finish(VerificationStatus::Unknown, result.reason);
        }
        if (k == options.max_k) {
            return finish(VerificationStatus::Unknown, "maximum induction depth reached");
        }

        auto next = fresh_state(ts);
        const z3::expr transition = transition_at(ts, current, next);
        base.add(transition);
        step.add(property);
        step.add(transition);
        step.add(rename(invariant, ts.vars, next));
        current = std::move(next);
    }
}

} // namespace invfinder
