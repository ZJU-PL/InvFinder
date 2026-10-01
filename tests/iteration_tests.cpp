#include "invariant.h"

#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using namespace invfinder;

namespace {

const std::vector<std::string> tactics = {
    "efsolve", "bitwise", "bounded", "optimal", "bitbase", "bsearch", "bilater", "fixbsrh"};

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}

bool is_baseline(const std::string& tactic) {
    return tactic == "bilater" || tactic == "fixbsrh";
}

void require_inductive(const transitionSystem& ts, const UBVInvariant& invariant,
                       const std::string& label) {
    z3::solver checker(ts.ctx);
    checker.add(ts.pre && !invariant.get_inv_with_var(ts.vars));
    require(checker.check() == z3::unsat, label + ": initiation failed");
    checker.reset();
    checker.add(invariant.get_inv_with_var(ts.vars) && ts.trans &&
                !invariant.get_inv_with_var(ts.vars_bar));
    require(checker.check() == z3::unsat, label + ": consecution failed");
}

void require_optimal_counter(const UBVInvariant& invariant, const std::string& label) {
    require(invariant.complete && !invariant.bad_solve && !invariant.iteration_limit_reached,
            label + ": unlimited synthesis did not complete");
    require(invariant.l_val[0].get_numeral_uint() == 0 &&
                invariant.u_val[0].get_numeral_uint() == 3,
            label + ": expected the interval [0,3]");
}

void check_budgets(const transitionSystem& ts, const std::string& tactic) {
    UBVInvariant zero(ts, "interval");
    zero.set_timer(0);
    zero.runTactic(tactic, 0);
    require(zero.iterations == 0 && zero.smt_count == 0,
            tactic + ": zero budget performed work");
    require(zero.iteration_limit_reached && !zero.complete && !zero.bad_solve &&
                zero.unknown_reason.empty(),
            tactic + ": zero budget confused a budget stop with a solver failure");
    require(zero.get_inv_with_var(ts.vars).is_true(), tactic + ": zero budget did not return top");

    UBVInvariant partial(ts, "interval");
    partial.set_timer(10);
    partial.runTactic(tactic, 1);
    require(partial.iterations == 1, tactic + ": one-iteration budget counted incorrectly");
    require(partial.iteration_limit_reached && !partial.complete && !partial.bad_solve &&
                partial.unknown_reason.empty(),
            tactic + ": one iteration incorrectly claimed completion or solver failure");
    require_inductive(ts, partial, tactic + "/partial");
    if (is_baseline(tactic)) {
        // The initial abstraction is an under-approximation of the eventual
        // fixed point, so it must not escape as an inductive auxiliary fact.
        require(partial.get_inv_with_var(ts.vars).is_true(),
                tactic + ": incomplete fixedpoint baseline exposed an unsafe intermediate");
        require(partial.smt_count > 2, tactic + ": abstraction round was counted as one SMT check");
    } else {
        require(partial.smt_count == 2, tactic + ": initial check/refinement accounting differs");
        if (tactic != "bitbase") {
            // Init fixes the lower endpoint at zero. The first successful
            // joint query must tighten the upper endpoint for this program.
            require(!partial.get_inv_with_var(ts.vars).is_true(),
                    tactic + ": a successful first refinement failed to improve top");
        }
    }

    UBVInvariant unlimited(ts, "interval");
    unlimited.set_timer(10);
    unlimited.runTactic(tactic, -1);
    require_optimal_counter(unlimited, tactic + "/unlimited");
    require(unlimited.iterations > 1, tactic + ": nontrivial computation counted too few iterations");
    require_inductive(ts, unlimited, tactic + "/unlimited");
    if (is_baseline(tactic)) {
        // Init={0}, then the three successive abstract images reach [0,3],
        // followed by a final round that establishes stability.
        require(unlimited.iterations == 5, tactic + ": abstract fixedpoint rounds counted incorrectly");
        UBVInvariant midway(ts, "interval");
        midway.set_timer(10);
        midway.runTactic(tactic, 3);
        require(midway.iterations == 3 && midway.iteration_limit_reached &&
                    !midway.complete && !midway.bad_solve &&
                    midway.get_inv_with_var(ts.vars).is_true(),
                tactic + ": interrupted fixedpoint iteration exposed a non-inductive approximation");
    } else if (tactic == "optimal") {
        require(unlimited.smt_count >= unlimited.iterations + 1 &&
                    unlimited.smt_count <= 2 * unlimited.iterations + 1,
                tactic + ": a refinement must contain one standard query and at most one leap");
    } else {
        require(unlimited.smt_count == unlimited.iterations + 1,
                tactic + ": candidate-query iteration count differs from SMT checks");
    }

    UBVInvariant default_budget(ts, "interval");
    default_budget.set_timer(10);
    default_budget.runTactic(tactic);
    require_optimal_counter(default_budget, tactic + "/default");

    UBVInvariant sufficient(ts, "interval");
    sufficient.set_timer(10);
    sufficient.runTactic(tactic, 1000);
    require_optimal_counter(sufficient, tactic + "/finite-complete");
    require(sufficient.iterations <= 1000, tactic + ": finite budget exceeded");

    UBVInvariant timed(ts, "interval");
    timed.set_timer(0);
    timed.runTactic(tactic, 1);
    require(!timed.complete && timed.bad_solve && !timed.iteration_limit_reached &&
                !timed.unknown_reason.empty(),
            tactic + ": timeout was reported as an iteration limit");
    require(timed.iterations == 0 && timed.smt_count == 0,
            tactic + ": expired timer counted an unstarted refinement");
    require(timed.get_inv_with_var(ts.vars).is_true(), tactic + ": initial timeout lost top");

    for (const std::int64_t invalid : {std::int64_t(-2), std::numeric_limits<std::int64_t>::min()}) {
        UBVInvariant rejected(ts, "interval");
        bool threw = false;
        try { rejected.runTactic(tactic, invalid); }
        catch (const std::invalid_argument&) { threw = true; }
        require(threw, tactic + ": invalid negative iteration budget was accepted");
        require(rejected.smt_count == 0, tactic + ": invalid budget performed solver work");
    }
}

void check_empty_initial_states(const transitionSystem& ts, const std::string& tactic) {
    transitionSystem empty(ts.ctx.bool_val(false), ts.trans, ts.post, ts.vars, ts.vars_bar);
    UBVInvariant zero(empty, "interval");
    zero.runTactic(tactic, 0);
    require(zero.smt_count == 0 && zero.iterations == 0 && !zero.complete &&
                zero.iteration_limit_reached && zero.get_inv_with_var(ts.vars).is_true(),
            tactic + ": zero cap searched for an empty initial set");
    UBVInvariant bottom(empty, "interval");
    bottom.set_timer(10);
    bottom.runTactic(tactic, 1);
    require(bottom.complete && !bottom.bad_solve && !bottom.iteration_limit_reached &&
                bottom.iterations == 0 && bottom.smt_count == 1 &&
                bottom.get_inv_with_var(ts.vars).is_false(),
            tactic + ": empty-set proof consumed an algorithm iteration or reported a limit");
}

void check_exact_completion_budget(const transitionSystem& counter, const std::string& tactic) {
    // Every state is initially reachable, so the only answer is top and every
    // refinement is rejected. This avoids model-dependent successful jumps
    // when comparing the final iteration with the immediately preceding cap.
    transitionSystem full(counter.ctx.bool_val(true), counter.trans, counter.post,
                          counter.vars, counter.vars_bar);
    UBVInvariant unlimited(full, "interval");
    unlimited.set_timer(10);
    unlimited.runTactic(tactic);
    require(unlimited.complete && unlimited.iterations > 0,
            tactic + ": full-state computation did not finish");

    UBVInvariant exact(full, "interval");
    exact.set_timer(10);
    exact.runTactic(tactic, unlimited.iterations);
    require(exact.complete && !exact.iteration_limit_reached && !exact.bad_solve &&
                exact.iterations == unlimited.iterations &&
                exact.get_inv_with_var(full.vars).is_true(),
            tactic + ": completing exactly at the cap was reported as incomplete");

    UBVInvariant before(full, "interval");
    before.set_timer(10);
    before.runTactic(tactic, unlimited.iterations - 1);
    require(!before.complete && before.iteration_limit_reached && !before.bad_solve &&
                before.iterations == unlimited.iterations - 1,
            tactic + ": completion was claimed before the final required iteration");
    require_inductive(full, before, tactic + "/before-completion");
}

void check_grouped_bounded_leap() {
    z3::context ctx;
    auto x = ctx.bv_const("x", 8), next = ctx.bv_const("next", 8);
    transitionSystem ts(z3::ule(x, ctx.bv_val(128, 8)), next == x,
                        z3::ule(x, ctx.bv_val(128, 8)), {x}, {next});
    UBVInvariant partial(ts, "interval");
    partial.set_timer(10);
    partial.runTactic("optimal", 1);
    require(partial.iterations == 1 && partial.smt_count == 3,
            "optimal: one refinement did not include both standard and bounded-leap queries");
    require(!partial.complete && partial.iteration_limit_reached && !partial.bad_solve,
            "optimal: successful bounded leap incorrectly established completion");
    require(partial.l_val[0].get_numeral_uint() == 0 &&
                partial.u_val[0].get_numeral_uint() >= 128 &&
                partial.u_val[0].get_numeral_uint() < 255,
            "optimal: capped refinement omitted the successful bounded-leap improvement");
    require_inductive(ts, partial, "optimal/grouped-leap-partial");

    UBVInvariant complete(ts, "interval");
    complete.set_timer(10);
    complete.runTactic("optimal");
    require(complete.complete && !complete.bad_solve &&
                complete.l_val[0].get_numeral_uint() == 0 &&
                complete.u_val[0].get_numeral_uint() == 128,
            "optimal: bounded-leap regression did not compute [0,128]");
    require(complete.smt_count - 1 <= 4 * 8,
            "optimal: bounded-leap regression exceeded the 4W query bound");
}

} // namespace

int main() {
    try {
        z3::context ctx;
        auto x = ctx.bv_const("x", 4), next = ctx.bv_const("next", 4);
        transitionSystem counter(x == 0,
            z3::ult(x, ctx.bv_val(3, 4)) && next == x + 1,
            z3::ule(x, ctx.bv_val(3, 4)), {x}, {next});
        for (const auto& tactic : tactics) {
            check_budgets(counter, tactic);
            check_empty_initial_states(counter, tactic);
            check_exact_completion_budget(counter, tactic);
        }
        check_grouped_bounded_leap();
        std::cout << "Passed iteration budgets, partial soundness, counting, and timeout checks\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "FAILED: " << error.what() << '\n';
        return 1;
    }
}
