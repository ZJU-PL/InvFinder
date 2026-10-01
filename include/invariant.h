#pragma once

#include "transition_system.h"
#include <chrono>
#include <cstdint>
#include <string>
#include <vector>

namespace invfinder {

// Fixed-width template invariants. All row arithmetic and comparisons use
// unsigned bit-vector semantics; no arithmetic expression is widened silently.
class UBVInvariant {
  public:
    transitionSystem trans;
    std::string inv_type;
    std::vector<z3::expr> var, var_bar, l_val, u_val;
    int size = 0;
    int smt_count = 0;
    bool bad_solve = false;
    bool complete = false;
    bool is_bottom = false;
    std::int64_t iterations = 0;
    bool iteration_limit_reached = false;
    std::string unknown_reason;

    UBVInvariant(transitionSystem transition, std::string domain);
    void set_timer(double seconds);
    double get_timeout() const;
    // An optimal iteration is one standard query and at most one following
    // bounded leap after UNSAT. Other top-down tactics count refinement queries.
    // Fixed-point tactics count completed abstraction rounds instead of their
    // individual solver queries. The initial emptiness check is excluded.
    // Zero returns top immediately; -1 runs without an iteration limit.
    void runTactic(const std::string &tactic, std::int64_t max_iterations = -1);
    z3::expr get_inv_with_var(const std::vector<z3::expr> &variables) const;
    std::string l_val_string() const;
    std::string u_val_string() const;

  private:
    z3::context &ctx;
    z3::expr inv_cons, inv_bar_cons, pre_cons, trans_cons;
    std::vector<int> size_var;
    std::vector<z3::expr> l_var, u_var;
    struct SearchState {
        z3::solver solver;
        std::vector<int> cur_bit_l, cur_bit_u;
        std::vector<z3::expr> bound_l, bound_u;
        explicit SearchState(z3::context &context) : solver(context) {
            solver.set("mbqi", true);
            unsigned major, minor, patch, revision;
            Z3_get_version(&major, &minor, &patch, &revision);
            // Z3 4.12.2 can return incomplete-quantifier results for incremental
            // BV queries with E-matching; MBQI alone handles these queries.
            if (major == 4 && minor == 12 && patch == 2)
                solver.set("ematching", false);
        }
    } data;
    std::chrono::steady_clock::time_point time_start;
    double time_out = -1;
    bool has_run = false;
    std::int64_t iteration_limit = -1;

    void add_row(const z3::expr &row, const z3::expr &row_bar);
    void require_iteration();
    // Applies the remaining total deadline to a native Z3 solver. UNKNOWN is
    // always recorded and never treated as UNSAT or as proof of optimality.
    z3::check_result solver_check(z3::solver &solver);
    z3::expr get_current_upper_consts();
    z3::expr get_current_lower_consts();
    void tactic_efsolve();
    void tactic_bitwise();
    void tactic_bounded_bitwise();
    void tactic_bounded_bitwise_partial_efsolve();
    void tactic_unmerged_bitwise();
    void tactic_binary_search();
    void tactic_fix_binary_search();
    void tactic_fix_bilateral();
};

} // namespace invfinder
