#include "invariant.h"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <utility>

namespace invfinder {
using namespace std;
using z3::lshr;
using z3::shl;
using z3::uge;
using z3::ugt;
using z3::ule;
using z3::ult;

namespace {
struct IterationLimitReached {};

z3::expr bv_all_ones(z3::context &ctx, unsigned width) { return (~ctx.bv_val(0, width)).simplify(); }
z3::expr bv_umax_const(const z3::expr &a, const z3::expr &b) {
    return ule(a, b).simplify().is_true() ? b : a;
}
z3::expr bv_umin_const(const z3::expr &a, const z3::expr &b) {
    return ule(a, b).simplify().is_true() ? a : b;
}
void tighten_with_model_bound(z3::expr &l, z3::expr &u, const z3::expr &ml, const z3::expr &mu) {
    l = bv_umax_const(l, ml);
    u = bv_umin_const(u, mu);
}
z3::expr bv_raise_to_bit(const z3::expr &v, int bit) {
    if (bit < 0)
        return v;
    const auto one = v.ctx().bv_val(1, v.get_sort().bv_size());
    return (shl(lshr(v, bit + 1), bit + 1) | shl(one, bit)).simplify();
}
z3::expr bv_lower_cover_bound(const z3::expr &v, int bit) {
    if (bit < 0)
        return v;
    const auto one = v.ctx().bv_val(1, v.get_sort().bv_size());
    return (v | (shl(one, bit + 1) - 1)).simplify();
}
z3::expr bv_upper_cover_bound(const z3::expr &v, int bit) {
    if (bit < 0)
        return v;
    const auto one = v.ctx().bv_val(1, v.get_sort().bv_size());
    return (v & ~(shl(one, bit + 1) - 1)).simplify();
}
z3::expr bv_decrement(const z3::expr &v) { return (v - 1).simplify(); }
int get_next_0_bit(const z3::expr &v, int bit) {
    for (int i = bit; i >= 0; --i)
        if (((lshr(v, i) & 1) == 0).simplify().is_true())
            return i;
    return -1;
}
int get_next_1_bit(const z3::expr &v, int bit) {
    for (int i = bit; i >= 0; --i)
        if (((lshr(v, i) & 1) == 1).simplify().is_true())
            return i;
    return -1;
}
int get_next_liftable_bit(const z3::expr &v, const z3::expr &limit, int bit) {
    for (int i = bit; i >= 0; --i)
        if (((lshr(v, i) & 1) == 0).simplify().is_true() &&
            ule(bv_raise_to_bit(v, i), limit).simplify().is_true())
            return i;
    return -1;
}
int get_next_dropable_bit(const z3::expr &v, const z3::expr &limit, int bit) {
    for (int i = bit; i >= 0; --i)
        if (((lshr(v, i) & 1) == 1).simplify().is_true() &&
            uge((bv_raise_to_bit(v, i) - 1).simplify(), limit).simplify().is_true())
            return i;
    return -1;
}
z3::expr align_unsigned(const z3::expr &v, unsigned width) {
    const unsigned current = v.get_sort().bv_size();
    return width == current ? v : z3::zext(v, width - current);
}
bool trace_enabled() { return std::getenv("BESTINV_TRACE") != nullptr; }
void trace_bounds(const char *tactic, const char *phase, int i, int bl, int bu, const z3::expr &l,
                  const z3::expr &u, const z3::expr &ll, const z3::expr &uu) {
    if (trace_enabled())
        cerr << "[InvFinder:" << tactic << "] " << phase << " dim=" << i << " bit_l=" << bl << " bit_u=" << bu
             << " l=" << l << " u=" << u << " bound_l=" << ll << " bound_u=" << uu << '\n';
}
void trace_check(const char *tactic, const char *phase, z3::check_result result, int count) {
    if (trace_enabled())
        cerr << "[InvFinder:" << tactic << "] " << phase << " check=" << result << " smt_count=" << count
             << '\n';
}
void trace_model_bound(const char *tactic, int i, const z3::expr &l, const z3::expr &u) {
    if (trace_enabled())
        cerr << "[InvFinder:" << tactic << "] model dim=" << i << " l=" << l << " u=" << u << '\n';
}
} // namespace

UBVInvariant::UBVInvariant(transitionSystem transition, string domain)
    : trans(std::move(transition)), inv_type(std::move(domain)), ctx(trans.ctx), inv_cons(ctx.bool_val(true)),
      inv_bar_cons(ctx.bool_val(true)), pre_cons(ctx.bool_val(true)), trans_cons(ctx.bool_val(true)),
      data(ctx), time_start(std::chrono::steady_clock::now()) {
    if (trans.vars.size() != trans.vars_bar.size())
        throw invalid_argument("Mismatched state-variable vectors");
    for (size_t i = 0; i < trans.vars.size(); ++i) {
        if (!trans.vars[i].is_bv() || !trans.vars_bar[i].is_bv() ||
            trans.vars[i].get_sort().bv_size() != trans.vars_bar[i].get_sort().bv_size())
            throw invalid_argument("Invariant synthesis requires matching bit-vector state variables");
    }
    const bool polyhedra = inv_type == "polyhedra" || inv_type == "template-polyhedra";
    if (inv_type == "knownbits") {
        for (size_t i = 0; i < trans.vars.size(); ++i)
            for (unsigned bit = 0; bit < trans.vars[i].get_sort().bv_size(); ++bit)
                add_row(trans.vars[i].extract(bit, bit), trans.vars_bar[i].extract(bit, bit));
    } else if (inv_type == "interval" || inv_type == "zones" || inv_type == "octagon" ||
               inv_type == "octagon-forward" || polyhedra) {
        for (size_t i = 0; i < trans.vars.size(); ++i)
            add_row(trans.vars[i], trans.vars_bar[i]);
        if (inv_type != "interval") {
            // Canonical pair rows use i<j for both sums and differences.
            for (size_t i = 0; i < trans.vars.size(); ++i)
                for (size_t j = i + 1; j < trans.vars.size(); ++j) {
                    const unsigned width =
                        max(trans.vars[i].get_sort().bv_size(), trans.vars[j].get_sort().bv_size());
                    const auto x = align_unsigned(trans.vars[i], width),
                               y = align_unsigned(trans.vars[j], width);
                    const auto xp = align_unsigned(trans.vars_bar[i], width),
                               yp = align_unsigned(trans.vars_bar[j], width);
                    if (inv_type != "zones")
                        add_row(x + y, xp + yp);
                    add_row(x - y, xp - yp);
                }
        }
        if (polyhedra) {
            for (size_t i = 0; i < trans.vars.size(); ++i)
                for (size_t j = i + 1; j < trans.vars.size(); ++j)
                    for (size_t k = j + 1; k < trans.vars.size(); ++k) {
                        const unsigned width =
                            max({trans.vars[i].get_sort().bv_size(), trans.vars[j].get_sort().bv_size(),
                                 trans.vars[k].get_sort().bv_size()});
                        const auto x = align_unsigned(trans.vars[i], width),
                                   y = align_unsigned(trans.vars[j], width),
                                   z = align_unsigned(trans.vars[k], width);
                        const auto xp = align_unsigned(trans.vars_bar[i], width),
                                   yp = align_unsigned(trans.vars_bar[j], width),
                                   zp = align_unsigned(trans.vars_bar[k], width);
                        for (int sy : {-1, 1})
                            for (int sz : {-1, 1})
                                add_row(x + (sy == 1 ? y : -y) + (sz == 1 ? z : -z),
                                        xp + (sy == 1 ? yp : -yp) + (sz == 1 ? zp : -zp));
                    }
        }
    } else
        throw invalid_argument("Unknown invariant domain: " + inv_type);
    size = static_cast<int>(var.size());
    const auto ori = trans.get_ori_consts();
    const auto all = trans.get_all_consts();
    pre_cons = z3::implies(trans.pre, inv_cons);
    trans_cons = z3::implies(inv_cons && trans.trans, inv_bar_cons);
    if (!ori.empty())
        pre_cons = z3::forall(ori, pre_cons);
    if (!all.empty())
        trans_cons = z3::forall(all, trans_cons);
    data.solver.add((pre_cons && trans_cons).simplify());
    data.cur_bit_u = data.cur_bit_l;
    data.bound_l = u_val;
    data.bound_u = l_val;
}

void UBVInvariant::add_row(const z3::expr &row, const z3::expr &row_bar) {
    var.push_back(row.simplify());
    var_bar.push_back(row_bar.simplify());
    const unsigned width = row.get_sort().bv_size();
    size_var.push_back(static_cast<int>(width));
    const auto sort = ctx.bv_sort(width);
    l_var.emplace_back(ctx, Z3_mk_fresh_const(ctx, "lower", sort));
    u_var.emplace_back(ctx, Z3_mk_fresh_const(ctx, "upper", sort));
    inv_cons = inv_cons && ule(l_var.back(), var.back()) && ule(var.back(), u_var.back());
    inv_bar_cons = inv_bar_cons && ule(l_var.back(), var_bar.back()) && ule(var_bar.back(), u_var.back());
    data.cur_bit_l.push_back(static_cast<int>(width) - 1);
    l_val.push_back(ctx.bv_val(0, width));
    u_val.push_back(bv_all_ones(ctx, width));
}

void UBVInvariant::set_timer(double seconds) {
    if (!std::isfinite(seconds))
        throw invalid_argument("Timeout must be finite");
    time_start = std::chrono::steady_clock::now();
    time_out = seconds;
}
double UBVInvariant::get_timeout() const {
    if (time_out < 0)
        return -1;
    return max(0.0, time_out -
                        std::chrono::duration<double>(std::chrono::steady_clock::now() - time_start).count());
}
z3::check_result UBVInvariant::solver_check(z3::solver &solver) {
    const double remaining = get_timeout();
    if (remaining == 0) {
        bad_solve = true;
        unknown_reason = "total synthesis timeout";
        return z3::unknown;
    }
    z3::params params(ctx);
    const double milliseconds = remaining < 0 ? 0 : std::ceil(remaining * 1000);
    params.set("timeout", static_cast<unsigned>(std::min(
                              milliseconds, static_cast<double>(std::numeric_limits<unsigned>::max()))));
    solver.set(params);
    ++smt_count;
    const auto result = solver.check();
    if (result == z3::unknown) {
        bad_solve = true;
        unknown_reason = solver.reason_unknown();
    }
    return result;
}

z3::expr UBVInvariant::get_inv_with_var(const vector<z3::expr> &variables) const {
    if (variables.size() != trans.vars.size())
        throw invalid_argument("Invariant variable arity mismatch");
    if (is_bottom)
        return ctx.bool_val(false);
    z3::expr_vector from(ctx), to(ctx);
    for (size_t i = 0; i < variables.size(); ++i) {
        from.push_back(trans.vars[i]);
        to.push_back(variables[i]);
    }
    z3::expr result = ctx.bool_val(true);
    for (int i = 0; i < size; ++i) {
        z3::expr row = var[i];
        row = row.substitute(from, to);
        result = result && ule(l_val[i], row) && ule(row, u_val[i]);
    }
    return result.simplify();
}
string UBVInvariant::l_val_string() const {
    if (is_bottom)
        return "[bottom]";
    string result;
    for (const auto &val : l_val) {
        if (!result.empty())
            result += ' ';
        result += val.to_string();
    }
    return '[' + result + ']';
}
string UBVInvariant::u_val_string() const {
    if (is_bottom)
        return "[bottom]";
    string result;
    for (const auto &val : u_val) {
        if (!result.empty())
            result += ' ';
        result += val.to_string();
    }
    return '[' + result + ']';
}

void UBVInvariant::require_iteration() {
    if (iteration_limit >= 0 && iterations >= iteration_limit) {
        iteration_limit_reached = true;
        throw IterationLimitReached{};
    }
}

void UBVInvariant::runTactic(const string &tactic, std::int64_t max_iterations) {
    if (has_run)
        throw logic_error("Create a new invariant engine for each synthesis run");
    if (tactic != "efsolve" && tactic != "bitwise" && tactic != "bounded" && tactic != "optimal" &&
        tactic != "bitbase" && tactic != "bsearch" && tactic != "bilater" && tactic != "fixbsrh")
        throw invalid_argument("Unknown tactic: " + tactic);
    if (max_iterations < -1)
        throw invalid_argument("Iteration limit must be nonnegative or -1 (unlimited)");
    has_run = true;
    iteration_limit = max_iterations;
    if (iteration_limit == 0) {
        iteration_limit_reached = true;
        return;
    }
    // Empty initial states have the canonical false invariant. Checking once
    // also handles the empty-set case in the symbolic-abstraction baselines.
    z3::solver initiation(ctx);
    initiation.add(trans.pre);
    const auto initial = solver_check(initiation);
    if (initial == z3::unknown)
        return;
    if (initial == z3::unsat) {
        is_bottom = true;
        complete = true;
        return;
    }
    try {
        if (tactic == "efsolve")
            tactic_efsolve();
        else if (tactic == "bitwise")
            tactic_bitwise();
        else if (tactic == "bounded")
            tactic_bounded_bitwise();
        else if (tactic == "optimal")
            tactic_bounded_bitwise_partial_efsolve();
        else if (tactic == "bitbase")
            tactic_unmerged_bitwise();
        else if (tactic == "bsearch")
            tactic_binary_search();
        else if (tactic == "bilater")
            tactic_fix_bilateral();
        else if (tactic == "fixbsrh")
            tactic_fix_binary_search();
    } catch (const IterationLimitReached &) {
        // The engine is single-use. Private solver scopes may be discarded;
        // published top-down bounds remain inductive, and unfinished fixed-point
        // rounds have never replaced the public top bounds.
        return;
    }
    complete = !bad_solve;
}

z3::expr UBVInvariant::get_current_upper_consts() {
    z3::expr ret = ctx.bool_val(true);
    for (int i = 0; i < size; ++i) {
        ret = ret && ule(l_val[i], l_var[i]) && ule(u_var[i], u_val[i]);
    }
    return ret.simplify();
}

z3::expr UBVInvariant::get_current_lower_consts() {
    z3::expr ret = ctx.bool_val(true);
    for (int i = 0; i < size; ++i) {
        ret = ret && ule(l_var[i], data.bound_l[i]) && ule(data.bound_u[i], u_var[i]);
    }
    return ret.simplify();
}

// Direct refinement by an arbitrary strictly tighter inductive witness.
void UBVInvariant::tactic_efsolve() {
    while (!bad_solve) {
        data.solver.push();
        z3::expr guess = ctx.bool_val(false);
        for (int i = 0; i < size; ++i) {
            guess = guess || ult(l_val[i], l_var[i]) || ult(u_var[i], u_val[i]);
        }
        data.solver.add((guess && get_current_upper_consts() && get_current_lower_consts()).simplify());
        require_iteration();
        ++iterations;
        z3::check_result res = solver_check(data.solver);

        if (res == z3::sat) {
            z3::model model = data.solver.get_model();
            for (int i = 0; i < size; ++i) {
                z3::expr model_lower = model.eval(l_var[i], true);
                z3::expr model_upper = model.eval(u_var[i], true);
                tighten_with_model_bound(l_val[i], u_val[i], model_lower, model_upper);
            }
            data.solver.pop();
            continue;
        }
        if (res == z3::unknown) {
            bad_solve = true;
        }
        data.solver.pop();
        return;
    }
}

// Merged most-significant-bit-first proposals, without boundary pruning.
void UBVInvariant::tactic_bitwise() {
    while (!bad_solve) {
        bool refine_possible = false;
        bool progressed = false;
        z3::expr guess = ctx.bool_val(false);
        for (int i = 0; i < size; ++i) {
            data.cur_bit_l[i] = get_next_0_bit(l_val[i], data.cur_bit_l[i]);
            data.cur_bit_u[i] = get_next_1_bit(u_val[i], data.cur_bit_u[i]);
            if (data.cur_bit_l[i] >= 0) {
                refine_possible = true;
                z3::expr bound = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                guess = guess || uge(l_var[i], bound);
            }
            if (data.cur_bit_u[i] >= 0) {
                refine_possible = true;
                z3::expr bound = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                guess = guess || ult(u_var[i], bound);
            }
            trace_bounds("bitwise", "candidate", i, data.cur_bit_l[i], data.cur_bit_u[i], l_val[i], u_val[i],
                         data.bound_l[i], data.bound_u[i]);
        }
        while (refine_possible) {
            data.solver.push();
            data.solver.add((guess && get_current_upper_consts() && get_current_lower_consts()).simplify());
            require_iteration();
            ++iterations;
            z3::check_result res = solver_check(data.solver);

            trace_check("bitwise", "refine", res, smt_count);
            if (res == z3::sat) {
                z3::model model = data.solver.get_model();
                bool changed = false;
                for (int i = 0; i < size; ++i) {
                    z3::expr model_l = model.eval(l_var[i], true);
                    z3::expr model_u = model.eval(u_var[i], true);
                    trace_model_bound("bitwise", i, model_l, model_u);

                    if (ult(l_val[i], model_l).simplify().is_true()) {
                        if (data.cur_bit_l[i] >= 0 &&
                            ((lshr(model_l, data.cur_bit_l[i]) & 1) == 1).simplify().is_true()) {
                            --data.cur_bit_l[i];
                        }
                        l_val[i] = model_l;
                        changed = true;
                    }

                    if (ult(model_u, u_val[i]).simplify().is_true()) {
                        if (data.cur_bit_u[i] >= 0 &&
                            ((lshr(model_u, data.cur_bit_u[i]) & 1) == 0).simplify().is_true()) {
                            --data.cur_bit_u[i];
                        }
                        u_val[i] = model_u;
                        changed = true;
                    }
                }
                if (changed) {
                    data.solver.pop();
                    progressed = true;
                    break;
                }
                trace_check("bitwise", "sat-no-progress", res, smt_count);
                bad_solve = true;
                unknown_reason = "satisfiable strict refinement made no progress";
                data.solver.pop();
                return;
            } else if (res == z3::unknown) {
                bad_solve = true;
                data.solver.pop();
                return;
            }

            refine_possible = false;
            guess = ctx.bool_val(false);
            for (int i = 0; i < size; ++i) {
                data.cur_bit_l[i] = get_next_0_bit(l_val[i], data.cur_bit_l[i] - 1);
                data.cur_bit_u[i] = get_next_1_bit(u_val[i], data.cur_bit_u[i] - 1);
                if (data.cur_bit_l[i] >= 0) {
                    refine_possible = true;
                    z3::expr bound = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                    guess = guess || uge(l_var[i], bound);
                }
                if (data.cur_bit_u[i] >= 0) {
                    refine_possible = true;
                    z3::expr bound = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                    guess = guess || ult(u_var[i], bound);
                }
                trace_bounds("bitwise", "next-candidate", i, data.cur_bit_l[i], data.cur_bit_u[i], l_val[i],
                             u_val[i], data.bound_l[i], data.bound_u[i]);
            }
            data.solver.pop();
        }
        if (progressed) {
            continue;
        }
        return;
    }
}

// Bitwise proposals with boundary limits learned from models and failures.
void UBVInvariant::tactic_bounded_bitwise() {
    while (!bad_solve) {
        bool refine_possible = false;
        bool progressed = false;
        z3::expr guess = ctx.bool_val(false);
        for (int i = 0; i < size; ++i) {
            data.bound_l[i] = bv_umin_const(data.bound_l[i], u_val[i]).simplify();
            data.bound_u[i] = bv_umax_const(data.bound_u[i], l_val[i]).simplify();
            data.cur_bit_l[i] = get_next_liftable_bit(l_val[i], data.bound_l[i], data.cur_bit_l[i]);
            data.cur_bit_u[i] = get_next_dropable_bit(u_val[i], data.bound_u[i], data.cur_bit_u[i]);
            if (data.cur_bit_l[i] >= 0) {
                data.bound_l[i] =
                    bv_umin_const(data.bound_l[i], bv_lower_cover_bound(l_val[i], data.cur_bit_l[i]))
                        .simplify();
            }
            if (data.cur_bit_u[i] >= 0) {
                data.bound_u[i] =
                    bv_umax_const(data.bound_u[i], bv_upper_cover_bound(u_val[i], data.cur_bit_u[i]))
                        .simplify();
            }
            if (data.cur_bit_l[i] >= 0) {
                refine_possible = true;
                z3::expr bound = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                guess = guess || uge(l_var[i], bound);
            }
            if (data.cur_bit_u[i] >= 0) {
                refine_possible = true;
                z3::expr bound = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                guess = guess || ult(u_var[i], bound);
            }
            trace_bounds("bounded", "candidate", i, data.cur_bit_l[i], data.cur_bit_u[i], l_val[i], u_val[i],
                         data.bound_l[i], data.bound_u[i]);
        }
        while (refine_possible) {
            data.solver.push();
            data.solver.add((guess && get_current_lower_consts() && get_current_upper_consts()).simplify());
            require_iteration();
            ++iterations;
            z3::check_result res = solver_check(data.solver);

            trace_check("bounded", "refine", res, smt_count);
            if (res == z3::sat) {
                z3::model model = data.solver.get_model();
                bool changed = false;
                for (int i = 0; i < size; ++i) {
                    z3::expr model_l = model.eval(l_var[i], true);
                    z3::expr model_u = model.eval(u_var[i], true);
                    trace_model_bound("bounded", i, model_l, model_u);

                    if (ult(l_val[i], model_l).simplify().is_true()) {
                        if (data.cur_bit_l[i] >= 0 &&
                            ((lshr(model_l, data.cur_bit_l[i]) & 1) == 1).simplify().is_true()) {
                            --data.cur_bit_l[i];
                        }
                        data.bound_u[i] = bv_umax_const(data.bound_u[i], model_l).simplify();
                        l_val[i] = model_l;
                        changed = true;
                    }

                    if (ult(model_u, u_val[i]).simplify().is_true()) {
                        if (data.cur_bit_u[i] >= 0 &&
                            ((lshr(model_u, data.cur_bit_u[i]) & 1) == 0).simplify().is_true()) {
                            --data.cur_bit_u[i];
                        }
                        data.bound_l[i] = bv_umin_const(data.bound_l[i], model_u).simplify();
                        u_val[i] = model_u;
                        changed = true;
                    }
                }
                if (changed) {
                    data.solver.pop();
                    progressed = true;
                    break;
                }
                trace_check("bounded", "sat-no-progress", res, smt_count);
                bad_solve = true;
                unknown_reason = "satisfiable strict refinement made no progress";
                data.solver.pop();
                return;
            } else if (res == z3::unknown) {
                bad_solve = true;
                data.solver.pop();
                return;
            }

            refine_possible = false;
            guess = ctx.bool_val(false);
            for (int i = 0; i < size; ++i) {
                if (data.cur_bit_l[i] >= 0) {
                    z3::expr failed_l = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                    data.bound_l[i] = bv_umin_const(data.bound_l[i], bv_decrement(failed_l)).simplify();
                }
                if (data.cur_bit_u[i] >= 0) {
                    // The tested upper candidate is threshold-1, so its
                    // failure gives the exact lower limit C.u+1=threshold.
                    z3::expr failed_u = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                    data.bound_u[i] = bv_umax_const(data.bound_u[i], failed_u).simplify();
                }
                data.cur_bit_l[i] = get_next_liftable_bit(l_val[i], data.bound_l[i], data.cur_bit_l[i] - 1);
                data.cur_bit_u[i] = get_next_dropable_bit(u_val[i], data.bound_u[i], data.cur_bit_u[i] - 1);
                if (data.cur_bit_l[i] >= 0) {
                    data.bound_l[i] =
                        bv_umin_const(data.bound_l[i], bv_lower_cover_bound(l_val[i], data.cur_bit_l[i]))
                            .simplify();
                }
                if (data.cur_bit_u[i] >= 0) {
                    data.bound_u[i] =
                        bv_umax_const(data.bound_u[i], bv_upper_cover_bound(u_val[i], data.cur_bit_u[i]))
                            .simplify();
                }
                if (data.cur_bit_l[i] >= 0) {
                    refine_possible = true;
                    z3::expr bound = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                    guess = guess || uge(l_var[i], bound);
                }
                if (data.cur_bit_u[i] >= 0) {
                    refine_possible = true;
                    z3::expr bound = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                    guess = guess || ult(u_var[i], bound);
                }
                trace_bounds("bounded", "next-candidate", i, data.cur_bit_l[i], data.cur_bit_u[i], l_val[i],
                             u_val[i], data.bound_l[i], data.bound_u[i]);
            }
            data.solver.pop();
        }
        if (progressed) {
            continue;
        }
        return;
    }
}

// Each refinement performs a standard bitwise query and, only after UNSAT,
// at most one bounded leap. Failed bit directions are consumed before the leap.
void UBVInvariant::tactic_bounded_bitwise_partial_efsolve() {
    auto accept_witness = [&](const z3::model& model) {
        bool changed = false;
        for (int i = 0; i < size; ++i) {
            const z3::expr model_l = model.eval(l_var[i], true);
            const z3::expr model_u = model.eval(u_var[i], true);
            trace_model_bound("optimal", i, model_l, model_u);
            if (ult(l_val[i], model_l).simplify().is_true()) {
                l_val[i] = model_l;
                changed = true;
            }
            if (ult(model_u, u_val[i]).simplify().is_true()) {
                u_val[i] = model_u;
                changed = true;
            }
            data.bound_l[i] = bv_umin_const(data.bound_l[i], u_val[i]).simplify();
            data.bound_u[i] = bv_umax_const(data.bound_u[i], l_val[i]).simplify();
        }
        if (!changed) {
            bad_solve = true;
            unknown_reason = "satisfiable strict refinement made no progress";
        }
    };

    while (!bad_solve) {
        bool proposed = false;
        z3::expr candidates = ctx.bool_val(false);
        for (int i = 0; i < size; ++i) {
            // Successful witnesses may resolve several positions at once.
            data.cur_bit_l[i] = get_next_0_bit(l_val[i], data.cur_bit_l[i]);
            data.cur_bit_u[i] = get_next_1_bit(u_val[i], data.cur_bit_u[i]);
            if (data.cur_bit_l[i] >= 0) {
                proposed = true;
                const z3::expr lower = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                candidates = candidates || uge(l_var[i], lower);
            }
            if (data.cur_bit_u[i] >= 0) {
                proposed = true;
                // The candidate upper bound is threshold-1. The threshold
                // has its tested bit set, so it is nonzero at every width.
                const z3::expr threshold = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                candidates = candidates || ult(u_var[i], threshold);
            }
            trace_bounds("optimal", "candidate", i, data.cur_bit_l[i], data.cur_bit_u[i], l_val[i],
                         u_val[i], data.bound_l[i], data.bound_u[i]);
        }
        if (!proposed)
            return;

        // A public optimal iteration is the complete refinement below, rather
        // than each of its one or two solver calls.
        require_iteration();
        ++iterations;
        data.solver.push();
        data.solver.add((candidates && get_current_lower_consts() && get_current_upper_consts()).simplify());
        const z3::check_result standard = solver_check(data.solver);
        trace_check("optimal", "refine", standard, smt_count);
        if (standard == z3::sat) {
            accept_witness(data.solver.get_model());
            data.solver.pop();
            continue;
        }
        data.solver.pop();
        if (standard == z3::unknown)
            return;

        // All proposed candidate regions were excluded. These integer-order
        // predecessor/successor updates are safe as bit-vector expressions:
        // lower>0 and candidate_upper<threshold<=MAX.
        bool nonempty_boundary = true;
        for (int i = 0; i < size; ++i) {
            if (data.cur_bit_l[i] >= 0) {
                const z3::expr lower = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
                data.bound_l[i] = bv_umin_const(data.bound_l[i], bv_decrement(lower)).simplify();
                --data.cur_bit_l[i];
            }
            if (data.cur_bit_u[i] >= 0) {
                const z3::expr threshold = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
                data.bound_u[i] = bv_umax_const(data.bound_u[i], threshold).simplify();
                --data.cur_bit_u[i];
            }
            if (ugt(data.bound_l[i], data.bound_u[i]).simplify().is_true())
                nonempty_boundary = false;
        }
        if (!nonempty_boundary)
            continue;

        // The failed positions are already consumed, including when this leap
        // succeeds. The next refinement must propose a new standard query.
        z3::expr tighter = ctx.bool_val(false);
        for (int i = 0; i < size; ++i)
            tighter = tighter || ult(l_val[i], l_var[i]) || ult(u_var[i], u_val[i]);
        data.solver.push();
        data.solver.add((tighter && get_current_lower_consts() && get_current_upper_consts()).simplify());
        const z3::check_result leap = solver_check(data.solver);
        trace_check("optimal", "bounded-leap", leap, smt_count);
        if (leap == z3::sat) {
            accept_witness(data.solver.get_model());
            data.solver.pop();
            continue;
        }
        data.solver.pop();
        // UNSAT establishes optimality; UNKNOWN preserves only the last
        // inductive witness and is recorded by solver_check.
        return;
    }
}

// Unmerged per-row bitwise proposals. Install complete inductive witnesses.
void UBVInvariant::tactic_unmerged_bitwise() {
    for (int i = 0; i < size; ++i) {
        data.cur_bit_l[i] = get_next_0_bit(l_val[i], data.cur_bit_l[i]);
        while (data.cur_bit_l[i] >= 0) {
            z3::expr bound = bv_raise_to_bit(l_val[i], data.cur_bit_l[i]);
            data.solver.push();
            data.solver.add((uge(l_var[i], bound) && get_current_upper_consts() && get_current_lower_consts())
                                .simplify());
            require_iteration();
            ++iterations;
            z3::check_result res = solver_check(data.solver);

            if (res == z3::sat) {
                z3::model model = data.solver.get_model();
                for (int j = 0; j < size; ++j) {
                    tighten_with_model_bound(l_val[j], u_val[j], model.eval(l_var[j], true),
                                             model.eval(u_var[j], true));
                }
            } else if (res == z3::unknown) {
                bad_solve = true;
                data.solver.pop();
                return;
            }
            data.solver.pop();
            data.cur_bit_l[i] = get_next_0_bit(l_val[i], data.cur_bit_l[i] - 1);
        }
        data.cur_bit_u[i] = get_next_1_bit(u_val[i], data.cur_bit_u[i]);
        while (data.cur_bit_u[i] >= 0) {
            z3::expr bound = bv_raise_to_bit(u_val[i], data.cur_bit_u[i]);
            data.solver.push();
            data.solver.add((ult(u_var[i], bound) && get_current_upper_consts() && get_current_lower_consts())
                                .simplify());
            require_iteration();
            ++iterations;
            z3::check_result res = solver_check(data.solver);

            if (res == z3::sat) {
                z3::model model = data.solver.get_model();
                for (int j = 0; j < size; ++j) {
                    tighten_with_model_bound(l_val[j], u_val[j], model.eval(l_var[j], true),
                                             model.eval(u_var[j], true));
                }
            } else if (res == z3::unknown) {
                bad_solve = true;
                data.solver.pop();
                return;
            }
            data.solver.pop();
            data.cur_bit_u[i] = get_next_1_bit(u_val[i], data.cur_bit_u[i] - 1);
        }
    }
    return;
}

// Chaotic iteration with binary-search best symbolic abstraction. Only the
// converged fixed point is published; interrupted iterates remain private.
void UBVInvariant::tactic_fix_binary_search() {
    z3::solver fix_sol(ctx);
    vector<z3::expr> l_new, u_new;
    function<bool()> abstraction = [&]() {
        for (int i = 0; i < size; ++i) {
            z3::expr l = data.bound_u[i];
            z3::expr r = u_val[i];
            while ((l != r).simplify().is_true()) {
                z3::expr mid = (l + lshr(r - l, 1)).simplify();
                fix_sol.push();
                fix_sol.add(ugt(var[i], mid));
                z3::check_result res = solver_check(fix_sol);

                if (res == z3::sat) {
                    l = (mid + 1).simplify();
                } else if (res == z3::unsat) {
                    r = mid;
                } else {
                    bad_solve = 1;
                    return false;
                }
                fix_sol.pop();
            }
            u_new.push_back(l);
            l = l_val[i];
            r = data.bound_l[i];
            while ((l != r).simplify().is_true()) {
                z3::expr mid = (l + lshr(r - l, 1)).simplify();
                fix_sol.push();
                fix_sol.add(ule(var[i], mid));
                z3::check_result res = solver_check(fix_sol);

                if (res == z3::sat) {
                    r = mid;
                } else if (res == z3::unsat) {
                    l = (mid + 1).simplify();
                } else {
                    bad_solve = 1;
                    return false;
                }
                fix_sol.pop();
            }
            l_new.push_back(l);
        }
        return true;
    };
    function<bool()> abstraction_bar = [&]() {
        z3::check_result res = solver_check(fix_sol);

        if (res != z3::sat) {
            if (res == z3::unknown) {
                bad_solve = 1;
            }
            return false;
        }
        z3::model model = fix_sol.get_model();
        for (int i = 0; i < size; ++i) {
            z3::expr l = model.eval(var_bar[i], true);
            z3::expr r = u_val[i];
            while ((l != r).simplify().is_true()) {
                z3::expr mid = (l + lshr(r - l, 1)).simplify();
                fix_sol.push();
                fix_sol.add(ugt(var_bar[i], mid));
                z3::check_result res = solver_check(fix_sol);

                if (res == z3::sat) {
                    l = (mid + 1).simplify();
                } else if (res == z3::unsat) {
                    r = mid;
                } else {
                    bad_solve = 1;
                    return false;
                }
                fix_sol.pop();
            }
            u_new[i] = bv_umax_const(u_new[i], l).simplify();
            l = l_val[i];
            r = model.eval(var_bar[i], true);
            while ((l != r).simplify().is_true()) {
                z3::expr mid = (l + lshr(r - l, 1)).simplify();
                fix_sol.push();
                fix_sol.add(ule(var_bar[i], mid));
                z3::check_result res = solver_check(fix_sol);

                if (res == z3::sat) {
                    r = mid;
                } else if (res == z3::unsat) {
                    l = (mid + 1).simplify();
                } else {
                    bad_solve = 1;
                    return false;
                }
                fix_sol.pop();
            }
            l_new[i] = bv_umin_const(l_new[i], l).simplify();
        }
        return true;
    };
    require_iteration();
    fix_sol.push();
    fix_sol.add(trans.pre);
    if (!abstraction()) {
        bad_solve = 1;
        return;
    }
    ++iterations;
    fix_sol.pop();
    fix_sol.add(trans.trans);
    while (true) {
        require_iteration();
        fix_sol.push();
        z3::expr inv = ctx.bool_val(true);
        z3::expr inv_bar = ctx.bool_val(true);
        for (int i = 0; i < size; ++i) {
            inv = inv && ule(l_new[i], var[i]) && ule(var[i], u_new[i]);
            inv_bar = inv_bar && ule(l_new[i], var_bar[i]) && ule(var_bar[i], u_new[i]);
        }
        fix_sol.add(inv && !inv_bar);
        const bool changed = abstraction_bar();
        if (bad_solve) {
            return;
        }
        ++iterations;
        if (!changed) {
            l_val = l_new;
            u_val = u_new;
            return;
        }
        fix_sol.pop();
    }
}

// Chaotic iteration with bilateral symbolic abstraction. Model points grow
// an inner bound; UNSAT queries tighten the outer abstraction.
void UBVInvariant::tactic_fix_bilateral() {
    z3::solver fix_sol(ctx);
    vector<z3::expr> l_new, u_new;
    vector<z3::expr> l_upper, u_upper;
    function<bool()> abstract_sequence = [&]() {
        l_new.clear();
        u_new.clear();
        bool tag = false;
        for (int i = 0; i < size; ++i) {
            l_new.emplace_back((l_upper[i] + lshr(data.bound_l[i] - l_upper[i], 1)).simplify());
            if ((l_new.back() != l_upper[i]).simplify().is_true()) {
                tag = true;
            }
            u_new.emplace_back((data.bound_u[i] + lshr(u_upper[i] - data.bound_u[i], 1)).simplify());
            if ((u_new.back() != u_upper[i]).simplify().is_true()) {
                tag = true;
            }
        }
        if (!tag) {
            for (int i = 0; i < size; ++i) {
                if ((data.bound_l[i] != l_upper[i]).simplify().is_true()) {
                    l_new[i] = (l_upper[i] + 1).simplify();
                    tag = true;
                    break;
                }
            }
        }
        return tag;
    };
    function<bool()> abstraction = [&]() {
        l_upper = l_val;
        u_upper = u_val;
        while (true) {
            if (!abstract_sequence()) {
                return true;
            }
            z3::expr lim = ctx.bool_val(true);
            for (int i = 0; i < size; ++i) {
                lim = lim && ule(l_new[i], var[i]) && ule(var[i], u_new[i]);
            }
            fix_sol.push();
            fix_sol.add(!lim);
            z3::check_result res = solver_check(fix_sol);

            if (res == z3::sat) {
                z3::model model = fix_sol.get_model();
                for (int i = 0; i < size; ++i) {
                    z3::expr model_val = model.eval(var[i], true);
                    data.bound_l[i] = bv_umin_const(data.bound_l[i], model_val).simplify();
                    data.bound_u[i] = bv_umax_const(data.bound_u[i], model_val).simplify();
                }
            } else if (res == z3::unsat) {
                for (int i = 0; i < size; ++i) {
                    l_upper[i] = bv_umax_const(l_upper[i], l_new[i]).simplify();
                    u_upper[i] = bv_umin_const(u_upper[i], u_new[i]).simplify();
                }
            } else {
                bad_solve = 1;
                return false;
            }
            fix_sol.pop();
        }
    };
    function<bool()> abstraction_bar = [&]() {
        l_upper = l_val;
        u_upper = u_val;
        bool tag = false;
        while (true) {
            if (!abstract_sequence()) {
                return tag;
            }
            z3::expr lim = ctx.bool_val(true);
            for (int i = 0; i < size; ++i) {
                lim = lim && ule(l_new[i], var_bar[i]) && ule(var_bar[i], u_new[i]);
            }
            fix_sol.push();
            fix_sol.add(!lim);
            z3::check_result res = solver_check(fix_sol);

            if (res == z3::sat) {
                z3::model model = fix_sol.get_model();
                for (int i = 0; i < size; ++i) {
                    z3::expr model_val = model.eval(var_bar[i], true);
                    data.bound_l[i] = bv_umin_const(data.bound_l[i], model_val).simplify();
                    data.bound_u[i] = bv_umax_const(data.bound_u[i], model_val).simplify();
                }
                tag = true;
            } else if (res == z3::unsat) {
                for (int i = 0; i < size; ++i) {
                    l_upper[i] = bv_umax_const(l_upper[i], l_new[i]).simplify();
                    u_upper[i] = bv_umin_const(u_upper[i], u_new[i]).simplify();
                }
            } else {
                bad_solve = 1;
                return false;
            }
            fix_sol.pop();
        }
    };
    require_iteration();
    fix_sol.push();
    fix_sol.add(trans.pre);
    if (!abstraction()) {
        bad_solve = 1;
        return;
    }
    ++iterations;
    fix_sol.pop();
    fix_sol.add(trans.trans);
    while (true) {
        require_iteration();
        fix_sol.push();
        z3::expr inv = ctx.bool_val(true);
        for (int i = 0; i < size; ++i) {
            inv = inv && ule(l_upper[i], var[i]) && ule(var[i], u_upper[i]);
        }
        fix_sol.add(inv);
        const bool changed = abstraction_bar();
        if (bad_solve) {
            return;
        }
        ++iterations;
        if (!changed) {
            l_val = l_upper;
            u_val = u_upper;
            return;
        }
        fix_sol.pop();
    }
}

// Merged binary-search refinement over the current learned boundary limits.
void UBVInvariant::tactic_binary_search() {
    while (!bad_solve) {
        vector<z3::expr> l_mid, u_mid;
        bool refine_possible = false;
        bool progressed = false;
        z3::expr guess = ctx.bool_val(false);
        for (int i = 0; i < size; ++i) {
            data.bound_l[i] = bv_umin_const(data.bound_l[i], u_val[i]).simplify();
            data.bound_u[i] = bv_umax_const(data.bound_u[i], l_val[i]).simplify();
            l_mid.push_back((l_val[i] + lshr(data.bound_l[i] - l_val[i], 1)).simplify());
            u_mid.push_back((data.bound_u[i] + lshr(u_val[i] - data.bound_u[i], 1)).simplify());
            if (ult(l_val[i], data.bound_l[i]).simplify().is_true()) {
                refine_possible = true;
                guess = guess || ugt(l_var[i], l_mid[i]);
            }
            if (ult(u_mid[i], u_val[i]).simplify().is_true()) {
                refine_possible = true;
                guess = guess || ule(u_var[i], u_mid[i]);
            }
            trace_bounds("bsearch", "candidate", i, -1, -1, l_val[i], u_val[i], data.bound_l[i],
                         data.bound_u[i]);
        }

        while (refine_possible) {
            data.solver.push();
            data.solver.add((guess && get_current_lower_consts() && get_current_upper_consts()).simplify());
            require_iteration();
            ++iterations;
            z3::check_result res = solver_check(data.solver);

            trace_check("bsearch", "refine", res, smt_count);

            if (res == z3::sat) {
                z3::model model = data.solver.get_model();
                bool changed = false;
                for (int i = 0; i < size; ++i) {
                    z3::expr model_l = model.eval(l_var[i], true);
                    z3::expr model_u = model.eval(u_var[i], true);
                    trace_model_bound("bsearch", i, model_l, model_u);
                    if (ult(l_val[i], model_l).simplify().is_true()) {
                        data.bound_u[i] = bv_umax_const(data.bound_u[i], model_l).simplify();
                        l_val[i] = model_l;
                        changed = true;
                    }
                    if (ult(model_u, u_val[i]).simplify().is_true()) {
                        data.bound_l[i] = bv_umin_const(data.bound_l[i], model_u).simplify();
                        u_val[i] = model_u;
                        changed = true;
                    }
                }
                if (changed) {
                    data.solver.pop();
                    progressed = true;
                    break;
                }
                trace_check("bsearch", "sat-no-progress", res, smt_count);
                bad_solve = true;
                unknown_reason = "satisfiable strict refinement made no progress";
                data.solver.pop();
                return;
            } else if (res == z3::unknown) {
                bad_solve = true;
                data.solver.pop();
                return;
            }

            refine_possible = false;
            guess = ctx.bool_val(false);
            for (int i = 0; i < size; ++i) {
                data.bound_l[i] = bv_umin_const(data.bound_l[i], l_mid[i]).simplify();
                if (ult(u_mid[i], u_val[i]).simplify().is_true()) {
                    data.bound_u[i] = bv_umax_const(data.bound_u[i], (u_mid[i] + 1).simplify()).simplify();
                }
                l_mid[i] = (l_val[i] + lshr(data.bound_l[i] - l_val[i], 1)).simplify();
                u_mid[i] = (data.bound_u[i] + lshr(u_val[i] - data.bound_u[i], 1)).simplify();
                if (ult(l_val[i], data.bound_l[i]).simplify().is_true()) {
                    refine_possible = true;
                    guess = guess || ugt(l_var[i], l_mid[i]);
                }
                if (ult(u_mid[i], u_val[i]).simplify().is_true()) {
                    refine_possible = true;
                    guess = guess || ule(u_var[i], u_mid[i]);
                }
                trace_bounds("bsearch", "next-candidate", i, -1, -1, l_val[i], u_val[i], data.bound_l[i],
                             data.bound_u[i]);
            }
            data.solver.pop();
        }
        if (progressed) {
            continue;
        }
        return;
    }
}

} // namespace invfinder
