#include "reduced_product.h"
#include "k_induction.h"
#include <iostream>
#include <stdexcept>

using namespace invfinder;
namespace {
void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}
template<class F> void rejects(F action) {
    bool rejected = false;
    try { action(); } catch (const std::exception&) { rejected = true; }
    require(rejected, "Expected invalid API usage to be rejected");
}
void equivalent(const z3::expr& left, const z3::expr& right) {
    z3::solver solver(left.ctx());
    solver.set("timeout", 10000u);
    solver.add(left != right);
    require(solver.check() == z3::unsat, "Unexpected invariant semantics");
}
void sound(const transitionSystem& system, const ReducedProductInvariant& engine) {
    z3::solver solver(system.ctx);
    solver.set("timeout", 10000u);
    solver.add(system.pre && !engine.get_inv_with_var(system.vars));
    require(solver.check() == z3::unsat, "Initiation failed");
    solver.reset(); solver.set("timeout", 10000u);
    solver.add(engine.get_inv_with_var(system.vars) && system.trans &&
               !engine.get_inv_with_var(system.vars_bar));
    require(solver.check() == z3::unsat, "Consecution failed");
}
}
int main(int argc, char** argv) {
    try {
        require(argc == 2, "Provide the examples directory");
        z3::context ctx;
        const auto system = load_chc(ctx, std::string(argv[1]) + "/reduced_product/mutual_interval_bits.smt2");
        const auto x = system.vars[0];
        const auto expected = z3::ule(x, ctx.bv_val(10, 4)) && x.extract(0, 0) == ctx.bv_val(0, 1);
        for (const std::string method : {"quantified", "cegis"}) {
            rp::Options options; options.method = method; options.certify_best = true;
            options.timeout_seconds = 15;
            for (const std::string product : {"interval", "knownbits", "interval+knownbits"}) {
                ReducedProductInvariant engine(system); engine.add_product(product);
                const auto& result = engine.run(options);
                require(result.complete && result.bestness_certified, "Synthesis/certification incomplete");
                equivalent(engine.get_inv_with_var(system.vars), product == "interval+knownbits" ? expected : ctx.bool_val(true));
                sound(system, engine);
                if (product == "interval+knownbits") {
                    auto auxiliary = engine.get_inv_with_var(system.vars);
                    KInductionOptions verification; verification.max_k = 0;
                    require(k_induction(system, verification, &auxiliary).status == VerificationStatus::Safe,
                            "Reduced-product auxiliary did not prove safety");
                    rejects([&] { engine.run(options); });
                    rejects([&] { engine.add_product("interval"); });
                    rejects([&] { engine.add_domain("knownbits"); });
                    rejects([&] { engine.get_inv_with_var({ctx.bv_const("wrong", 3)}); });
                    z3::context foreign;
                    rejects([&] { engine.get_inv_with_var({foreign.bv_const("other", 4)}); });
                }
            }
            for (const std::int64_t budget : {0, 1, 3, 8, 16}) {
                options.max_solver_calls = budget;
                ReducedProductInvariant engine(system); engine.add_product("interval+knownbits");
                const auto& result = engine.run(options);
                require(result.stats.calls() <= static_cast<std::uint64_t>(budget), "Query budget exceeded");
                sound(system, engine);
            }
            options.max_solver_calls = -1;
            // CHC projection retains a quantified nondeterministic local.
            const auto local = load_chc(ctx, std::string(argv[1]) + "/local_choice.smt2");
            ReducedProductInvariant choices(local); choices.add_product("interval+knownbits");
            require(choices.run(options).complete, "Quantified CHC local interrupted synthesis");
            equivalent(choices.get_inv_with_var(local.vars), z3::ule(local.vars[0], ctx.bv_val(3, 4)));
            sound(local, choices);
            // Mixed widths, quoted state names, and relational congruence/predicate observations.
            auto a = ctx.bv_const("a with spaces", 2), an = ctx.bv_const("a next", 2);
            auto b = ctx.bv_const("b", 3), bn = ctx.bv_const("b next", 3);
            transitionSystem mixed(a == 0 && b == 0, an == a + 1 && bn == b + 2,
                                   ctx.bool_val(true), {a, b}, {an, bn});
            ReducedProductInvariant relation(mixed); relation.add_product("octagon+signed+knownbits+congruence:03");
            relation.add_flat("diff_mod3", z3::urem(b - z3::zext(a, 1), ctx.bv_val(3, 3)));
            relation.add_flat("predicate", z3::ite(b.extract(0, 0) == 0, ctx.bv_val(1, 1), ctx.bv_val(0, 1)));
            require(relation.run(options).complete, "Mixed-width synthesis incomplete");
            equivalent(relation.get_inv_with_var(mixed.vars), b.extract(0, 0) == 0);
            sound(mixed, relation);
            // Signed bounds across zero and a wide value retain exact BV semantics.
            auto s = ctx.bv_const("signed", 4), sn = ctx.bv_const("signed_next", 4);
            transitionSystem signed_loop(s == 9, sn == z3::ite(s < ctx.bv_val(3, 4), s + 1, s),
                                         ctx.bool_val(true), {s}, {sn});
            ReducedProductInvariant signed_engine(signed_loop); signed_engine.add_product("interval+signed");
            require(signed_engine.run(options).complete, "Signed synthesis incomplete");
            equivalent(signed_engine.get_inv_with_var({s}), s >= ctx.bv_val(9, 4) && s <= ctx.bv_val(3, 4));
            auto wide = ctx.bv_const("wide", 128), widen = ctx.bv_const("wide_next", 128);
            transitionSystem wide_loop(wide == ctx.bv_val("170141183460469231731687303715884105728", 128),
                                       widen == wide, ctx.bool_val(true), {wide}, {widen});
            ReducedProductInvariant wide_engine(wide_loop); wide_engine.add_product("interval");
            require(wide_engine.run(options).complete, "128-bit adapter synthesis incomplete");
            equivalent(wide_engine.get_inv_with_var({wide}), wide_loop.pre);
            transitionSystem empty(ctx.bool_val(false), ctx.bool_val(true), ctx.bool_val(false), {s}, {sn});
            ReducedProductInvariant bottom(empty); bottom.add_product("interval+knownbits");
            require(bottom.run(options).invariant.bottom, "Empty initialization did not yield bottom");
            equivalent(bottom.get_inv_with_var({s}), ctx.bool_val(false));
        }
        for (const std::string product : {"", "interval+", "+interval", "interval++knownbits", "interval+interval",
                                          "congruence:", "congruence:1", "congruence:16", "congruence:3x", "unknown"}) {
            ReducedProductInvariant engine(system);
            rejects([&] { engine.add_product(product); });
        }
        ReducedProductInvariant unused(system);
        rejects([&] { unused.result(); });
        rejects([&] { unused.get_inv_with_var(system.vars); });
        std::cout << "PASS: native reduced-product adapter, CHCs, budgets, and auxiliary k-induction\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n'; return 1;
    }
}
