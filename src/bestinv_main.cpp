#include "cli.h"
#include "invariant.h"
#include <chrono>

using namespace invfinder;
int main(int argc, char** argv) {
    try {
        const auto o = parse_options(argc, argv, false);
        if (o.help) { print_help(false); return 0; }
        if (o.version) { std::cout << "InvFinder; Z3 " << Z3_get_full_version() << '\n'; return 0; }
        z3::context ctx;
        auto ts = load_chc(ctx, o.file);
        UBVInvariant inv(ts, o.domain);
        const auto start = std::chrono::steady_clock::now();
        inv.set_timer(o.timeout);
        inv.runTactic(o.tactic, o.inv_iterations);
        const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        std::cout << "---Analysis Result---\nFile: " << o.file
          << "\nDomain: " << o.domain << "\nTactic: " << o.tactic
          << "\nSynthesis status: " << (inv.complete ? "good" : inv.bad_solve ? "bad" : "partial")
          << "\nOptimality: " << (inv.complete && !inv.bad_solve ? "established" : "not established")
          << "\nIterations: " << inv.iterations
          << "\nIteration limit: " << (o.inv_iterations < 0 ? "unlimited" : std::to_string(o.inv_iterations))
          << "\nTime used: " << elapsed << "s\nSMT(OMT) calls: " << inv.smt_count
          << "\nInvariant: " << inv.l_val_string() << inv.u_val_string() << '\n';
        if (!inv.unknown_reason.empty()) std::cout << "Reason: " << inv.unknown_reason << '\n';
        else if (inv.iteration_limit_reached) std::cout << "Reason: iteration limit\n";
        if (o.validate) {
            z3::solver check(ctx);
            check.set("timeout", 10000u);
            check.add(ts.pre && !inv.get_inv_with_var(ts.vars));
            auto initial = check.check();
            check.reset(); check.set("timeout", 10000u);
            check.add(inv.get_inv_with_var(ts.vars) && ts.trans && !inv.get_inv_with_var(ts.vars_bar));
            auto inductive = check.check();
            std::cout << "Validation: initiation=" << initial << ", consecution=" << inductive << '\n';
            if (initial != z3::unsat || inductive != z3::unsat) return 2;
        }
        // A structured partial/unknown result is a successful invocation, not a proof of bestness.
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "bestInv error: " << e.what() << '\n'; return 1;
    }
}
