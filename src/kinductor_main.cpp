#include "cli.h"
#include "invariant.h"
#include "k_induction.h"
#include <algorithm>
#include <chrono>

using namespace invfinder;
int main(int argc, char** argv) {
    try {
        const auto o = parse_options(argc, argv, true);
        if (o.help) { print_help(true); return 0; }
        if (o.version) { std::cout << "InvFinder k-induction; Z3 " << Z3_get_full_version() << '\n'; return 0; }
        z3::context ctx;
        auto ts = load_chc(ctx, o.file);
        const auto start = std::chrono::steady_clock::now();
        z3::expr auxiliary = ctx.bool_val(true);
        if (o.domain != "none") {
            UBVInvariant inv(ts, o.domain);
            double budget = o.synthesis_timeout;
            if (o.timeout >= 0) budget = budget < 0 ? o.timeout : std::min(budget, o.timeout);
            inv.set_timer(budget); inv.runTactic(o.tactic, o.inv_iterations);
            auxiliary = inv.get_inv_with_var(ts.vars);
            std::cout << "Auxiliary synthesis: " << (inv.complete ? "complete" : "partial")
              << "\nInvariant tactic: " << o.tactic
              << "\nInvariant iterations: " << inv.iterations
              << "\nInvariant iteration limit: " << (o.inv_iterations < 0 ? "unlimited" : std::to_string(o.inv_iterations))
              << "\nAuxiliary invariant: " << inv.l_val_string() << inv.u_val_string() << '\n';
            if (inv.iteration_limit_reached) std::cout << "Auxiliary stop reason: iteration limit\n";
            else if (!inv.unknown_reason.empty()) std::cout << "Auxiliary stop reason: " << inv.unknown_reason << '\n';
        }
        const double synthesis_elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        KInductionOptions options;
        options.max_k = o.max_k;
        options.timeout_seconds = o.timeout < 0 ? -1 : std::max(0.0, o.timeout - synthesis_elapsed);
        auto result = k_induction(ts, options, o.domain == "none" ? nullptr : &auxiliary);
        const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        std::cout << "---Verification Result---\nFile: " << o.file
          << "\nTactic(s): " << o.tactic << "\nMode: " << (o.domain == "none" ? "pure" : "precomputed auxiliary")
          << "\nTermination status: " << (result.status == VerificationStatus::Unknown ? "bad" : "good")
          << "\nTime used: " << elapsed << "s\nRequired K: " << result.k
          << "\nResult: " << verification_status_name(result.status)
          << "\nReason: " << result.reason << '\n';
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "kInductor error: " << e.what() << '\n'; return 1;
    }
}
