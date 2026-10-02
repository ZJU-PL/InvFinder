#pragma once
#include "cli.h"
#include "rp/reduced_product.hpp"

namespace invfinder {
struct RPCommand {
    rp::Options options;
    std::string file, domain = "interval+knownbits", dump;
    bool help = false, version = false;
};
inline RPCommand parse_rp_options(int argc, char** argv, bool chc) {
    RPCommand command;
    for (int i = 1; i < argc; ++i) {
        const std::string key = argv[i];
        auto value = [&]() {
            if (i + 1 == argc) throw std::invalid_argument("Missing value for " + key);
            return std::string(argv[++i]);
        };
        if (key == "--help" || key == "-h") command.help = true;
        else if (key == "--version") command.version = true;
        else if (key == "--file" || key == "-F") command.file = value();
        else if (chc && (key == "--domain" || key == "-D")) command.domain = value();
        else if (key == "--method" || key == "-M") command.options.method = value();
        else if (key == "--timeout" || key == "-T") command.options.timeout_seconds = seconds(value());
        else if (key == "--max-queries") command.options.max_solver_calls = iteration_limit(value());
        else if (key == "--max-candidates") command.options.max_candidates = iteration_limit(value());
        else if (key == "--certify") command.options.certify_best = true;
        else if (key == "--dump") command.dump = value();
        else if (key == "--no-reduction") command.options.reduction = false;
        else if (key == "--no-promotion") command.options.promotion = false;
        else if (key == "--range-first") command.options.flat_first = false;
        else if (!key.empty() && key.front() != '-' && command.file.empty()) command.file = key;
        else throw std::invalid_argument("Unknown option: " + key);
    }
    if (!command.help && !command.version && command.file.empty())
        throw std::invalid_argument("Provide an input file or use --file FILE");
    return command;
}
inline void print_rp_help(bool chc) {
    std::cout << (chc ? "rp_bestInv FILE.smt2 [--domain PRODUCT]\n" : "rp_synth FILE.rp\n")
        << "  --method quantified|cegis   ACR or CARE (default: cegis)\n"
           "  --timeout SECONDS          Synthesis deadline (default: 30; -1 unlimited)\n"
           "  --max-queries N            Solver-call budget (-1 or unlimited disables)\n"
           "  --max-candidates N         CARE candidate budget (-1 or unlimited disables)\n"
           "  --certify                  Independently check bestness\n"
           "  --dump PREFIX              Write initiation, consecution, and bestness obligations\n"
           "  --no-reduction --no-promotion --range-first   Algorithm ablations\n"
           "  --help --version\n";
    if (chc) std::cout << "Products combine interval, signed, zones, octagon, octagon-forward,\n"
        "polyhedra, template-polyhedra, knownbits, congruence:M using '+'.\n"
        "Default: interval+knownbits. Moduli are decimal integers >= 2.\n";
    std::cout << "JSON output; exit codes: 0 complete, 3 incomplete, 2 input/validation error.\n";
}
} // namespace invfinder
