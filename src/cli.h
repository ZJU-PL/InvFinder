#pragma once
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <z3++.h>

namespace invfinder {
struct Options {
    std::string file, domain = "interval", tactic = "optimal";
    double timeout = 60.0, synthesis_timeout = 10.0;
    unsigned max_k = 64;
    std::int64_t inv_iterations = -1;
    bool validate = false, help = false, version = false;
};
inline std::int64_t iteration_limit(const std::string& value) {
    if (value == "unlimited" || value == "-1") return -1;
    if (value.empty() || value.find_first_not_of("0123456789") != std::string::npos)
        throw std::invalid_argument("Iterations must be a nonnegative integer, -1, or unlimited");
    try {
        const auto result = std::stoull(value);
        if (result <= static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max()))
            return static_cast<std::int64_t>(result);
    } catch (const std::exception&) {}
    throw std::invalid_argument("Iteration limit is too large");
}
inline double seconds(const std::string& value) {
    std::size_t end = 0;
    double result = std::stod(value, &end);
    if (end != value.size() || !std::isfinite(result) || (result < 0 && result != -1))
        throw std::invalid_argument("Timeout must be nonnegative seconds or -1 (unlimited)");
    return result;
}
inline Options parse_options(int argc, char** argv, bool verification) {
    Options o;
    bool domain_set = false, tactic_set = false, iterations_set = false;
    if (verification) { o.domain = "none"; o.tactic = "none"; }
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        if (a == "-h" || a == "--help") { o.help = true; continue; }
        if (a == "--version") { o.version = true; continue; }
        if (a == "--validate" && !verification) { o.validate = true; continue; }
        if (i + 1 == argc) throw std::invalid_argument("Missing value for " + a);
        const std::string v = argv[++i];
        if (a == "-F" || a == "--file") o.file = v;
        else if (a == "-D" || a == "--domain" || (verification && a == "--inv-domain")) {
            o.domain = v; domain_set = true;
        }
        else if (a == "-M" || a == "--tactic" || (verification && a == "--inv-tactic")) {
            o.tactic = v; tactic_set = true;
        }
        else if (a == "-I" || a == "--iterations" || (verification && a == "--inv-iterations")) {
            o.inv_iterations = iteration_limit(v); iterations_set = true;
        }
        else if (a == "-T" || a == "--timeout") o.timeout = seconds(v);
        else if (a == "--synthesis-timeout" && verification) o.synthesis_timeout = seconds(v);
        else if ((a == "-K" || a == "--max-k") && verification) {
            std::size_t end = 0;
            const auto k = std::stoull(v, &end);
            if (v.empty() || v.front() == '-' || end != v.size() || k > std::numeric_limits<unsigned>::max())
                throw std::invalid_argument("Invalid induction depth: " + v);
            o.max_k = static_cast<unsigned>(k);
        } else throw std::invalid_argument("Unknown option: " + a);
    }
    if (!o.help && !o.version && o.file.empty()) throw std::invalid_argument("Use -F <CHC SMT2 file>");
    if (o.help || o.version) return o;
    if (verification && !domain_set && ((tactic_set && o.tactic != "none") || iterations_set))
        o.domain = "interval";
    if (verification && tactic_set && o.tactic == "none" && o.domain != "none")
        throw std::invalid_argument("Tactic none requires --inv-domain none");
    if (verification && o.domain != "none" && o.tactic == "none") o.tactic = "optimal";
    if (verification && o.domain == "none" && (o.tactic != "none" || iterations_set))
        throw std::invalid_argument("Invariant tactic/iterations conflict with --inv-domain none");
    return o;
}
inline void print_help(bool verification) {
    std::cout << (verification ? "kInductor" : "bestInv")
      << " -F input.smt2 [-D domain] [-M tactic] [-T seconds]\n"
      << "Domains: interval, zones, octagon, octagon-forward, polyhedra, knownbits"
      << (verification ? ", none (default)\n" : " (default: interval)\n")
      << "Tactics: efsolve, bitwise, bounded, optimal, bitbase, bsearch, bilater, fixbsrh\n"
      << "Timeout: 60 seconds by default; -1 disables the deadline.\n";
    if (verification)
      std::cout << "-K/--max-k: maximum transition depth (default 64)\n"
                   "-D/--inv-domain: template domain (none for pure k-induction)\n"
                   "-M/--inv-tactic: tactic used to precompute the auxiliary invariant\n"
                   "-I/--inv-iterations: iteration limit; N, -1, or unlimited (default unlimited)\n"
                   "An invariant tactic or iteration limit enables interval synthesis by default.\n"
                   "--synthesis-timeout: auxiliary synthesis budget (default 10 seconds), within -T\n"
                   "Uses pure k-induction or a precomputed auxiliary invariant.\n";
    else std::cout << "-I/--iterations: synthesis iteration limit; N, -1, or unlimited (default unlimited)\n"
                      "--validate: independently check initiation and inductiveness\n";
    std::cout << "Iterations count propose-and-refine attempts; optimal includes its optional bounded leap.\n"
                 "fixbsrh/bilater count completed abstraction rounds.\n"
                 "Zero iterations uses top; unlimited iterations still obey time limits.\n";
    std::cout << "--version: print the linked Z3 version\n";
}
} // namespace invfinder
