#pragma once
#include <boost/multiprecision/cpp_int.hpp>
#include <cstdint>
#include <string>
#include <vector>

namespace invfinder::rp {
using Integer = boost::multiprecision::cpp_int;
struct Variable {
    std::string current, next;
    unsigned width;
};
struct Row {
    std::string label;
    unsigned width;
    std::string current, next;
};
// A range row tracks unsigned bounds on an arbitrary BV expression. A flat row
// tracks TOP or equality of an arbitrary BV expression to a single constant.
// Examples: signed intervals use x XOR signbit, known bits use extract,
// congruences use bvurem, and predicate facts use ite(predicate,#b1,#b0).
struct Problem {
    std::vector<Variable> variables;
    std::string pre, transition;
    std::vector<Row> ranges, flats;
    void validate() const;
};
struct Element {
    bool bottom = false;
    std::vector<Integer> lower, upper;
    std::vector<bool> enabled;
    std::vector<Integer> constants;
};
struct Options {
    std::string method = "cegis"; // "quantified" = ACR; "cegis" = CARE
    double timeout_seconds = 30;
    std::int64_t max_solver_calls = -1;
    std::int64_t max_candidates = -1;
    bool reduction = true;
    bool promotion = true;
    bool flat_first = true;
    bool certify_best = false;
};
struct Statistics {
    std::uint64_t initial = 0, quantified = 0, candidate = 0;
    std::uint64_t verifier = 0, reduction = 0, certificate = 0;
    std::uint64_t proposals = 0, reduction_hits = 0;
    std::uint64_t positive_samples = 0, implication_samples = 0;
    std::uint64_t promoted_targets = 0, envelope_updates = 0;
    std::uint64_t accepted_candidates = 0;
    double seconds = 0;
    std::uint64_t calls() const;
};
struct Result {
    Element invariant;
    bool complete = false;
    bool sound = true; // only validated candidates or equivalent reductions publish
    bool bestness_certified = false;
    std::string reason;
    Statistics stats;
};
Result synthesize(const Problem&, const Options& = {});
std::string formula(const Problem&, const Element&, bool next = false);
std::string result_json(const Problem&, const Result&);
std::string solver_version();
Problem read_problem(const std::string& filename);
void write_certificates(const Problem&, const Result&, const std::string& prefix);
} // namespace invfinder::rp
