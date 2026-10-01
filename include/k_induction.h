#pragma once

#include "transition_system.h"
#include <string>

namespace invfinder {

enum class VerificationStatus { Safe, Unsafe, Unknown };

struct KInductionOptions {
    // Maximum transition depth, inclusive. At depth zero only the initial
    // state and the implication auxiliary => post are checked.
    unsigned max_k = 64;
    // Wall-clock budget for verification and auxiliary validation; negative
    // values disable the timeout. A zero budget returns Unknown immediately.
    double timeout_seconds = 60.0;
};

struct KInductionResult {
    VerificationStatus status = VerificationStatus::Unknown;
    unsigned k = 0;
    unsigned base_checks = 0;
    unsigned induction_checks = 0;
    unsigned auxiliary_checks = 0;
    double elapsed_seconds = 0.0;
    std::string reason;
};

const char* verification_status_name(VerificationStatus status);

// Optional auxiliary is a Boolean expression over ts.vars. Its initiation and
// consecution are independently checked before it is used in induction.
// Other free symbols/functions are rejected; quantifier-bound variables are
// allowed. In particular, a next-state variable cannot be an auxiliary parameter.
// Auxiliary constraints never restrict the reachable-counterexample search.
// Runs pure k-induction or strengthens it with the supplied invariant.
KInductionResult k_induction(const transitionSystem& ts,
                            const KInductionOptions& options = {},
                            const z3::expr* auxiliary = nullptr);

} // namespace invfinder
