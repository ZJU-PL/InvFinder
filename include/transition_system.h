#pragma once

#include <string>
#include <vector>
#include <z3++.h>

namespace invfinder {

// The context must outlive this object and every result constructed from it.
// pre/post refer to vars; trans may also refer to vars_bar. Clause-local
// nondeterministic values are bound by quantifiers, never free constants.
struct transitionSystem {
    z3::context& ctx;
    z3::expr pre;
    z3::expr trans;
    z3::expr post;
    std::vector<z3::expr> vars;
    std::vector<z3::expr> vars_bar;
    std::string logic;

    transitionSystem(z3::expr pre, z3::expr trans, z3::expr post,
                     std::vector<z3::expr> vars,
                     std::vector<z3::expr> vars_bar,
                     std::string logic = "BV");

    z3::expr_vector get_ori_consts() const;
    z3::expr_vector get_bar_consts() const;
    z3::expr_vector get_all_consts() const;
};

// Read SMT-LIB assert/forall/=> CHCs through Z3's native parser. Supported:
// a single positive-arity relation over bit-vectors, at most one occurrence
// of that relation in each conjunctive body, and a relation/theory head.
// Theory terms may use nonlinear bit-vector arithmetic. Unsupported CHC
// structures and undeclared state parameters throw std::runtime_error.
transitionSystem load_chc(z3::context& ctx, const std::string& filename);

} // namespace invfinder
