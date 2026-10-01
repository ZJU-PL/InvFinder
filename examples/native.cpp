#include "invariant.h"
#include <iostream>

// Construct a three-bit counter directly with the Z3 API.
int main() {
    z3::context ctx;
    auto x = ctx.bv_const("x", 3), next = ctx.bv_const("x_next", 3);
    invfinder::transitionSystem loop(
        x == ctx.bv_val(5, 3),
        z3::ult(x, ctx.bv_val(6, 3)) && next == x + 1,
        z3::ule(x, ctx.bv_val(6, 3)), {x}, {next});
    invfinder::UBVInvariant result(loop, "interval");
    result.set_timer(10);
    result.runTactic("optimal");
    std::cout << result.get_inv_with_var({x}) << '\n';
    return result.complete && !result.bad_solve ? 0 : 1;
}
