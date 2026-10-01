#include "transition_system.h"

#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>

namespace {

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}

void equivalent(const z3::expr& actual, const z3::expr& expected,
                const std::string& message) {
    z3::solver solver(actual.ctx());
    solver.add(actual != expected);
    require(solver.check() == z3::unsat, message);
}

struct Inputs {
    std::filesystem::path directory;
    unsigned next = 0;
    Inputs() {
        const auto stamp = std::chrono::steady_clock::now().time_since_epoch().count();
        directory = std::filesystem::temp_directory_path() /
                    ("invfinder-parser-" + std::to_string(stamp));
        std::filesystem::create_directory(directory);
    }
    ~Inputs() { std::error_code error; std::filesystem::remove_all(directory, error); }
    std::string write(const std::string& text) {
        const auto path = directory / (std::to_string(next++) + ".smt2");
        std::ofstream stream(path);
        stream << text;
        if (!stream) throw std::runtime_error("could not write test input");
        return path.string();
    }
};

void rejected(z3::context& ctx, Inputs& inputs, const std::string& text,
              const std::string& explanation) {
    bool failed = false;
    try { (void)invfinder::load_chc(ctx, inputs.write(text)); }
    catch (const std::runtime_error&) { failed = true; }
    require(failed, explanation);
}

} // namespace

int main(int argc, char** argv) {
    try {
        z3::context ctx;
        Inputs inputs;
        const std::filesystem::path examples = argc > 1 ? argv[1] : "examples";
        const auto counter = invfinder::load_chc(ctx, (examples / "counter.smt2").string());
        const auto x = counter.vars[0], next = counter.vars_bar[0];
        equivalent(counter.pre, x == ctx.bv_val(0, 8), "counter initial states");
        equivalent(counter.trans, z3::ult(x, ctx.bv_val(10, 8)) &&
                   next == x + ctx.bv_val(1, 8), "counter transition");
        equivalent(counter.post, z3::ule(x, ctx.bv_val(10, 8)), "counter safety");

        const auto local = invfinder::load_chc(ctx, (examples / "local_choice.smt2").string());
        const auto lx = local.vars[0], ln = local.vars_bar[0];
        equivalent(local.trans, z3::ult(lx, ctx.bv_val(3, 4)) &&
                   (ln == lx || ln == lx + ctx.bv_val(1, 4)),
                   "local choices must be existentially projected");
        equivalent(local.post, z3::ule(lx, ctx.bv_val(3, 4)), "false-head safety query");

        // Quantifier order is deliberately unrelated to current/next-state
        // order. Multiple initial rules and a safety-local variable are used.
        const auto shuffled = invfinder::load_chc(ctx, inputs.write(R"(
(set-logic HORN)
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (forall ((choice (_ BitVec 4)) (x (_ BitVec 4)))
  (=> (and (inv x) (= choice (bvadd x #x1))) (bvult choice #x4))))
(assert (inv #x1))
(assert (forall ((new (_ BitVec 4)) (old (_ BitVec 4)))
  (=> (and (= new (bvadd old #x1)) (inv old) (bvult old #x2)) (inv new))))
(assert (forall ((initial (_ BitVec 4)))
  (=> (= initial #x1) (inv (bvadd initial #x1)))))
)"));
        const auto sx = shuffled.vars[0], sn = shuffled.vars_bar[0];
        equivalent(shuffled.pre, sx == ctx.bv_val(1, 4) || sx == ctx.bv_val(2, 4),
                   "multiple initial rules and expression relation arguments");
        equivalent(shuffled.trans, z3::ult(sx, ctx.bv_val(2, 4)) &&
                   sn == sx + ctx.bv_val(1, 4), "binder order must not determine state order");
        equivalent(shuffled.post, z3::ult(sx + ctx.bv_val(1, 4), ctx.bv_val(4, 4)),
                   "safety locals must be universally respected");

        const auto repeated = invfinder::load_chc(ctx, inputs.write(R"(
(declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 4))) (inv x x)))
(assert (forall ((a (_ BitVec 4)) (b (_ BitVec 4)))
  (=> (inv a b) (inv b a))))
)"));
        equivalent(repeated.pre, repeated.vars[0] == repeated.vars[1],
                   "repeated relation arguments must retain equality");
        equivalent(repeated.trans, repeated.vars_bar[0] == repeated.vars[1] &&
                   repeated.vars_bar[1] == repeated.vars[0], "shared source/target locals");
        equivalent(repeated.post, ctx.bool_val(true), "missing safety must be true");

        rejected(ctx, inputs, R"(
(declare-fun a ((_ BitVec 4)) Bool)
(declare-fun b ((_ BitVec 4)) Bool)
(assert (a #x0)) (assert (=> (a #x0) (b #x0)))
)", "multiple predicates must be rejected");
        rejected(ctx, inputs, R"(
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
  (=> (and (inv x) (inv y)) (inv (bvadd x y)))))
)", "nonlinear CHC bodies must be rejected");
        rejected(ctx, inputs, R"(
(declare-fun inv (Int) Bool) (assert (inv 0))
)", "non-BV state must be rejected");
        rejected(ctx, inputs, R"(
(declare-fun inv ((_ BitVec 4)) Bool)
(declare-const parameter (_ BitVec 4)) (assert (inv parameter))
)", "free global parameters must be rejected");
        rejected(ctx, inputs, R"(
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 4)))
  (=> (or (inv x) (= x #x0)) (inv (bvadd x #x1)))))
)", "predicate under disjunction must be rejected");
        rejected(ctx, inputs, R"(
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (inv #x0)) (rule (=> (inv #x0) (inv #x1)))
)", "mixed assert/rule inputs must not silently drop transitions");

        std::cout << "parser tests passed\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
