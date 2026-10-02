#include "reduced_product.h"
#include "rp_cli.h"
#include <iostream>

int main(int argc, char** argv) {
    try {
        const auto command = invfinder::parse_rp_options(argc, argv, true);
        if (command.help) { invfinder::print_rp_help(true); return 0; }
        if (command.version) { std::cout << "InvFinder-RP; Z3 " << invfinder::rp::solver_version() << '\n'; return 0; }
        z3::context ctx;
        invfinder::ReducedProductInvariant engine(invfinder::load_chc(ctx, command.file));
        engine.add_product(command.domain);
        const auto& result = engine.run(command.options);
        if (!command.dump.empty()) invfinder::rp::write_certificates(engine.problem(), result, command.dump);
        std::cout << invfinder::rp::result_json(engine.problem(), result);
        return result.complete ? 0 : 3;
    } catch (const std::exception& error) {
        std::cerr << "rp_bestInv: " << error.what() << '\n';
        return 2;
    }
}
