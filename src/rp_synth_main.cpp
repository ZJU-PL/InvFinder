#include "rp_cli.h"
#include <iostream>

int main(int argc, char** argv) {
    try {
        const auto command = invfinder::parse_rp_options(argc, argv, false);
        if (command.help) { invfinder::print_rp_help(false); return 0; }
        if (command.version) { std::cout << "InvFinder-RP; Z3 " << invfinder::rp::solver_version() << '\n'; return 0; }
        const auto problem = invfinder::rp::read_problem(command.file);
        const auto result = invfinder::rp::synthesize(problem, command.options);
        if (!command.dump.empty()) invfinder::rp::write_certificates(problem, result, command.dump);
        std::cout << invfinder::rp::result_json(problem, result);
        return result.complete ? 0 : 3;
    } catch (const std::exception& error) {
        std::cerr << "rp_synth: " << error.what() << '\n';
        return 2;
    }
}
