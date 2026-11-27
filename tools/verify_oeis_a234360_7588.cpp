// Check Sun's third A234360 assertion at n = 7588 using the witness lists
// in proofs/OeisA234360.conjecture_3.lean. Dev Pratap Singh discovered the
// counterexample and published the witnesses in DevSingh05/oeis-a234360.
//
// Build: c++ -O3 -std=c++17 -fopenmp verify_oeis_a234360_7588.cpp -lgmpxx -lgmp -o verify7588
// Run: OMP_NUM_THREADS=3 ./verify7588 proofs/OeisA234360.conjecture_3.lean
#include <gmpxx.h>
#include <array>
#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

constexpr unsigned n = 7588;

std::vector<unsigned long> read_witnesses(const char* path) {
    std::ifstream file(path);
    if (!file) throw std::runtime_error("cannot open the Lean proof");
    const std::regex declaration(R"(^private def w([0-9]+) : List ℕ := \[([^\]]*)\]$)");
    const std::regex number(R"(^\s*([0-9]+)\s*$)");
    std::vector<unsigned long> divisors(1); // The first candidate is k = 1.
    std::string line;
    unsigned expected_block = 0;
    while (std::getline(file, line)) {
        if (line.rfind("private def w", 0) != 0) continue;
        std::smatch fields;
        if (!std::regex_match(line, fields, declaration) ||
            std::stoul(fields[1]) != expected_block++) {
            throw std::runtime_error("missing or malformed witness block");
        }
        std::stringstream values(fields[2].str());
        std::string item;
        while (std::getline(values, item, ',')) {
            std::smatch value;
            if (!std::regex_match(item, value, number))
                throw std::runtime_error("invalid divisor in witness block");
            divisors.push_back(std::stoul(value[1]));
        }
    }
    if (divisors.size() != n) throw std::runtime_error("expected 7587 witnesses");
    return divisors;
}

std::array<unsigned, n> totients() {
    std::array<unsigned, n> phi{};
    for (unsigned m = 0; m < n; ++m) phi[m] = m;
    for (unsigned p = 2; p < n; ++p) {
        if (phi[p] != p) continue;
        for (unsigned m = p; m < n; m += p) phi[m] -= phi[m] / p;
    }
    return phi;
}

bool proves_composite(unsigned k, unsigned exponent, unsigned long divisor) {
    mpz_class candidate;
    mpz_ui_pow_ui(candidate.get_mpz_t(), k + 1, exponent);
    candidate = k * candidate + 1;
    if (divisor != 0)
        return divisor > 1 && divisor < candidate &&
               mpz_divisible_ui_p(candidate.get_mpz_t(), divisor);
    if (candidate <= 2) return false;
    const mpz_class base = 2, power = candidate - 1;
    mpz_class residue;
    mpz_powm(residue.get_mpz_t(), base.get_mpz_t(), power.get_mpz_t(), candidate.get_mpz_t());
    return residue != 1; // Every prime greater than two has residue one.
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: verify7588 path/to/OeisA234360.conjecture_3.lean\n";
        return 2;
    }
    try {
        const auto divisors = read_witnesses(argv[1]);
        const auto phi = totients();
        std::array<unsigned char, n> verified{};
        #pragma omp parallel for schedule(dynamic, 1)
        for (unsigned k = 1; k < n; ++k)
            verified[k] = proves_composite(k, phi[n - k], divisors[k]);
        unsigned factors = 0;
        for (unsigned k = 1; k < n; ++k) {
            if (!verified[k]) {
                std::cerr << "Invalid compositeness witness at k = " << k << '\n';
                return 1;
            }
            if (divisors[k]) ++factors;
        }
        std::cout << "Verified all " << n - 1 << " candidates: " << factors
                  << " proper divisors, " << n - 1 - factors << " failed Fermat tests.\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
