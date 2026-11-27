// Prove that each n from 2 through 7587 admits a prime k*(k+1)^phi(n-k)+1.
// The input pairs (n,k) are from Dev Pratap Singh, DevSingh05/oeis-a234360,
// revision 2dd137006c176c1b8780f50452e9a102f695d80c, data/witnesses_c3.txt.
// Its MIT license is reproduced in proofs/OeisA234360.conjecture_3.lean.
// Input: sequential lines "n k" (find a full-order base) or "n k a" (verify
// the supplied base). Output: n k a. The accompanying TSV uses bases found here.
// Build: c++ -O3 -std=c++17 -fopenmp prove_7588_minimal.cpp -lgmpxx -lgmp -o minimal
// Run: OMP_NUM_THREADS=3 ./minimal tools/sun_7588_prime_witnesses.tsv > checked.tsv
#include <gmpxx.h>
#include <array>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

constexpr unsigned limit = 7588;

std::vector<unsigned> prime_divisors(unsigned value) {
    std::vector<unsigned> factors;
    for (unsigned p = 2; p * p <= value; ++p) {
        if (value % p) continue;
        factors.push_back(p);
        do { value /= p; } while (value % p == 0);
    }
    if (value > 1) factors.push_back(value);
    return factors;
}

bool full_order(const mpz_class& m, const mpz_class& order,
                const std::vector<unsigned>& primes, unsigned witness) {
    const mpz_class a = witness;
    if (a < 2 || a >= m || mpz_jacobi(a.get_mpz_t(), m.get_mpz_t()) != -1) return false;
    mpz_class residue, exponent;
    mpz_powm(residue.get_mpz_t(), a.get_mpz_t(), order.get_mpz_t(), m.get_mpz_t());
    if (residue != 1) return false;
    for (unsigned p : primes) {
        mpz_divexact_ui(exponent.get_mpz_t(), order.get_mpz_t(), p);
        mpz_powm(residue.get_mpz_t(), a.get_mpz_t(), exponent.get_mpz_t(), m.get_mpz_t());
        if (residue == 1) return false;
    }
    // The order of a modulo m is m-1. Its distinct powers are m-1 units,
    // so every nonzero residue is invertible and m is prime.
    return true;
}

struct Row { unsigned k = 0; unsigned base = 0; };

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: minimal path/to/witnesses.tsv\n";
        return 2;
    }
    std::ifstream input(argv[1]);
    std::array<Row, limit> rows{};
    std::array<unsigned char, limit> fixed{};
    std::string line;
    for (unsigned n = 2; n < limit; ++n) {
        if (!std::getline(input, line)) return 2;
        std::istringstream in(line);
        unsigned index;
        if (!(in >> index >> rows[n].k) || index != n || rows[n].k == 0 || rows[n].k >= n)
            return 2;
        in >> std::ws;
        if (!in.eof()) {
            if (!(in >> rows[n].base)) return 2;
            in >> std::ws;
            if (!in.eof()) return 2;
            fixed[n] = 1;
        }
    }
    while (std::getline(input, line)) if (line.find_first_not_of(" \t\r") != std::string::npos) return 2;

    std::array<unsigned, limit> phi{};
    for (unsigned n = 1; n < limit; ++n) {
        phi[n] = n;
        for (unsigned p : prime_divisors(n)) phi[n] -= phi[n] / p;
    }
    #pragma omp parallel for schedule(dynamic, 1)
    for (unsigned n = 2; n < limit; ++n) {
        const unsigned k = rows[n].k;
        mpz_class order;
        mpz_ui_pow_ui(order.get_mpz_t(), k + 1, phi[n - k]);
        order *= k;
        const mpz_class m = order + 1;
        auto primes = prime_divisors(k);
        auto next = prime_divisors(k + 1);
        primes.insert(primes.end(), next.begin(), next.end());
        if (fixed[n]) {
            if (!full_order(m, order, primes, rows[n].base)) rows[n].base = 0;
        } else {
            for (unsigned a = 2; a <= 1024 && a < m; ++a)
                if (full_order(m, order, primes, a)) { rows[n].base = a; break; }
        }
    }
    unsigned largest_base = 0;
    for (unsigned n = 2; n < limit; ++n) {
        if (!rows[n].base) {
            std::cerr << "No valid full-order certificate for n = " << n << '\n';
            return 1;
        }
        if (rows[n].base > largest_base) largest_base = rows[n].base;
    }
    for (unsigned n = 2; n < limit; ++n)
        std::cout << n << '\t' << rows[n].k << '\t' << rows[n].base << '\n';
    std::cerr << "Proved prime witnesses for all 7586 smaller n; largest base "
              << largest_base << ".\n";
}
