// Independently find the least allowed first term in ab+bc+ac through a finite limit.
// For given a,b, write n+a^2=(a+b)(a+c) and enumerate the complementary factor.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>

int main() {
    constexpr std::uint64_t limit = 100000000;
    const std::vector<std::uint64_t> euler = {
        1,2,3,4,5,6,7,8,9,10,12,13,15,16,18,21,22,24,25,28,30,33,37,40,42,45,48,
        57,58,60,70,72,78,85,88,93,102,105,112,120,130,133,165,168,177,190,210,232,
        240,253,273,280,312,330,345,357,385,408,462,520,760,840,1320,1365,1848
    };
    std::vector<std::uint64_t> covered(limit/64+1);
    for (std::uint64_t a = 1; a <= 14; ++a) {
        const std::uint64_t bound = limit + a*a;
        for (std::uint64_t d = 2*a+1; d*(d+1) <= bound; ++d) {
            for (std::uint64_t product = d*(d+1); product <= bound; product += d) {
                const auto n = product-a*a;
                covered[n/64] |= (std::uint64_t{1} << (n%64));
            }
        }
        if (a < 13) continue;
        std::vector<std::uint64_t> missing;
        for (std::uint64_t n=1; n<=limit; ++n) {
            if (!(covered[n/64] & (std::uint64_t{1} << (n%64)))) missing.push_back(n);
        }
        auto expected=euler;
        if (a==13) expected.push_back(136173);
        if (missing!=expected) return 1;
        std::cout << "a <= " << a << ", unrepresented " << missing.size()
                  << ", largest " << missing.back() << '\n' << std::flush;
    }
}
