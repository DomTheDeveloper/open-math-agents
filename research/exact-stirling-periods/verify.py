"""Verify the period certificates and exact-cycle comparisons (Python standard library)."""
import argparse
from functools import reduce
from math import comb, gcd, lcm
from pathlib import Path


def factors(number):
    result = {}
    divisor = 2
    while divisor * divisor <= number:
        while number % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            number //= divisor
        divisor += 1
    if number > 1:
        result[number] = 1
    return result


def least_prime_power_period(b, p, e):
    if p == 2:
        threshold, shift = (3, 5) if b == 1 else (6, 7)
        return 1 if e <= threshold else 2 ** max(1, e - shift)
    if p == 3:
        threshold = 1 if b == 1 else 5
        return 3 ** (e - 1) * (1 if e <= threshold else 2)
    return (p - 1) * p ** (e - 1)


def least_period(b, m):
    if b not in (1, 2) or m < 1:
        raise ValueError('Use b=1 or 2 and a positive modulus.')
    return lcm(*(least_prime_power_period(b, p, e) for p, e in factors(m).items()))


def factorial_cutoff(m):
    k, residue = 0, 1 % m
    while residue:
        k += 1
        residue = residue * k % m
    return k


def weights(b, m):
    """Coefficients of sum g_k (y-1)^k modulo m, through the factorial cutoff."""
    cutoff = factorial_cutoff(m)
    result = [0] * cutoff
    for k in range(cutoff):
        g = comb(2 * k, k) * pow(b, k, m)
        for j in range(k + 1):
            coefficient = (-1) ** (k - j) * comb(k, j) * g
            result[j] = (result[j] + coefficient) % m
    return result


def difference_window(b, m, start, step):
    coeffs = weights(b, m)
    terms = [c * pow(j, start, m) * (pow(j, step, m) - 1) % m
             for j, c in enumerate(coeffs)]
    result = []
    for _ in coeffs:
        result.append(sum(terms) % m)
        terms = [j * term % m for j, term in enumerate(terms)]
    return result


def check_certificates():
    for b, bare, shift, anchor in ((1, 3, 5, 3), (2, 6, 7, 5)):
        for s in range(anchor + 1):
            valuation = bare if s == 0 else s + shift
            modulus = 2 ** (valuation + 1)
            differences = difference_window(b, modulus, valuation + 1, 2 ** s)
            assert reduce(gcd, differences, modulus) == 2 ** valuation
    assert difference_window(1, 9, 2, 3) == [6, 3] * 3
    assert difference_window(2, 243, 5, 81) == [0] * 12
    assert difference_window(2, 729, 6, 243) == [486, 243] * 7 + [486]


def derivative_terms(b, last):
    """Use (1+4b-4b exp x) F' = 2b exp(x) F and exact integer arithmetic."""
    result, row = [1], [1]
    for n in range(last):
        first = sum(c * result[k] for k, c in enumerate(row))
        second = sum(c * result[k + 1] for k, c in enumerate(row[:-1]))
        result.append(2 * b * first + 4 * b * second)
        row = [1] + [row[k - 1] + row[k] for k in range(1, n + 1)] + [1]
    return result


def stirling_terms(b, last):
    weights_g = [b ** k * comb(2 * k, k) for k in range(last + 1)]
    row, result = [1], [1]
    for n in range(1, last + 1):
        previous = row + [0]
        row = [0] + [k * (previous[k] + previous[k - 1]) for k in range(1, n + 1)]
        result.append(sum(g * entry for g, entry in zip(weights_g, row)))
    return result


def carmichael(m):
    powers = [(2 ** max(1, e - 2) if p == 2 and e >= 2 else (p - 1) * p ** (e - 1))
              for p, e in factors(m).items()]
    return lcm(*powers)


def measured_period(terms, m):
    onset_bound = max(factors(m).values(), default=0)
    universal = carmichael(m)
    block = [value % m for value in terms[onset_bound:onset_bound + 2 * universal]]
    assert len(block) == 2 * universal and block[:universal] == block[universal:]
    period = universal
    for q in factors(universal):
        while period % q == 0:
            candidate = period // q
            if any(block[i] != block[i + candidate] for i in range(universal)):
                break
            period = candidate
    return period


def check_fermat_quotients():
    count = 0
    for b in (1, 2):
        for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
            h = (p - 1) // 2
            law = []
            for r in range(1, h + 1):
                weight = comb(h, r) * pow(1 + 4 * b, h - r, p) * pow(-4 * b, r, p)
                quotient = (pow(r, p - 1, p * p) - 1) // p
                law.append((r, weight * (quotient - 2 * b * pow(r, -1, p)) % p))
            for e in (2, 3, 4):
                modulus = p ** e
                divisor = p ** (e - 1)
                shift = (p - 1) * p ** (e - 2)
                terms = weights(b, modulus)
                for n in range(e, e + p - 1):
                    difference = sum(weight * pow(j, n, modulus) * (pow(j, shift, modulus) - 1)
                                     for j, weight in enumerate(terms)) % modulus
                    assert difference % divisor == 0
                    predicted = sum(weight * pow(r, n, p) for r, weight in law) % p
                    assert difference // divisor == predicted, (b, p, e, n)
                    count += 1
    print(f'{count} normalized Fermat-quotient identities checked directly.')


def compare_oeis(directory, sequence, terms):
    lines = (directory / f'{sequence}.seq').read_text(encoding='utf8').splitlines()
    listed = [int(number) for line in lines if line.startswith(('%S ', '%T ', '%U '))
              for number in line.split(' ', 2)[2].strip(',').split(',')]
    assert listed and listed == terms[:len(listed)]
    print(f'{sequence}: all {len(listed)} displayed OEIS terms agree.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oeis-dir', type=Path, help='optional directory with both OEIS .seq files')
    args = parser.parse_args()
    check_certificates()
    check_fermat_quotients()
    print('13 finite windows verified (10 dyadic and 3 ternary).')
    moduli = list(range(1, 513)) + [729, 1000, 1024]
    last = max(max(factors(m).values(), default=0) + 2 * carmichael(m) for m in moduli)
    for b in (1, 2):
        terms = derivative_terms(b, last)
        assert terms[:101] == stirling_terms(b, 100)
        if args.oeis_dir:
            compare_oeis(args.oeis_dir, {1: "A354242", 2: "A354253"}[b], terms)
        for m in moduli:
            measured = measured_period(terms, m)
            assert measured == least_period(b, m), (b, m, measured, least_period(b, m))
        print(f'b={b}: exact recurrence and Stirling transform agree at indices 0..100; '
              f'{len(moduli)} least periods checked using two full universal periods.')
    for m in (9, 64, 243, 729, 1000, 1024):
        print(f'{m:4}: {least_period(1,m):4} {least_period(2,m):4}')


if __name__ == '__main__':
    main()
