"""Find an ordered idoneal-number witness and independently enumerate the exceptions."""
from argparse import ArgumentParser
from math import isqrt

EULER = (
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24,
    25, 28, 30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88,
    93, 102, 105, 112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240,
    253, 273, 280, 312, 330, 345, 357, 385, 408, 462, 520, 760, 840, 1320,
    1365, 1848,
)


def witness(n, first_limit=None):
    """Return an (a,b,c) with 0<a<b<c and ab+bc+ac=n, if one exists."""
    if n < 1:
        raise ValueError('the input must be positive')
    bound = isqrt((n-1)//3)
    if first_limit is not None:
        bound = min(bound, first_limit)
    for a in range(1, bound + 1):
        product = n + a*a
        for d in range(2*a+1, isqrt(product-1) + 1):
            quotient, remainder = divmod(product, d)
            if remainder == 0:
                return a, d-a, quotient-a
    return None


def sieve(limit, first_factor_limit=None, require_capped_witness=False):
    """Mark progressions in c, then individually decide survivors if a is capped."""
    if limit < 1:
        raise ValueError('the limit must be positive')
    represented = bytearray(limit+1)
    largest_a = isqrt((limit-1)//3)
    if first_factor_limit is not None:
        if first_factor_limit < 1:
            raise ValueError('the first-factor cutoff must be positive')
        largest_a = min(largest_a, first_factor_limit)
    for a in range(1, largest_a + 1):
        b = a+1
        while True:
            step = a+b
            first = a*b + step*(b+1)
            if first > limit:
                break
            count = (limit-first)//step + 1
            represented[first:limit+1:step] = bytes([1])*count
            b += 1
    exceptions = []
    n = represented.find(0, 1)
    while n != -1:
        triple = None if first_factor_limit is None or require_capped_witness else witness(n)
        if triple is None:
            exceptions.append(n)
        else:
            a, b, c = triple
            if not (0 < a < b < c and a*b + b*c + a*c == n):
                raise RuntimeError(f'invalid witness for {n}')
        n = represented.find(0, n+1)
    return tuple(exceptions)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', nargs='*', type=int)
    parser.add_argument('--verify', type=int, metavar='LIMIT')
    parser.add_argument('--first-factor-limit', type=int, metavar='A', help='sieve up to A and inspect every survivor with the factor-window test')
    parser.add_argument('--only-first', type=int, metavar='A', help='verify every nonexception has a triple with first term at most A')
    args = parser.parse_args()
    if args.verify is not None:
        if args.only_first is not None and args.first_factor_limit is not None:
            parser.error('choose one first-factor option')
        limit_a = args.only_first if args.only_first is not None else args.first_factor_limit
        observed = sieve(args.verify, limit_a, args.only_first is not None)
        expected = tuple(n for n in EULER if n <= args.verify)
        if observed != expected:
            raise RuntimeError((observed, expected))
        for n in range(1,min(args.verify,10000)+1):
            proof = witness(n)
            if proof is None:
                if n not in observed:
                    raise RuntimeError(f'missing witness at {n}')
            else:
                a,b,c=proof
                if not (0<a<b<c and a*b+b*c+a*c==n and n not in observed):
                    raise RuntimeError(f'invalid witness at {n}')
        print(f'Found {len(observed)} exceptions through {args.verify:,}. The largest is {max(observed)}.')
    for n in args.n:
        print(n, witness(n))

if __name__ == '__main__':
    main()
