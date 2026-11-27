"""Find the least first-term bound covering every positive non-idoneal input through --limit."""
from argparse import ArgumentParser
from math import isqrt
from idoneal import EULER, witness


def cover(limit):
    if limit < 1:
        raise ValueError('the limit must be positive')
    known = tuple(n for n in EULER if n <= limit)
    covered = bytearray(limit + 1)
    previous_count = limit
    previous = None
    for a in range(1, isqrt((limit-1)//3)+1):
        b = a + 1
        while True:
            step = a+b
            first = a*b + step*(b+1)
            if first > limit:
                break
            count = (limit-first)//step + 1
            covered[first:limit+1:step] = bytes([1])*count
            b += 1
        count = covered.count(0)-1
        if count <= len(known)+15:
            survivors=[]
            x = covered.find(0,1)
            while x >= 0:
                if x not in known:
                    survivors.append(x)
                x=covered.find(0,x+1)
            print(a, count, survivors, flush=True)
            if count == len(known) and not survivors and all(covered[n]==0 for n in known):
                if previous is not None and previous_count <= len(known)+15:
                    return a, previous
                for n in range(1, limit+1):
                    if n not in known and witness(n, a-1) is None:
                        return a, [n]
                raise RuntimeError('no sharpness witness')
        previous = survivors if count <= len(known)+15 else None
        previous_count = count
    raise RuntimeError('the list or cutoff is incorrect')


if __name__ == '__main__':
    parser=ArgumentParser(description=__doc__);parser.add_argument('--limit',type=int,default=100_000_000);opt=parser.parse_args()
    if opt.limit < 1:
        parser.error('the limit must be positive')
    if opt.limit < 11:
        print('The interval contains only exceptions.')
    else:
        bound, critical=cover(opt.limit)
        print('Least first-term bound',bound,flush=True)
        if critical:
            for n in critical:
                first=witness(n)
                if first is None or first[0]!=bound:raise RuntimeError(n)
                print('Sharpness witness',n,first,flush=True)
