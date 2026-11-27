"""Independent checks for the continued fractions, OEIS claims and dyadic periods."""
from argparse import ArgumentParser
from math import comb, factorial
from pathlib import Path


def moments(a, u, v, degree):
    """Stirling formula, calculated over the integers."""
    weights = [1]
    for k in range(degree):
        weights.append(weights[-1] * (a + k*u))
    row, result = [1], []
    for n in range(degree+1):
        result.append(sum(s * (v-u)**(n-k) * weights[k] for k, s in enumerate(row)))
        row = [k*s + prev for k,(s,prev) in enumerate(zip(row+[0], [0]+row))]
    return result


def fraction(a, u, v, degree):
    """Bottom-up nested fractions via coefficient comparison in (1 - alpha*z*tail)*out = 1."""
    tail = [1] + [0]*degree
    for h in range(degree-1, -1, -1):
        j = h//2
        alpha = a+j*u if h%2 == 0 else (j+1)*v
        out = [1]
        for n in range(1,degree+1):
            out.append(alpha*sum(tail[i]*out[n-1-i] for i in range(n)))
        tail = out
    return tail


def polynomial_rows(u, v, degree):
    """Source definition P_next(x)=x*((u-v)*P(x)+v*P(x+1))."""
    rows = [[1]]
    for _ in range(degree):
        row = rows[-1]
        shifted = [sum(comb(i,j)*row[i] for i in range(j,len(row))) for j in range(len(row))]
        rows.append([0] + [(u-v)*p+v*q for p,q in zip(row,shifted)])
    return rows


SCALARS = {'A305404': (1,2,3), 'A354242': (2,4,5), 'A354253': (4,8,9)}
TRIANGLES = {'A079641': (1,2), 'A195204': (2,1), 'A195205': (3,2)}


def check_formulas():
    degree = 24
    for pars in SCALARS.values():
        assert moments(*pars, degree) == fraction(*pars, degree)
    for u,v in TRIANGLES.values():
        rows = polynomial_rows(u,v,degree)
        for x in range(degree+1):
            direct = [sum(coef*x**k for k,coef in enumerate(row)) for row in rows]
            assert direct == moments(u*x,u,v,degree) == fraction(u*x,u,v,degree)
    print('Six continued fractions matched through degree 24. Polynomial identities used 25 distinct x values and degree at most 24.')
    a = moments(3,2,3,60)
    b = moments(1,2,3,61)[1:]
    assert a[0] == b[0] == 1
    for n in range(1,61):
        assert a[n] == b[n-1] + 2*sum(comb(n,j)*a[j] for j in range(n))
        assert b[n] == b[n-1] + sum(comb(n-1,j)*a[j+1] for j in range(n))
    print('The coupled recurrence and the A305404 shift matched through n=60.')


def source_terms(root, name):
    with (root / (name+'.seq')).open() as stream:
        fields = [line.split(maxsplit=2)[2].strip().strip(',') for line in stream
                  if line.startswith(('%S ', '%T ', '%U '))]
    return [int(n) for field in fields for n in field.split(',') if n]


def check_sources(root):
    counts = {}
    for name,params in {**SCALARS,'A375948': (3,2,3)}.items():
        terms = source_terms(root,name)
        assert terms == moments(*params,len(terms)-1), name
        counts[name] = len(terms)
    for name,(u,v) in TRIANGLES.items():
        terms = source_terms(root,name)
        rows = polynomial_rows(u,v,12)
        flat = [k for row in rows[1:] for k in row[1:]]
        assert terms == flat[:len(terms)], name
        counts[name] = len(terms)
    print(f'Matched all {sum(counts.values())} displayed integers in seven OEIS entries: {dict(sorted(counts.items()))}.')


def predicted_cycle(c,e):
    if not c:
        return 1,1
    if c%2:
        return 0, 3 if e == 1 else 3*2**e
    b = abs(c)//2
    t = (b & -b).bit_length()-1
    onset = max(1, e-1-2*t)
    if e <= 3*t+3:
        return onset,1
    return onset,2**max(1,e-3*t-4-int(t==0))


def modular_moments(c, modulus, length):
    """Jacobi paths with unit up weight. An excursion reaching K contains a factor K!."""
    K = 1
    while factorial(K)%modulus:
        K += 1
    diagonal = [(c+(4*c+1)*h)%modulus for h in range(K)]
    down = [(h+1)*(2*c+1)*c*(2*h+1)%modulus for h in range(K)]
    row, result = [1]+[0]*K, []
    for _ in range(length):
        result.append(row[0])
        row = [((row[h-1] if h else 0) + diagonal[h]*row[h] + down[h]*row[h+1])%modulus
               for h in range(K)] + [0]
    return result


def measure(values, mod, start, upper):
    residues = [n%mod for n in values[:start+2*upper]]
    block = residues[start:start+upper]
    assert block == residues[start+upper:], (mod,start,upper)
    # The prefix function finds the least period of the repeating word independently.
    prefix = [0]*len(block)
    for i in range(1,len(block)):
        j = prefix[i-1]
        while j and block[i] != block[j]:
            j = prefix[j-1]
        if block[i] == block[j]:
            j += 1
        prefix[i] = j
    candidate = len(block)-prefix[-1]
    period = candidate if len(block)%candidate == 0 else len(block)
    onset = next((n+1 for n in range(start-1,-1,-1) if residues[n] != residues[n+period]),0)
    return onset,period


def check_cycles():
    max_e = 10
    for c in range(-24,25):
        values = modular_moments(c,2**max_e, max_e+6*2**max_e)
        assert values[:25] == [n%2**max_e for n in moments(c,2*c,2*c+1,24)]
        for e in range(1,max_e+1):
            upper = (3 if c%2 else 1) * 2**e
            observed = measure(values,2**e,e,upper)
            assert observed == predicted_cycle(c,e), (c,e,observed,predicted_cycle(c,e))
    print('490 signed parameter/modulus pairs checked (integers -24 through 24, exponents 1 through 10). Both the least period and earliest starting index matched in all 490.')
    for c in (1,2,3,4):
        N,T = predicted_cycle(c,6)
        values = modular_moments(c,64,N+T)
        print(f'c={c} modulo 64: first index {N}, period {T}'
              + (f', repeating block {values[N:]}' if T<=2 else ''))


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--oeis-dir',type=Path,help='directory containing the seven listed .seq files')
    args = parser.parse_args()
    check_formulas()
    if args.oeis_dir:
        check_sources(args.oeis_dir)
    check_cycles()
