# Continued fractions and exact cycles of Stirling transforms

The [seven-page proof](StirlingTransforms.pdf) establishes eight formulas recorded as conjectural across seven OEIS entries. It also determines the earliest start and least eventual period of an integer family modulo every power of two.

## Which formulas are proved

| OEIS entry | Formula in the entry | Result |
| --- | --- | --- |
| [A305404](https://oeis.org/A305404) | Bala's continued fraction and Rattaggi's infinite sum | Both hold for every index, including zero |
| [A354242](https://oeis.org/A354242) | Bala's continued fraction | Numerators in consecutive pairs are $4j+2$ and $5(j+1)$ for $j\ge0$ |
| [A354253](https://oeis.org/A354253) | Bala's continued fraction | Numerators are $8j+4$ and $9(j+1)$ |
| [A079641](https://oeis.org/A079641) | Continued fraction for the row polynomials | Numerators are $x+j$ and $2(j+1)$ |
| [A195204](https://oeis.org/A195204) | Continued fraction for the row polynomials | Numerators are $2(x+j)$ and $j+1$ |
| [A195205](https://oeis.org/A195205) | Continued fraction for the row polynomials | Numerators are $3(x+j)$ and $2(j+1)$ |
| [A375948](https://oeis.org/A375948) | Kurkov's coupled recurrence and its proposed auxiliary sequence | Both equations hold, with $b_n=\mathrm{A305404}(n+1)$ |

The common continued fraction is classical. Sokal and Zeng give the fraction and its explicit Stirling formula in equations (2.2), (2.3) and (2.12) and credit Stieltjes, section 81. The six entries are applications of that result. [Sokal and Zeng (2022)](https://doi.org/10.1016/j.aam.2022.102341)

## The arithmetic theorem

Let $a_c(n)$ be the Stirling transform of $c^k(2k-1)!!$ for any integer $c$, with $(-1)!!=1$. Let $N$ be the earliest index where the eventual cycle begins modulo $2^e$ and $T$ its least positive period, for $e\ge1$.

- For $c=0$, $(N,T)=(1,1)$.
- For odd $c$, $N=0$. The least period is 3 at $e=1$ and $3\cdot2^e$ at every $e\ge2$.
- For nonzero $c=2b$, set $t=v_2(b)$ and $L=3t+4+\mathbf{1}_{t=0}$. Then $N=\max(1,e-1-2t)$. The period is 1 for $e\le3t+3$ and $2^{\max(1,e-L)}$ for $e>3t+3$.

The [earlier note](https://github.com/DomTheDeveloper/open-math-agents/blob/6ac3356a6c8ec804cee7b17aa714278711db2376/research/exact-stirling-periods/ExactPeriods.pdf) treats the periods of $c=2,4$ at all moduli. The present theorem covers the start and length for every integer parameter at powers of two. Historical priority for the general classification is unverified.

## Reproduce the checks

Use Lean 4.33.1 and Python 3. The Lean files require only the standard distribution.

```sh
lake build
python3 verify.py
```

The [coefficient theorem](ContinuedFractions.lean) equates the affine Stirling recurrence to the paired weighted-path recurrence at every index for all integer parameter choices. The written proof identifies these with the displayed Stirling sum and the continued fraction by decomposing a path at its first return. The three row-polynomial applications follow coefficientwise, since they agree at every integer specialization.

The [residue certificates](ResidueCertificates.lean) verify every coefficient of four finite polynomial windows and the four odd residue cases in the sharpness proof. The [lifting theorem](DyadicPower.lean) proves the all-exponent congruence for every odd integer base. The remaining arithmetic arguments, the analytic moment formula and the coupled recurrence are proved in the [manuscript](StirlingTransforms.tex).

The Python program compares truncated continued fractions with the independent Stirling formula and polynomial recurrences, both coupled equations through index 60, and minimum cycles for 490 signed parameter/modulus pairs. To reproduce the seven published data comparisons, download the seven linked entries from the [pinned OEIS export](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq). For example A305404 is stored in `A305/A305404.seq`. Put the seven `.seq` files in a single directory and run `python3 verify.py --oeis-dir /path/to/entries`. The [verification record](verification.txt) includes the axiom reports and the results.
