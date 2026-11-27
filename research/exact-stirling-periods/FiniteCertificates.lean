/-! Finite certificates for the exceptional primes in OEIS A354242 and A354253.
    Standard Lean only. The weight formula is the binomial expansion of (y-1)^k.
    Each certificate computes the entire window from the defining coefficients. -/
namespace PeriodCertificates

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def binom (n k : Nat) : Nat :=
  if k ≤ n then factorial n / (factorial k * factorial (n-k)) else 0

/-- Coefficient of y^j in the substituted polynomial, reduced modulo m. -/
def weight (b m K j : Nat) : Nat :=
  ((List.range K).foldl (fun acc k =>
    let term := (b^k * binom (2*k) k * binom k j) % m
    let signed := if (k-j)%2 == 0 then term else m-term
    (acc+signed)%m) 0)

/-- A window of K differences a(n+d)-a(n), beginning at n=N. -/
def window (b m K N d : Nat) : List Nat :=
  let terms := (List.range K).map fun j => (j, weight b m K j)
  let value := fun n : Nat => terms.foldl (fun acc jw =>
    (acc + jw.2 * (jw.1^n%m))%m) 0
  (List.range K).map fun i => (value (N+i+d) + m - value (N+i))%m

/-- The window has common divisibility by 2^v and contains a witness modulo 2^(v+1). -/
def twoCheck (b s v K : Nat) : Bool :=
  let half := 2^v
  let m := 2*half
  let values := window b m K (v+1) (2^s)
  factorial K % m == 0 && values.all (fun r => r % half == 0) && values.contains half

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

theorem A354242_dyadic :
    twoCheck 1 0 3 6 && twoCheck 1 1 6 8 && twoCheck 1 2 7 10 && twoCheck 1 3 8 12 := by
  decide +kernel

theorem A354253_dyadic :
    twoCheck 2 0 6 8 && twoCheck 2 1 8 12 && twoCheck 2 2 9 12 &&
    twoCheck 2 3 10 14 && twoCheck 2 4 11 16 && twoCheck 2 5 12 16 := by
  decide +kernel

theorem A354242_mod9 : factorial 6 % 9 = 0 ∧ window 1 9 6 2 3 = [6,3,6,3,6,3] := by
  decide +kernel

theorem A354253_mod243 : factorial 12 % 243 = 0 ∧
    window 2 243 12 5 81 = List.replicate 12 0 := by decide +kernel

theorem A354253_mod729 : factorial 15 % 729 = 0 ∧
    window 2 729 15 6 243 = [486,243,486,243,486,243,486,243,486,243,486,243,486,243,486] := by
  decide +kernel

#print axioms A354242_dyadic
#print axioms A354253_dyadic
#print axioms A354242_mod9
#print axioms A354253_mod243
#print axioms A354253_mod729
end PeriodCertificates
