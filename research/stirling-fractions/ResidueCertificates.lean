/-! Exact polynomial certificates. Each computed column is a coefficient after b=1+2z. -/
namespace ResidueCertificates
def fact : Nat → Nat | 0 => 1 | n+1 => (n+1)*fact n
def choose (n k : Nat) : Nat := if k ≤ n then fact n / (fact k*fact (n-k)) else 0
private def signedColumn (m k n d : Nat) : Nat :=
  (List.range (k+1)).foldl (fun z j =>
    let diff := ((j^(n+d))%m + m - (j^n)%m)%m
    let x := choose k j * diff %m
    (z + (if (k-j)%2==0 then x else m-x))%m) 0
def differenceCoeffs (m K n d : Nat) : List Nat :=
  let terms := (List.range K).map fun k => choose (2*k) k * signedColumn m k n d %m
  (List.range K).map fun h => (terms.zipIdx.foldl (fun acc wk =>
    (acc + wk.1 * choose wk.2 h * 2^h)%m) 0)
def windowCert (s V K : Nat) (first : List Nat) : Bool :=
  let m := 2^(V+1)
  fact K%m==0 && first.length==K &&
    (first.zipIdx.all (fun wi =>
      differenceCoeffs m K (V+1+wi.2) (2^s) == wi.1 :: List.replicate (K-1) 0))
set_option maxRecDepth 12000
set_option maxHeartbeats 6000000
theorem odd_b_shift_one : windowCert 0 3 6 [8,8,8,8,8,8] := by decide +kernel
theorem odd_b_shift_two : windowCert 1 6 8 [64,0,64,0,64,0,64,0] := by decide +kernel
theorem odd_b_shift_four : windowCert 2 7 10 [0,128,0,128,0,128,0,128,0,128] := by decide +kernel
theorem odd_b_shift_eight : windowCert 3 8 12 [256,0,256,0,256,0,256,0,256,0,256,0] := by decide +kernel
private def stirling : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 0
  | n+1, k+1 => (k+1)*stirling n (k+1) + stirling n k
private def df : Nat → Nat | 0 => 1 | k+1 => (2*k+1)*df k
def scalar (c n : Nat) : Nat :=
  (List.range (n+1)).foldl (fun a k => a + stirling n k * c^k * df k) 0
theorem odd_c_small : [1,3,5,7].all (fun c =>
    scalar c 0 == 1 && scalar c 1%2==1 && scalar c 2%2==0 &&
    scalar c 6%4==3 && scalar c 12%8==5) := by decide +kernel
#print axioms odd_b_shift_one
#print axioms odd_b_shift_two
#print axioms odd_b_shift_four
#print axioms odd_b_shift_eight
#print axioms odd_c_small
end ResidueCertificates
