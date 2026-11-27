module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Four primes between consecutive positive cubes

Theorems `Hilliard.four_le_primeCount_of_bound` and `Hilliard.minimum_of_bound`
deduce the sharp minimum from the Carneiro–Milinovich–Soundararajan interval bound.
The initial certificate covers the indices below 576.
-/

@[expose] public section

set_option maxRecDepth 64000
set_option maxHeartbeats 4000000

namespace Hilliard.Certificate

structure Row where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

/-- Product of the `2^k` consecutive positive integers immediately after `s`. -/
def blockProduct : Nat → Nat → Nat
  | 0, s => s + 1
  | k + 1, s => blockProduct k s * blockProduct k (s + 2 ^ k)

/-- Primality is certified by coprimality with all potential small factors. -/
def rowOK (bound f n : Nat) (r : Row) : Bool :=
  let a := n ^ 3 + r.a
  let b := n ^ 3 + r.b
  let c := n ^ 3 + r.c
  let d := n ^ 3 + r.d
  decide (n ^ 3 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < (n + 1) ^ 3 ∧
    2 ≤ a ∧ d ≤ bound ^ 2 ∧ a.gcd f = 1 ∧ b.gcd f = 1 ∧ c.gcd f = 1 ∧ d.gcd f = 1)

def rowsOK (bound f : Nat) : Nat → List Row → Bool
  | _, [] => true
  | n, r :: rs => rowOK bound f n r && rowsOK bound f (n + 1) rs

def rows4 : List Row := [
  ⟨3, 7, 9, 15⟩, ⟨2, 6, 12, 14⟩, ⟨7, 11, 13, 17⟩, ⟨4, 6, 10, 16⟩,
  ⟨9, 11, 29, 35⟩, ⟨4, 10, 14, 22⟩, ⟨9, 13, 19, 21⟩, ⟨30, 36, 42, 50⟩,
  ⟨5, 13, 19, 25⟩, ⟨6, 10, 16, 24⟩, ⟨5, 9, 23, 33⟩, ⟨14, 16, 32, 38⟩]

theorem check4 : rowsOK (2 ^ 6) (blockProduct 6 0) 4 rows4 = true := by
  decide +kernel

def rows16 : List Row := [
  ⟨3, 15, 31, 33⟩, ⟨6, 18, 20, 24⟩, ⟨7, 11, 17, 19⟩, ⟨4, 10, 12, 24⟩,
  ⟨9, 11, 17, 39⟩, ⟨16, 20, 22, 32⟩, ⟨3, 9, 15, 19⟩, ⟨30, 36, 44, 60⟩,
  ⟨5, 7, 17, 35⟩, ⟨4, 16, 18, 22⟩, ⟨3, 5, 21, 23⟩, ⟨4, 14, 16, 26⟩,
  ⟨9, 25, 39, 45⟩, ⟨2, 18, 24, 30⟩, ⟨11, 17, 31, 43⟩, ⟨12, 28, 42, 46⟩,
  ⟨3, 11, 15, 21⟩, ⟨14, 26, 32, 40⟩, ⟨9, 13, 19, 37⟩, ⟨24, 26, 48, 54⟩,
  ⟨7, 23, 25, 31⟩, ⟨18, 30, 54, 70⟩, ⟨5, 9, 35, 45⟩, ⟨14, 22, 32, 38⟩,
  ⟨7, 13, 19, 33⟩, ⟨6, 26, 42, 72⟩, ⟨5, 11, 13, 43⟩, ⟨24, 30, 42, 52⟩,
  ⟨9, 15, 17, 29⟩, ⟨2, 4, 14, 16⟩, ⟨31, 33, 37, 43⟩, ⟨14, 18, 20, 44⟩]

theorem check16 : rowsOK (2 ^ 9) (blockProduct 9 0) 16 rows16 = true := by
  decide +kernel

def rows48 : List Row := [
  ⟨5, 11, 17, 31⟩, ⟨10, 22, 24, 30⟩, ⟨3, 17, 29, 53⟩, ⟨10, 16, 28, 38⟩,
  ⟨3, 9, 19, 21⟩, ⟨14, 36, 44, 50⟩, ⟨13, 19, 25, 49⟩, ⟨18, 24, 28, 34⟩,
  ⟨5, 15, 17, 33⟩, ⟨28, 40, 50, 74⟩, ⟨9, 15, 19, 25⟩, ⟨12, 18, 20, 38⟩,
  ⟨23, 37, 61, 71⟩, ⟨10, 30, 46, 72⟩, ⟨3, 11, 33, 35⟩, ⟨2, 4, 10, 26⟩]

theorem check48 : rowsOK (2 ^ 9) (blockProduct 9 0) 48 rows48 = true := by
  decide +kernel

def rows64 : List Row := [
  ⟨3, 7, 9, 43⟩, ⟨2, 36, 42, 54⟩, ⟨5, 7, 41, 53⟩, ⟨16, 24, 36, 46⟩,
  ⟨9, 21, 35, 59⟩, ⟨2, 4, 10, 34⟩, ⟨19, 37, 51, 61⟩, ⟨2, 56, 66, 72⟩,
  ⟨25, 43, 49, 53⟩, ⟨6, 10, 12, 24⟩, ⟨3, 15, 17, 23⟩, ⟨16, 32, 38, 68⟩,
  ⟨3, 7, 13, 31⟩, ⟨6, 20, 24, 26⟩, ⟨5, 17, 19, 29⟩, ⟨4, 10, 28, 54⟩,
  ⟨9, 11, 21, 47⟩, ⟨16, 40, 56, 80⟩, ⟨13, 19, 39, 55⟩, ⟨2, 12, 14, 24⟩,
  ⟨19, 23, 37, 43⟩, ⟨4, 18, 22, 28⟩, ⟨3, 5, 15, 17⟩, ⟨4, 44, 46, 70⟩,
  ⟨9, 15, 21, 25⟩, ⟨14, 20, 24, 30⟩, ⟨19, 23, 37, 41⟩, ⟨12, 16, 18, 40⟩,
  ⟨5, 9, 11, 21⟩, ⟨10, 14, 26, 52⟩, ⟨3, 7, 13, 33⟩, ⟨32, 36, 44, 56⟩]

theorem check64 : rowsOK (2 ^ 12) (blockProduct 12 0) 64 rows64 = true := by
  decide +kernel

def rows96 : List Row := [
  ⟨7, 53, 55, 67⟩, ⟨54, 90, 100, 124⟩, ⟨9, 15, 17, 29⟩, ⟨4, 14, 52, 92⟩,
  ⟨3, 33, 37, 39⟩, ⟨6, 48, 56, 60⟩, ⟨19, 43, 53, 65⟩, ⟨4, 6, 30, 52⟩,
  ⟨3, 5, 87, 93⟩, ⟨2, 16, 44, 46⟩, ⟨3, 15, 45, 61⟩, ⟨18, 24, 30, 36⟩,
  ⟨25, 31, 37, 47⟩, ⟨4, 22, 28, 40⟩, ⟨23, 39, 41, 51⟩, ⟨16, 56, 80, 82⟩,
  ⟨9, 31, 33, 45⟩, ⟨2, 14, 24, 26⟩, ⟨7, 29, 59, 67⟩, ⟨4, 12, 28, 48⟩,
  ⟨5, 17, 57, 71⟩, ⟨4, 10, 14, 16⟩, ⟨7, 37, 45, 67⟩, ⟨12, 20, 48, 50⟩,
  ⟨17, 19, 43, 61⟩, ⟨46, 52, 72, 96⟩, ⟨11, 23, 33, 35⟩, ⟨2, 10, 26, 56⟩,
  ⟨3, 13, 19, 49⟩, ⟨26, 32, 38, 42⟩, ⟨5, 11, 13, 17⟩, ⟨30, 36, 46, 84⟩]

theorem check96 : rowsOK (2 ^ 12) (blockProduct 12 0) 96 rows96 = true := by
  decide +kernel

def rows128 : List Row := [
  ⟨17, 59, 71, 77⟩, ⟨2, 4, 34, 44⟩, ⟨21, 43, 49, 87⟩, ⟨26, 32, 42, 48⟩,
  ⟨35, 49, 53, 61⟩, ⟨4, 6, 16, 24⟩, ⟨17, 29, 35, 45⟩, ⟨22, 32, 46, 56⟩,
  ⟨21, 61, 67, 73⟩, ⟨56, 68, 74, 96⟩, ⟨5, 11, 17, 31⟩, ⟨10, 30, 34, 48⟩,
  ⟨3, 17, 29, 39⟩, ⟨32, 38, 70, 82⟩, ⟨3, 15, 21, 25⟩, ⟨2, 6, 20, 24⟩,
  ⟨7, 19, 47, 53⟩, ⟨4, 6, 28, 34⟩, ⟨5, 11, 101, 111⟩, ⟨10, 74, 86, 94⟩,
  ⟨9, 15, 19, 25⟩, ⟨24, 78, 108, 128⟩, ⟨7, 17, 19, 37⟩, ⟨12, 28, 36, 40⟩,
  ⟨9, 11, 33, 53⟩, ⟨2, 16, 20, 32⟩, ⟨15, 39, 69, 93⟩, ⟨18, 38, 56, 72⟩,
  ⟨35, 37, 53, 71⟩, ⟨24, 66, 96, 100⟩, ⟨17, 39, 47, 59⟩, ⟨10, 14, 28, 34⟩]

theorem check128 : rowsOK (2 ^ 12) (blockProduct 12 0) 128 rows128 = true := by
  decide +kernel

def rows160 : List Row := [
  ⟨13, 21, 33, 49⟩, ⟨6, 30, 38, 48⟩, ⟨25, 35, 61, 73⟩, ⟨10, 16, 36, 72⟩,
  ⟨3, 5, 9, 17⟩, ⟨32, 46, 68, 86⟩, ⟨3, 31, 97, 111⟩, ⟨30, 74, 84, 90⟩,
  ⟨11, 41, 47, 85⟩, ⟨4, 22, 54, 58⟩, ⟨9, 11, 21, 63⟩, ⟨2, 40, 46, 52⟩,
  ⟨19, 63, 73, 81⟩, ⟨2, 6, 44, 54⟩, ⟨7, 53, 59, 67⟩, ⟨4, 52, 58, 72⟩,
  ⟨3, 15, 17, 23⟩, ⟨40, 106, 124, 134⟩, ⟨7, 21, 45, 61⟩, ⟨18, 30, 54, 74⟩,
  ⟨7, 19, 49, 53⟩, ⟨6, 76, 100, 112⟩, ⟨3, 9, 11, 29⟩, ⟨4, 14, 16, 22⟩,
  ⟨3, 9, 19, 25⟩, ⟨44, 54, 66, 98⟩, ⟨5, 43, 65, 71⟩, ⟨6, 40, 60, 90⟩,
  ⟨9, 45, 81, 89⟩, ⟨2, 22, 38, 44⟩, ⟨3, 9, 31, 33⟩, ⟨26, 32, 66, 78⟩]

theorem check160 : rowsOK (2 ^ 12) (blockProduct 12 0) 160 rows160 = true := by
  decide +kernel

def rows192 : List Row := [
  ⟨5, 13, 19, 23⟩, ⟨24, 40, 46, 66⟩, ⟨5, 17, 39, 47⟩, ⟨4, 14, 28, 34⟩,
  ⟨37, 67, 81, 123⟩, ⟨14, 30, 38, 50⟩, ⟨5, 31, 35, 37⟩, ⟨28, 42, 60, 72⟩,
  ⟨9, 17, 23, 33⟩, ⟨16, 40, 52, 58⟩, ⟨3, 31, 49, 51⟩, ⟨20, 30, 36, 44⟩,
  ⟨65, 79, 113, 143⟩, ⟨12, 24, 36, 52⟩, ⟨23, 45, 51, 95⟩, ⟨4, 16, 28, 38⟩,
  ⟨7, 9, 51, 75⟩, ⟨2, 48, 72, 108⟩, ⟨13, 23, 41, 59⟩, ⟨18, 42, 46, 60⟩,
  ⟨3, 29, 35, 95⟩, ⟨32, 80, 82, 86⟩, ⟨19, 39, 43, 63⟩, ⟨2, 14, 18, 24⟩,
  ⟨25, 55, 67, 77⟩, ⟨10, 18, 36, 46⟩, ⟨9, 11, 15, 35⟩, ⟨2, 14, 32, 50⟩,
  ⟨21, 63, 91, 93⟩, ⟨80, 92, 116, 140⟩, ⟨11, 13, 19, 41⟩, ⟨10, 34, 40, 42⟩]

theorem check192 : rowsOK (2 ^ 12) (blockProduct 12 0) 192 rows192 = true := by
  decide +kernel

def rows224 : List Row := [
  ⟨3, 5, 23, 47⟩, ⟨16, 22, 28, 44⟩, ⟨51, 73, 93, 117⟩, ⟨14, 26, 48, 84⟩,
  ⟨7, 17, 85, 107⟩, ⟨10, 42, 54, 58⟩, ⟨9, 17, 21, 33⟩, ⟨2, 26, 50, 52⟩,
  ⟨9, 19, 25, 33⟩, ⟨12, 54, 72, 110⟩, ⟨59, 77, 89, 119⟩, ⟨4, 52, 54, 72⟩,
  ⟨3, 11, 21, 35⟩, ⟨14, 28, 34, 40⟩, ⟨15, 37, 55, 57⟩, ⟨24, 54, 74, 80⟩,
  ⟨17, 23, 49, 59⟩, ⟨16, 18, 30, 40⟩, ⟨5, 39, 45, 65⟩, ⟨2, 16, 44, 56⟩,
  ⟨9, 37, 55, 75⟩, ⟨2, 12, 18, 32⟩, ⟨7, 25, 31, 43⟩, ⟨10, 16, 28, 66⟩,
  ⟨17, 21, 35, 39⟩, ⟨2, 22, 40, 52⟩, ⟨7, 13, 19, 31⟩, ⟨6, 20, 32, 38⟩,
  ⟨13, 53, 59, 73⟩, ⟨10, 16, 24, 36⟩, ⟨17, 23, 29, 33⟩, ⟨16, 28, 56, 76⟩]

theorem check224 : rowsOK (2 ^ 12) (blockProduct 12 0) 224 rows224 = true := by
  decide +kernel

def rows256 : List Row := [
  ⟨43, 73, 75, 115⟩, ⟨18, 38, 54, 56⟩, ⟨11, 19, 55, 67⟩, ⟨10, 18, 24, 34⟩,
  ⟨17, 21, 29, 33⟩, ⟨32, 46, 50, 52⟩, ⟨21, 25, 33, 49⟩, ⟨2, 24, 54, 60⟩,
  ⟨5, 7, 37, 47⟩, ⟨12, 48, 82, 84⟩, ⟨15, 23, 41, 45⟩, ⟨10, 26, 44, 58⟩,
  ⟨15, 25, 39, 45⟩, ⟨20, 24, 72, 74⟩, ⟨7, 17, 23, 29⟩, ⟨6, 12, 28, 72⟩,
  ⟨11, 35, 39, 59⟩, ⟨10, 20, 34, 40⟩, ⟨15, 19, 37, 79⟩, ⟨26, 42, 54, 68⟩,
  ⟨5, 11, 13, 31⟩, ⟨4, 10, 24, 30⟩, ⟨21, 35, 45, 59⟩, ⟨4, 10, 28, 40⟩,
  ⟨3, 19, 31, 33⟩, ⟨12, 32, 56, 78⟩, ⟨11, 23, 29, 59⟩, ⟨4, 6, 10, 30⟩,
  ⟨3, 9, 29, 35⟩, ⟨28, 58, 62, 86⟩, ⟨3, 31, 45, 73⟩, ⟨20, 24, 50, 60⟩]

theorem check256 : rowsOK (2 ^ 14) (blockProduct 14 0) 256 rows256 = true := by
  decide +kernel

def rows288 : List Row := [
  ⟨61, 65, 79, 85⟩, ⟨4, 18, 24, 40⟩, ⟨3, 9, 11, 17⟩, ⟨2, 10, 32, 38⟩,
  ⟨9, 13, 19, 25⟩, ⟨6, 14, 44, 84⟩, ⟨17, 25, 37, 43⟩, ⟨4, 42, 72, 94⟩,
  ⟨5, 11, 17, 33⟩, ⟨10, 16, 28, 40⟩, ⟨15, 51, 57, 61⟩, ⟨2, 62, 72, 74⟩,
  ⟨11, 13, 23, 41⟩, ⟨10, 30, 52, 58⟩, ⟨3, 9, 33, 39⟩, ⟨22, 110, 122, 140⟩,
  ⟨39, 45, 55, 67⟩, ⟨2, 26, 36, 42⟩, ⟨7, 23, 31, 35⟩, ⟨10, 48, 54, 66⟩,
  ⟨75, 81, 137, 149⟩, ⟨28, 52, 82, 100⟩, ⟨7, 9, 19, 37⟩, ⟨2, 60, 68, 80⟩,
  ⟨49, 71, 89, 95⟩, ⟨6, 24, 34, 46⟩, ⟨23, 33, 47, 69⟩, ⟨22, 32, 34, 46⟩,
  ⟨15, 21, 31, 43⟩, ⟨14, 24, 38, 50⟩, ⟨19, 25, 37, 47⟩, ⟨18, 24, 42, 72⟩]

theorem check288 : rowsOK (2 ^ 14) (blockProduct 14 0) 288 rows288 = true := by
  decide +kernel

def rows320 : List Row := [
  ⟨11, 33, 39, 81⟩, ⟨10, 16, 32, 62⟩, ⟨25, 43, 51, 75⟩, ⟨12, 14, 32, 36⟩,
  ⟨5, 17, 25, 47⟩, ⟨6, 12, 46, 54⟩, ⟨15, 17, 21, 45⟩, ⟨34, 56, 58, 76⟩,
  ⟨9, 21, 31, 39⟩, ⟨18, 20, 24, 32⟩, ⟨47, 59, 71, 89⟩, ⟨16, 28, 36, 52⟩,
  ⟨5, 9, 11, 33⟩, ⟨10, 32, 46, 56⟩, ⟨9, 19, 39, 67⟩, ⟨12, 24, 32, 44⟩,
  ⟨11, 23, 25, 31⟩, ⟨4, 24, 28, 36⟩, ⟨11, 51, 77, 81⟩, ⟨10, 20, 28, 44⟩,
  ⟨37, 39, 81, 93⟩, ⟨2, 42, 56, 68⟩, ⟨23, 31, 55, 83⟩, ⟨4, 12, 22, 60⟩,
  ⟨29, 33, 77, 113⟩, ⟨4, 14, 16, 82⟩, ⟨25, 55, 63, 67⟩, ⟨18, 36, 50, 54⟩,
  ⟨25, 35, 41, 55⟩, ⟨10, 24, 72, 88⟩, ⟨33, 47, 57, 69⟩, ⟨32, 38, 70, 98⟩]

theorem check320 : rowsOK (2 ^ 14) (blockProduct 14 0) 320 rows320 = true := by
  decide +kernel

def rows352 : List Row := [
  ⟨19, 21, 39, 43⟩, ⟨14, 26, 74, 80⟩, ⟨49, 79, 89, 175⟩, ⟨4, 16, 18, 24⟩,
  ⟨17, 41, 45, 47⟩, ⟨4, 10, 16, 100⟩, ⟨25, 45, 61, 79⟩, ⟨14, 24, 30, 44⟩,
  ⟨11, 67, 83, 89⟩, ⟨16, 28, 78, 82⟩, ⟨33, 35, 41, 53⟩, ⟨2, 4, 20, 34⟩,
  ⟨9, 45, 57, 75⟩, ⟨18, 56, 78, 84⟩, ⟨23, 35, 37, 47⟩, ⟨16, 30, 58, 76⟩,
  ⟨11, 21, 39, 57⟩, ⟨2, 10, 80, 98⟩, ⟨3, 19, 49, 79⟩, ⟨20, 30, 50, 92⟩,
  ⟨11, 23, 43, 53⟩, ⟨24, 46, 60, 66⟩, ⟨3, 35, 59, 63⟩, ⟨14, 26, 44, 46⟩,
  ⟨51, 55, 61, 93⟩, ⟨18, 20, 44, 74⟩, ⟨11, 29, 31, 59⟩, ⟨4, 22, 24, 54⟩,
  ⟨11, 87, 93, 99⟩, ⟨28, 62, 68, 70⟩, ⟨25, 33, 79, 105⟩, ⟨12, 20, 42, 72⟩]

theorem check352 : rowsOK (2 ^ 14) (blockProduct 14 0) 352 rows352 = true := by
  decide +kernel

def rows384 : List Row := [
  ⟨49, 55, 65, 79⟩, ⟨18, 36, 58, 102⟩, ⟨5, 47, 53, 63⟩, ⟨16, 28, 46, 50⟩,
  ⟨25, 31, 37, 55⟩, ⟨32, 44, 72, 84⟩, ⟨19, 37, 41, 49⟩, ⟨6, 60, 72, 82⟩,
  ⟨15, 23, 81, 89⟩, ⟨14, 106, 110, 112⟩, ⟨3, 25, 39, 45⟩, ⟨2, 6, 24, 48⟩,
  ⟨25, 71, 85, 107⟩, ⟨16, 18, 28, 48⟩, ⟨11, 51, 59, 81⟩, ⟨20, 22, 44, 52⟩,
  ⟨31, 43, 51, 63⟩, ⟨50, 56, 72, 92⟩, ⟨23, 25, 41, 55⟩, ⟨22, 46, 54, 60⟩,
  ⟨9, 17, 39, 63⟩, ⟨38, 46, 68, 86⟩, ⟨31, 33, 57, 73⟩, ⟨24, 36, 38, 56⟩,
  ⟨19, 29, 47, 59⟩, ⟨12, 24, 28, 30⟩, ⟨3, 11, 53, 57⟩, ⟨16, 28, 32, 52⟩,
  ⟨9, 13, 39, 69⟩, ⟨20, 50, 74, 90⟩, ⟨17, 19, 25, 35⟩, ⟨24, 28, 36, 78⟩]

theorem check384 : rowsOK (2 ^ 14) (blockProduct 14 0) 384 rows384 = true := by
  decide +kernel

def rows416 : List Row := [
  ⟨33, 53, 81, 87⟩, ⟨10, 14, 16, 50⟩, ⟨25, 45, 49, 67⟩, ⟨2, 14, 42, 68⟩,
  ⟨13, 19, 29, 31⟩, ⟨12, 66, 88, 100⟩, ⟨9, 11, 15, 65⟩, ⟨16, 44, 56, 70⟩,
  ⟨7, 33, 57, 63⟩, ⟨2, 6, 48, 62⟩, ⟨7, 31, 83, 103⟩, ⟨10, 16, 18, 36⟩,
  ⟨9, 17, 21, 71⟩, ⟨10, 14, 28, 50⟩, ⟨3, 13, 31, 37⟩, ⟨2, 38, 50, 60⟩,
  ⟨41, 73, 95, 109⟩, ⟨30, 54, 60, 84⟩, ⟨3, 17, 33, 47⟩, ⟨2, 14, 32, 56⟩,
  ⟨33, 43, 45, 61⟩, ⟨26, 48, 56, 80⟩, ⟨5, 7, 35, 59⟩, ⟨18, 24, 28, 90⟩,
  ⟨17, 39, 123, 137⟩, ⟨26, 58, 100, 116⟩, ⟨33, 99, 115, 129⟩, ⟨26, 30, 32, 42⟩,
  ⟨7, 17, 19, 49⟩, ⟨16, 72, 78, 82⟩, ⟨33, 45, 47, 65⟩, ⟨14, 46, 56, 80⟩]

theorem check416 : rowsOK (2 ^ 14) (blockProduct 14 0) 416 rows416 = true := by
  decide +kernel

def rows448 : List Row := [
  ⟨45, 51, 79, 97⟩, ⟨12, 18, 24, 32⟩, ⟨17, 31, 59, 71⟩, ⟨10, 18, 40, 42⟩,
  ⟨9, 11, 15, 23⟩, ⟨10, 20, 32, 52⟩, ⟨3, 13, 19, 33⟩, ⟨32, 66, 72, 74⟩,
  ⟨17, 23, 35, 43⟩, ⟨10, 28, 40, 88⟩, ⟨17, 47, 81, 101⟩, ⟨22, 28, 32, 52⟩,
  ⟨21, 39, 49, 51⟩, ⟨6, 38, 72, 86⟩, ⟨19, 23, 53, 79⟩, ⟨12, 84, 102, 124⟩,
  ⟨9, 15, 33, 57⟩, ⟨58, 68, 74, 104⟩, ⟨3, 25, 75, 93⟩, ⟨38, 68, 98, 104⟩,
  ⟨11, 47, 49, 101⟩, ⟨4, 34, 40, 52⟩, ⟨3, 17, 23, 59⟩, ⟨68, 80, 86, 98⟩,
  ⟨3, 33, 49, 51⟩, ⟨2, 24, 30, 72⟩, ⟨35, 49, 89, 107⟩, ⟨12, 24, 28, 42⟩,
  ⟨11, 15, 23, 45⟩, ⟨10, 28, 100, 128⟩, ⟨31, 37, 57, 81⟩, ⟨14, 20, 30, 44⟩]

theorem check448 : rowsOK (2 ^ 14) (blockProduct 14 0) 448 rows448 = true := by
  decide +kernel

def rows480 : List Row := [
  ⟨29, 37, 49, 59⟩, ⟨40, 76, 112, 118⟩, ⟨9, 21, 23, 35⟩, ⟨2, 16, 40, 74⟩,
  ⟨37, 73, 79, 87⟩, ⟨68, 72, 74, 86⟩, ⟨7, 41, 55, 61⟩, ⟨4, 10, 24, 30⟩,
  ⟨5, 11, 17, 39⟩, ⟨52, 100, 110, 140⟩, ⟨31, 39, 57, 93⟩, ⟨2, 26, 38, 50⟩,
  ⟨11, 25, 29, 43⟩, ⟨10, 76, 82, 132⟩, ⟨5, 17, 29, 35⟩, ⟨2, 4, 28, 34⟩,
  ⟨3, 13, 63, 67⟩, ⟨6, 20, 50, 54⟩, ⟨5, 25, 47, 59⟩, ⟨10, 12, 30, 40⟩,
  ⟨3, 77, 89, 149⟩, ⟨2, 16, 28, 46⟩, ⟨3, 13, 33, 49⟩, ⟨2, 6, 24, 30⟩,
  ⟨17, 25, 47, 55⟩, ⟨16, 22, 42, 52⟩, ⟨21, 57, 93, 95⟩, ⟨4, 16, 38, 46⟩,
  ⟨19, 31, 37, 57⟩, ⟨2, 12, 20, 24⟩, ⟨11, 19, 47, 53⟩, ⟨6, 12, 30, 48⟩]

theorem check480 : rowsOK (2 ^ 14) (blockProduct 14 0) 480 rows480 = true := by
  decide +kernel

def rows512 : List Row := [
  ⟨29, 45, 51, 53⟩, ⟨26, 80, 100, 116⟩, ⟨7, 9, 25, 45⟩, ⟨2, 12, 18, 26⟩,
  ⟨7, 37, 53, 65⟩, ⟨16, 28, 60, 108⟩, ⟨5, 9, 29, 75⟩, ⟨4, 28, 32, 44⟩,
  ⟨21, 31, 57, 73⟩, ⟨18, 26, 42, 48⟩, ⟨49, 53, 59, 65⟩, ⟨6, 10, 34, 52⟩,
  ⟨5, 17, 23, 59⟩, ⟨4, 22, 26, 46⟩, ⟨21, 33, 37, 51⟩, ⟨14, 36, 44, 50⟩,
  ⟨25, 41, 49, 59⟩, ⟨4, 18, 22, 28⟩, ⟨9, 23, 63, 83⟩, ⟨10, 16, 40, 46⟩,
  ⟨39, 43, 55, 69⟩, ⟨2, 12, 42, 44⟩, ⟨47, 115, 119, 127⟩, ⟨4, 12, 16, 24⟩,
  ⟨33, 35, 47, 57⟩, ⟨4, 10, 16, 44⟩, ⟨9, 75, 79, 81⟩, ⟨32, 38, 62, 90⟩,
  ⟨17, 19, 37, 59⟩, ⟨18, 28, 42, 82⟩, ⟨3, 23, 41, 53⟩, ⟨10, 32, 44, 50⟩]

theorem check512 : rowsOK (2 ^ 14) (blockProduct 14 0) 512 rows512 = true := by
  decide +kernel

def rows544 : List Row := [
  ⟨9, 19, 37, 93⟩, ⟨12, 32, 54, 56⟩, ⟨25, 37, 41, 61⟩, ⟨30, 36, 40, 96⟩,
  ⟨11, 29, 35, 71⟩, ⟨2, 10, 32, 52⟩, ⟨21, 63, 67, 151⟩, ⟨26, 30, 56, 62⟩,
  ⟨41, 55, 59, 79⟩, ⟨52, 96, 100, 120⟩, ⟨17, 65, 93, 135⟩, ⟨2, 4, 14, 16⟩,
  ⟨55, 75, 93, 117⟩, ⟨44, 54, 56, 78⟩, ⟨7, 19, 35, 59⟩, ⟨4, 12, 18, 40⟩,
  ⟨9, 29, 33, 39⟩, ⟨2, 40, 50, 56⟩, ⟨79, 85, 93, 123⟩, ⟨44, 56, 84, 110⟩,
  ⟨23, 29, 35, 49⟩, ⟨12, 16, 76, 102⟩, ⟨5, 35, 41, 53⟩, ⟨16, 50, 58, 76⟩,
  ⟨7, 37, 91, 109⟩, ⟨18, 24, 44, 54⟩, ⟨13, 17, 37, 67⟩, ⟨36, 112, 220, 262⟩,
  ⟨9, 23, 53, 75⟩, ⟨20, 34, 52, 56⟩, ⟨15, 19, 39, 45⟩, ⟨2, 24, 42, 86⟩]

theorem check544 : rowsOK (2 ^ 14) (blockProduct 14 0) 544 rows544 = true := by
  decide +kernel

end Hilliard.Certificate

namespace Hilliard

/-- Four prime witnesses in increasing order, strictly between the endpoints. -/
def FourPrimes (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧
    n ^ 3 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < (n + 1) ^ 3

end Hilliard

namespace Hilliard

/-- The closed-interval statement in Carneiro–Milinovich–Soundararajan, Theorem 5. -/
def PrimeIntervalBound : Prop :=
  ∀ x : ℝ, 4 ≤ x → ∃ p : ℕ, p.Prime ∧ x ≤ (p : ℝ) ∧
    (p : ℝ) ≤ x + (22 / 25) * Real.sqrt x * Real.log x

private theorem log_le_sqrt {y : ℝ} (hy : 576 ≤ y) :
    Real.log y ≤ (5 / 18) * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have hu : 24 ≤ Real.sqrt y := by
    calc (24 : ℝ) = Real.sqrt (24 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
         _ ≤ Real.sqrt y := Real.sqrt_le_sqrt (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y / 16 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hy0.le,
    show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hlog
  have ht : (2 : ℝ) ≤ (1 + 7 / 640 : ℝ) ^ 64 := by norm_num
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
  rw [Real.log_pow] at hmono
  have hunit := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 7 / 640 by norm_num)
  linarith

private theorem gap_lt_quarter {u x : ℝ} (hu : 576 ≤ u) (hx : 4 ≤ x)
    (hupper : x ≤ (u + 1) ^ 3) :
    1 + (22 / 25) * Real.sqrt x * Real.log x < ((u + 1) ^ 3 - u ^ 3) / 4 := by
  let y := u + 1
  have hy : 576 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hroot : Real.sqrt x ≤ y * Real.sqrt y := by
    calc Real.sqrt x ≤ Real.sqrt (y ^ 3) := Real.sqrt_le_sqrt hupper
         _ = y * Real.sqrt y := by
           rw [show y ^ 3 = y ^ 2 * y by ring, Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy0]
  have hlog : Real.log x ≤ 3 * ((5 / 18) * Real.sqrt y) := by
    calc Real.log x ≤ Real.log (y ^ 3) := Real.log_le_log (by linarith) hupper
         _ = 3 * Real.log y := by rw [Real.log_pow]; norm_num
         _ ≤ _ := by linarith [log_le_sqrt hy]
  have hprod := mul_le_mul hroot hlog (Real.log_nonneg (by linarith))
    (mul_nonneg hy0 (Real.sqrt_nonneg y))
  have hs := Real.sq_sqrt hy0
  have hsize : 1 + (11 / 15) * y ^ 2 < ((u + 1) ^ 3 - u ^ 3) / 4 := by
    dsimp [y]
    nlinarith [mul_nonneg (show 0 ≤ u - 576 by linarith) (show 0 ≤ u by linarith)]
  calc 1 + (22 / 25) * Real.sqrt x * Real.log x
      ≤ 1 + (22 / 25) * ((y * Real.sqrt y) * (3 * ((5 / 18) * Real.sqrt y))) := by
        rw [mul_assoc (22 / 25) (Real.sqrt x) (Real.log x)]
        exact add_le_add (le_refl (1 : ℝ))
          (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 22 / 25))
    _ = 1 + (11 / 15) * y ^ 2 := by linear_combination (11/15 : ℝ) * y * hs
    _ < _ := hsize

/-- Place one prime in the interior of each quarter of the cube interval. -/
theorem fourPrimes_large (h : PrimeIntervalBound) {n : ℕ} (hn : 576 ≤ n) : FourPrimes n := by
  let u : ℝ := n
  let w : ℝ := ((u + 1) ^ 3 - u ^ 3) / 4
  have hu : 576 ≤ u := by
    change (576 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hw : 1 < w := by dsimp [w]; nlinarith [sq_nonneg u]
  have hbase : 4 ≤ u ^ 3 := by nlinarith [sq_nonneg u, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 576) hu 3]
  have hslot (k : ℝ) (hk0 : 0 ≤ k) (hk3 : k ≤ 3) :
      ∃ p : ℕ, p.Prime ∧ u ^ 3 + k * w < p ∧ (p : ℝ) < u ^ 3 + (k + 1) * w := by
    let x := u ^ 3 + k * w + 1
    have hx : 4 ≤ x := by dsimp [x]; nlinarith [mul_nonneg hk0 (by linarith : 0 ≤ w)]
    have hend : u ^ 3 + 4 * w = (u + 1) ^ 3 := by dsimp [w]; ring
    have hupper : x ≤ (u + 1) ^ 3 := by
      dsimp [x]; nlinarith [mul_nonneg (sub_nonneg.mpr hk3) (by linarith : 0 ≤ w)]
    obtain ⟨p, hp, hl, hr⟩ := h x hx
    have hg : 1 + (22 / 25) * Real.sqrt x * Real.log x < w := gap_lt_quarter hu hx hupper
    refine ⟨p, hp, ?_, ?_⟩
    · dsimp [x] at hl; linarith
    · calc (p : ℝ) ≤ x + (22 / 25) * Real.sqrt x * Real.log x := hr
           _ < u ^ 3 + k * w + w := by dsimp only [x] at *; linarith
           _ = _ := by ring
  obtain ⟨a, ha, ha0, ha1⟩ := hslot 0 (by norm_num) (by norm_num)
  obtain ⟨b, hb, hb1, hb2⟩ := hslot 1 (by norm_num) (by norm_num)
  obtain ⟨c, hc, hc2, hc3⟩ := hslot 2 (by norm_num) (by norm_num)
  obtain ⟨d, hd, hd3, hd4⟩ := hslot 3 (by norm_num) (by norm_num)
  have h0 : (n : ℝ) ^ 3 < a := by change u ^ 3 < a; linarith
  have hab : (a : ℝ) < b := by linarith
  have hbc : (b : ℝ) < c := by linarith
  have hcd : (c : ℝ) < d := by linarith
  have h4 : (d : ℝ) < ((n : ℝ) + 1) ^ 3 := by
    change (d : ℝ) < (u + 1) ^ 3
    dsimp [w] at hd4; linarith
  exact ⟨a, b, c, d, ha, hb, hc, hd, by exact_mod_cast h0, by exact_mod_cast hab,
    by exact_mod_cast hbc, by exact_mod_cast hcd, by exact_mod_cast h4⟩

end Hilliard

namespace Hilliard
open Certificate

/-- Every integer from `s+1` to `s+2^k` divides `blockProduct k s`. -/
private theorem dvd_block (k : ℕ) {s d : ℕ} (hs : s < d) (hd : d ≤ s + 2 ^ k) :
    d ∣ blockProduct k s := by
  induction k generalizing s with
  | zero =>
    simp only [pow_zero] at hd
    have : d = s + 1 := by omega
    simp [blockProduct, this]
  | succ k ih =>
    rw [blockProduct]
    by_cases h : d ≤ s + 2 ^ k
    · exact dvd_mul_of_dvd_left (ih hs h) _
    · apply dvd_mul_of_dvd_right (ih (by omega) ?_) _
      rw [pow_succ] at hd
      omega

/-- A composite has a nontrivial divisor at most its square root. -/
private theorem prime_of_gcd {k p : ℕ} (hp : 2 ≤ p) (hpmax : p ≤ (2 ^ k) ^ 2)
    (hcop : Nat.gcd p (blockProduct k 0) = 1) : p.Prime := by
  refine Nat.prime_def_le_sqrt.mpr ⟨hp, ?_⟩
  intro d hd hs hdp
  have hbound : d ≤ 2 ^ k := by
    have hsq := (Nat.le_sqrt'.mp hs).trans hpmax
    simpa using (Nat.mul_self_le_mul_self_iff.mp (by simpa [pow_two] using hsq))
  have hf := dvd_block k (s := 0) (by omega : 0 < d) (by simpa using hbound)
  have hg := Nat.dvd_gcd hdp hf
  rw [hcop] at hg
  have := Nat.le_of_dvd Nat.zero_lt_one hg
  omega

private theorem row_sound {k n : ℕ} {r : Row}
    (hc : rowOK (2 ^ k) (blockProduct k 0) n r = true) : FourPrimes n := by
  unfold rowOK at hc
  simp only [decide_eq_true_eq] at hc
  obtain ⟨ha, hab, hbc, hcd, hd, ha2, hmax, ga, gb, gc, gd⟩ := hc
  exact ⟨_, _, _, _, prime_of_gcd ha2 (by omega) ga, prime_of_gcd (by omega) (by omega) gb,
    prime_of_gcd (by omega) (by omega) gc, prime_of_gcd (by omega) hmax gd,
    ha, hab, hbc, hcd, hd⟩

private theorem rows_sound {k start : ℕ} {rs : List Row}
    (hc : rowsOK (2 ^ k) (blockProduct k 0) start rs = true) {n : ℕ}
    (hlo : start ≤ n) (hhi : n < start + rs.length) : FourPrimes n := by
  induction rs generalizing start with
  | nil => simp at hhi; omega
  | cons r rs ih =>
    simp only [rowsOK, Bool.and_eq_true] at hc
    simp only [List.length_cons] at hhi
    by_cases he : n = start
    · subst n; exact row_sound hc.1
    · exact ih hc.2 (by omega) (by omega)

/-- The 575 small intervals are certified independently of any prime-gap estimate. -/
theorem fourPrimes_small {n : ℕ} (hn : 1 ≤ n) (hu : n < 576) : FourPrimes n := by
  by_cases h : n < 4
  · have : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases this with h | h | h <;> subst n
    · exact ⟨2, 3, 5, 7, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩
    · exact ⟨11, 13, 17, 19, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩
    · exact ⟨29, 31, 37, 41, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩
  have hlo : 4 ≤ n := by omega
  by_cases hi16 : n < 16
  · exact rows_sound check4 (by omega) (by change n < 16; omega)
  by_cases hi48 : n < 48
  · exact rows_sound check16 (by omega) (by change n < 48; omega)
  by_cases hi64 : n < 64
  · exact rows_sound check48 (by omega) (by change n < 64; omega)
  by_cases hi96 : n < 96
  · exact rows_sound check64 (by omega) (by change n < 96; omega)
  by_cases hi128 : n < 128
  · exact rows_sound check96 (by omega) (by change n < 128; omega)
  by_cases hi160 : n < 160
  · exact rows_sound check128 (by omega) (by change n < 160; omega)
  by_cases hi192 : n < 192
  · exact rows_sound check160 (by omega) (by change n < 192; omega)
  by_cases hi224 : n < 224
  · exact rows_sound check192 (by omega) (by change n < 224; omega)
  by_cases hi256 : n < 256
  · exact rows_sound check224 (by omega) (by change n < 256; omega)
  by_cases hi288 : n < 288
  · exact rows_sound check256 (by omega) (by change n < 288; omega)
  by_cases hi320 : n < 320
  · exact rows_sound check288 (by omega) (by change n < 320; omega)
  by_cases hi352 : n < 352
  · exact rows_sound check320 (by omega) (by change n < 352; omega)
  by_cases hi384 : n < 384
  · exact rows_sound check352 (by omega) (by change n < 384; omega)
  by_cases hi416 : n < 416
  · exact rows_sound check384 (by omega) (by change n < 416; omega)
  by_cases hi448 : n < 448
  · exact rows_sound check416 (by omega) (by change n < 448; omega)
  by_cases hi480 : n < 480
  · exact rows_sound check448 (by omega) (by change n < 480; omega)
  by_cases hi512 : n < 512
  · exact rows_sound check480 (by omega) (by change n < 512; omega)
  by_cases hi544 : n < 544
  · exact rows_sound check512 (by omega) (by change n < 544; omega)
  exact rows_sound check544 (by omega) (by change n < 576; omega)

end Hilliard

namespace Hilliard

/-- The number of primes strictly between `n³` and `(n+1)³`, OEIS A060199. -/
def primeCount (n : ℕ) : ℕ :=
  ((Finset.Ioo (n ^ 3) ((n + 1) ^ 3)).filter Nat.Prime).card

theorem fourPrimes_of_bound (h : PrimeIntervalBound) {n : ℕ} (hn : 1 ≤ n) : FourPrimes n := by
  by_cases hlarge : 576 ≤ n
  · exact fourPrimes_large h hlarge
  · exact fourPrimes_small hn (by omega)

private theorem count_four {n : ℕ} (h : FourPrimes n) : 4 ≤ primeCount n := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, h0, hab, hbc, hcd, h1⟩ := h
  let s : Finset ℕ := {a, b, c, d}
  have hcard : s.card = 4 := by
    simp [s, hab.ne, (hab.trans hbc).ne, ((hab.trans hbc).trans hcd).ne,
      hbc.ne, (hbc.trans hcd).ne, hcd.ne]
  rw [← hcard]
  apply Finset.card_le_card
  intro p hp
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at hp
  simp only [Finset.mem_filter, Finset.mem_Ioo]
  rcases hp with rfl | rfl | rfl | rfl <;> constructor
  all_goals first | assumption | exact ⟨by omega, by omega⟩

/-- Hilliard's four-prime conjecture, with the one analytic input displayed. -/
theorem four_le_primeCount_of_bound (h : PrimeIntervalBound) {n : ℕ} (hn : 1 ≤ n) :
    4 ≤ primeCount n := count_four (fourPrimes_of_bound h hn)

theorem primeCount_one : primeCount 1 = 4 := by decide

/-- The lower bound is attained, so 4 is the exact uniform minimum for positive `n`. -/
theorem minimum_of_bound (h : PrimeIntervalBound) :
    IsLeast (primeCount '' Set.Ici 1) 4 := by
  constructor
  · exact ⟨1, by simp, primeCount_one⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact four_le_primeCount_of_bound h hn


end Hilliard
