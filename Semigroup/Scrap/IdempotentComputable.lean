import Mathlib
import Semigroup.SemigroupIdempotentPow

open Semigroup

/-!
We make the `idempotentPow` function computable by using `Nat.find`,
but this does not give us any explicit numbers.
-/

section find

variable {S : Type*} [Finite S] [Semigroup S] [Pow S ℕ+] [PNatPowAssoc S]

/-- Existence phrased over `ℕ` so we can hand it to `Nat.find`. -/
private theorem exists_idem_succ (x : S) :
    ∃ n : ℕ, IsIdempotentElem (x ^ n.succPNat) := by
  obtain ⟨m, hm⟩ := exists_idempotent_ppow x
  exact ⟨m.natPred, by rwa [PNat.succPNat_natPred]⟩

variable [DecidableEq S]

instance decidable_idempotent_elem (x : S) : Decidable (IsIdempotentElem x) := by
  unfold IsIdempotentElem
  infer_instance

/-- The least positive `n` with `x ^ n` idempotent. Computable. -/
def idempotentPow (x : S) : ℕ+ := (Nat.find (exists_idem_succ x)).succPNat

theorem idempotentPow_spec (x : S) : IsIdempotentElem (x ^ idempotentPow x) :=
  Nat.find_spec (exists_idem_succ x)

end find


section scrap

lemma n_lt_2nm (n m : ℕ+) : n ≤ 2 * n * m := by
  induction m with
  | one => pnat_to_nat; omega
  | succ m ih => pnat_to_nat; ring_nf; omega

variable {S : Type*} [Finite S] [DecidableEq S] [Semigroup S] [Pow S ℕ+] [PNatPowAssoc S]

/-- The first `m` such that `x ^ n = x ^ (n + m)` -/
def findRepeat (x : S) (n : ℕ+) (m : ℕ+) : ℕ+ :=
  if x ^ n = x ^ (n + m) then m else findRepeat x n (m + 1)

lemma findRepeat_spec (x : S) (n : ℕ+) : x ^ n = x ^ (n + findRepeat x n 1) := by
  sorry

/-- A repeated element in a sequence of powers -/
def endOfTail (x : S) : ℕ+ :=
  findRepeat x 1 1

/-- The length of the cycle in the sequence of powers of `x` -/
def loopSize (x : S) : ℕ+ :=
  findRepeat x (endOfTail x) 1 - endOfTail x

/-- every `n` greater than or equal to `endOfTail x` repeats every `loopSize x` powers -/
lemma ge_endOfTail_repeats (x : S) (n : ℕ+) (l : ℕ+) (h_ge : endOfTail x ≤ n) :
    x ^ n = x ^ (n + l * loopSize x) := by
  induction l with
  | one =>
     simp
     sorry
  | succ l ih => sorry

/-- Given an element in a finite semigroup, the smallest idempotent power of that element. -/
def idempotentPow' (x : S) : ℕ+ :=
  2 * (endOfTail x) * (loopSize x)

/-- `idempotentPow x` is idempotent -/
theorem idempotentPow'_spec (x : S) : IsIdempotentElem (x ^ idempotentPow' x) := by
  unfold IsIdempotentElem
  rw [← ppow_add]
  symm
  exact ge_endOfTail_repeats x (idempotentPow' x) (2 * endOfTail x) (by
    apply n_lt_2nm (endOfTail x) (loopSize x))

end scrap
