/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

import Mathlib.Data.Fintype.Option
import Semigroup.Greens.Basic
import Semigroup.SemigroupIdempotentPow
import Semigroup.Stable

/-!
# Finite Semigroups and Green's Relations

This file proves theorems about Green's relations in finite semigroups.

## Main theorems
* `Semigroup.stable_of_finite` - Finite semigroups are stable.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] [Finite S] [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)]
  {x y u v : S}

/-! ### The D-J Theorem for Finite Semigroups -/

/-- If `S` is finite, then `WithOne S` is also finite. -/
instance _root_.WithOne.finite : Finite (WithOne S) := inferInstanceAs (Finite (Option S))


/-!
### Properties relating 𝓙, 𝓛, and 𝓡
This section shows how 𝓙-equivalence "strengthens"
𝓡 and 𝓛 preorders to equivalences in finite semigroups.
-/

/-- In finite semigroups, 𝓙-equivalence with a right product gives 𝓡-equivalence. -/
lemma REquiv.of_jEquiv_mul_right (hj : x 𝓙 x * y) : x 𝓡 x * y := by
  obtain ⟨⟨u, v, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc, mul_assoc] at hxy
  obtain ⟨_, n, _, hneq, _, ha ⟩ := Monoid.exists_pow_sandwich_eq_self hxy
  simp only [REquiv, RPreorder.mul_right_self, and_true]
  use v * (↑y * v) ^ (n - 1)
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑x ↑y v]
  rw [mul_assoc ↑x (↑y * v), ← pow_succ']
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, 𝓙-equivalence with a left product gives 𝓛-equivalence. -/
lemma LEquiv.of_jEquiv_mul_left (hj : x 𝓙 y * x) : x 𝓛 y * x := by
  obtain ⟨⟨u, v, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc] at hxy
  obtain ⟨n, _, hneq, _, ha, _⟩ := Monoid.exists_pow_sandwich_eq_self hxy
  simp only [LEquiv, LPreorder.mul_left_self, and_true]
  use (u * ↑y) ^ (n - 1) * u
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc _ u, ← _root_.pow_succ]
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, 𝓙-equivalence strengthens the 𝓡-preorder to 𝓡-equivalence. -/
theorem REquiv.of_rPreorder_and_jEquiv (hr : x ≤𝓡 y) (hj : x 𝓙 y) : x 𝓡 y := by
  obtain ⟨z, hz⟩ := hr
  cases z with
  | one =>
    have heq : x = y := by simp_all
    subst x; simp
  | coe z =>
    have heq : y * z = x := by
      rw [← WithOne.coe_inj, WithOne.coe_mul]
      exact hz
    subst x
    exact (REquiv.of_jEquiv_mul_right hj.symm).symm

/-- In finite semigroups, 𝓙-equivalence strengthens the 𝓛-preorder to 𝓛-equivalence. -/
theorem LEquiv.of_lPreorder_and_jEquiv (hl : x ≤𝓛 y) (hj : x 𝓙 y) : x 𝓛 y := by
  obtain ⟨z, hz⟩ := hl
  cases z with
  | one =>
    have heq : x = y := by simp_all
    subst x; simp
  | coe z =>
    have heq : z * y = x := by
      rwa [← WithOne.coe_inj, WithOne.coe_mul]
    subst x
    exact (LEquiv.of_jEquiv_mul_left hj.symm).symm

/-! ### Stability -/

/-- Finite Semigroups are Stable -/
instance stable_of_finite : Stable S where
  rEquiv_of_rPreorder_and_jEquiv := by
    intros x y hj hr
    exact REquiv.of_rPreorder_and_jEquiv hr hj
  lEquiv_of_lPreorder_and_jEquiv := by
    intros x y hj hl
    exact LEquiv.of_lPreorder_and_jEquiv hl hj

-- Remove these
theorem dEquiv_iff_jEquiv_ : x 𝓓 y ↔ x 𝓙 y := dEquiv_iff_jEquiv
theorem HEquiv.of_eq_sandwich' (h : u * x * v = x) : x 𝓗 u * x ∧ x 𝓗 x * v :=
  HEquiv.of_eq_sandwich h

end Semigroup
