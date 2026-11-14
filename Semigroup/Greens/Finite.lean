/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

import Mathlib.Data.Fintype.Option
import Semigroup.Greens.Basic
import Semigroup.SemigroupIdempotentPow
import Semigroup.Greens.Stable

/-!
# Finite Semigroups and Green's Relations

This file proves theorems about Green's relations in finite semigroups.

## Main theorems
* `Semigroup.stable_of_finite` - Finite semigroups are stable.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] [Finite S] {x y : S}

/-! ### The D-J Theorem for Finite Semigroups -/

/-- If `α` is finite, then `WithOne α` is also finite. -/
instance _root_.WithOne.finite {α : Type*} [Finite α] : Finite (WithOne α) :=
  inferInstanceAs (Finite (Option α))

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
  simp only [REquiv.mul_right_iff]
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
  simp only [LEquiv.mul_left_iff]
  use (u * ↑y) ^ (n - 1) * u
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc _ u, ← _root_.pow_succ]
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, 𝓙-equivalence strengthens the 𝓡-preorder to 𝓡-equivalence. -/
theorem REquiv.of_rPreorder_and_jEquiv (hr : x ≤𝓡 y) (hj : x 𝓙 y) : x 𝓡 y := by
  obtain rfl | ⟨z, rfl⟩ := hr.eq_or_exists_mul
  · rfl
  · exact (REquiv.of_jEquiv_mul_right hj.symm).symm

/-- In finite semigroups, 𝓙-equivalence strengthens the 𝓛-preorder to 𝓛-equivalence. -/
theorem LEquiv.of_lPreorder_and_jEquiv (hl : x ≤𝓛 y) (hj : x 𝓙 y) : x 𝓛 y := by
  obtain rfl | ⟨z, rfl⟩ := hl.eq_or_exists_mul
  · rfl
  · exact (LEquiv.of_jEquiv_mul_left hj.symm).symm

/-! ### Stability -/

/-- Finite Semigroups are Stable -/
instance stable_of_finite : Stable S where
  rEquiv_of_rPreorder_and_jEquiv hj hr := REquiv.of_rPreorder_and_jEquiv hr hj
  lEquiv_of_lPreorder_and_jEquiv hj hl := LEquiv.of_lPreorder_and_jEquiv hl hj

end Semigroup
