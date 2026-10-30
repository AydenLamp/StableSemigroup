/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

import Mathlib
import Semigroup.Greens.Defs
import Semigroup.Greens.Basic

/-!
# Stable Semigroups

This file defines stable semigroups.

## Main Definitions
* `Semigroup.Stable` - A semigroup is stable if it satisfies the following two properties:
  * If `x 𝓙 y` and `x ≤𝓡 y`, then `x 𝓡 y`.
  * If `x 𝓙 y` and `x ≤𝓛 y`, then `x 𝓛 y`.

## Main Theorems
* `Semigroup.dEquiv_iff_jEquiv` - In stable semigroups, the 𝓓-relation equals the 𝓙-relation.
* `Semigroup.HEquiv.of_eq_sandwich` - In stable semigroups, an element sandwiched between two
 factors is 𝓗-related to its left and right partial products.
-/

namespace Semigroup

class Stable (S : Type*) [Semigroup S] where
  rEquiv_of_rPreorder_and_jEquiv {x y : S} (hj : x 𝓙 y) (hr : x ≤𝓡 y) : x 𝓡 y
  lEquiv_of_lPreorder_and_jEquiv {x y : S} (hj : x 𝓙 y) (hl : x ≤𝓛 y) : x 𝓛 y

variable {S : Type*} [Semigroup S] [Stable S] {x y u v : S}

@[simp] lemma rEquiv_of_rPreorder_and_jEquiv_of_Stable (hj : x 𝓙 y) (hr : x ≤𝓡 y) : x 𝓡 y :=
  Stable.rEquiv_of_rPreorder_and_jEquiv hj hr

@[simp] lemma lEquiv_of_lPreorder_and_jEquiv_of_Stable (hj : x 𝓙 y) (hl : x ≤𝓛 y) : x 𝓛 y :=
  Stable.lEquiv_of_lPreorder_and_jEquiv hj hl

lemma JEquiv.to_dEquiv (hj : x 𝓙 y) : x 𝓓 y := by
  obtain ⟨⟨u, v, huv⟩, _⟩ := by exact hj
  cases v
  · simp only [mul_one] at huv
    use x
    simp only [REquiv.refl, true_and]
    apply Stable.lEquiv_of_lPreorder_and_jEquiv hj
    use u
  · expose_names
    symm
    use y * a
    constructor
    · have hj₂ : y * a 𝓙 y := by
        refine ⟨by simp, ?_⟩
        trans x
        · simp [hj]
        · use u, 1
          simp [huv, ← mul_assoc]
      symm
      simp_all
    · have hj₂ : x 𝓙 y * a := by
        constructor
        · use u, 1
          simp [huv, ← mul_assoc]
        · trans y
          all_goals simp_all
      symm
      apply Stable.lEquiv_of_lPreorder_and_jEquiv hj₂
      use u
      simp [huv, ← mul_assoc]

/-- In stable semigroups, the 𝓓-relation equals the 𝓙-relation. -/
theorem dEquiv_iff_jEquiv : x 𝓓 y ↔ x 𝓙 y := ⟨DEquiv.to_jEquiv, JEquiv.to_dEquiv⟩

/-- Sandwich property. In stable  semigroups, an element sandwiched between two factors is 𝓗-related
to its left and right partial products. -/
theorem HEquiv.of_eq_sandwich (h : u * x * v = x) : x 𝓗 u * x ∧ x 𝓗 x * v := by
  have hj₁ : x 𝓙 u * x := by
    rw [JEquiv]
    refine ⟨RPreorder.to_jPreorder ?_, LPreorder.to_jPreorder ?_⟩
    · use v
      simp_all [← WithOne.coe_mul]
    · simp
  have hj₂ : x 𝓙 x * v := by
    rw [JEquiv]
    refine ⟨LPreorder.to_jPreorder ?_, RPreorder.to_jPreorder ?_⟩
    · use u
      simp_all [← WithOne.coe_mul, ← mul_assoc]
    · simp
  simp only [HEquiv.iff_rEquiv_and_lEquiv ]
  refine ⟨⟨?_ , ?_⟩, ⟨?_ , ?_⟩⟩
  · apply Stable.rEquiv_of_rPreorder_and_jEquiv hj₁
    use v
    simp_all [← WithOne.coe_mul]
  · symm
    apply Stable.lEquiv_of_lPreorder_and_jEquiv hj₁.symm
    simp
  · symm
    apply Stable.rEquiv_of_rPreorder_and_jEquiv hj₂.symm
    simp
  · apply Stable.lEquiv_of_lPreorder_and_jEquiv hj₂
    use u
    simp_all [← WithOne.coe_mul, ← mul_assoc]

end Semigroup
