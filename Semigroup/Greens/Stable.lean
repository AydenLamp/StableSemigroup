/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Semigroup.Greens.Basic

/-!
# Stable Semigroups

This file defines stable semigroups and proves basic properties about them.

## Main Definitions
* `Semigroup.Stable` - A semigroup is stable if it satisfies the following two properties:
  * If `x ≤𝓡 y` and `x 𝓙 y`, then `x 𝓡 y` (`Semigroup.REquiv.of_rPreorder_of_jEquiv`).
  * If `x ≤𝓛 y` and `x 𝓙 y`, then `x 𝓛 y` (`Semigroup.LEquiv.of_lPreorder_of_jEquiv`).

## Main Theorems
* `Semigroup.dEquiv_iff_jEquiv` - In stable semigroups, the 𝓓-relation equals the 𝓙-relation.
* `Semigroup.HEquiv.of_eq_sandwich` - In stable semigroups, an element sandwiched between two
 factors is 𝓗-related to its left and right partial products.
-/

public section

namespace Semigroup

/-- A semigroup is *stable* if 𝓙-equivalence upgrades the 𝓡- and 𝓛-preorders to
equivalences. Finite semigroups are stable (`Semigroup.stable_of_finite`). -/
class Stable (S : Type*) [Semigroup S] where
  /-- `x ≤𝓡 y` and `x 𝓙 y` imply `x 𝓡 y`. -/
  rEquiv_of_rPreorder_of_jEquiv {x y : S} (hr : x ≤𝓡 y) (hj : x 𝓙 y) : x 𝓡 y
  /-- `x ≤𝓛 y` and `x 𝓙 y` imply `x 𝓛 y`. -/
  lEquiv_of_lPreorder_of_jEquiv {x y : S} (hl : x ≤𝓛 y) (hj : x 𝓙 y) : x 𝓛 y

variable {S : Type*} [Semigroup S] [Stable S] {x y u v : S}

/-- In stable semigroups, `x ≤𝓡 y` and `x 𝓙 y` imply `x 𝓡 y`. -/
@[grind →] lemma REquiv.of_rPreorder_of_jEquiv (hr : x ≤𝓡 y) (hj : x 𝓙 y) : x 𝓡 y :=
  Stable.rEquiv_of_rPreorder_of_jEquiv hr hj

/-- In stable semigroups, `x ≤𝓛 y` and `x 𝓙 y` imply `x 𝓛 y`. -/
@[grind →] lemma LEquiv.of_lPreorder_of_jEquiv (hl : x ≤𝓛 y) (hj : x 𝓙 y) : x 𝓛 y :=
  Stable.lEquiv_of_lPreorder_of_jEquiv hl hj

/-- In stable semigroups, 𝓙-equivalent elements are 𝓓-equivalent. -/
lemma JEquiv.to_dEquiv (hj : x 𝓙 y) : x 𝓓 y := by
  obtain ⟨⟨u, v, huv⟩, -⟩ := id hj
  cases v with
  | one =>
    have hl : x ≤𝓛 y := ⟨u, by simpa using huv⟩
    exact (LEquiv.of_lPreorder_of_jEquiv hl hj).to_dEquiv
  | coe a =>
    -- Write `x = u * (y * a)`. The pivot `w := y * a` satisfies `y 𝓡 w` and `w 𝓛 x`.
    have hxw : x ≤𝓛 y * a := ⟨u, by rw [WithOne.coe_mul, ← mul_assoc, huv]⟩
    have hwy : y * a 𝓙 y :=
      ⟨RPreorder.mul_right_self.to_jPreorder, hj.ge.trans hxw.to_jPreorder⟩
    have hr : y * a 𝓡 y := REquiv.of_rPreorder_of_jEquiv RPreorder.mul_right_self hwy
    have hl : x 𝓛 y * a := LEquiv.of_lPreorder_of_jEquiv hxw (hj.trans hwy.symm)
    exact DEquiv.symm ⟨y * a, hr.symm, hl.symm⟩

/-- In stable semigroups, the 𝓓-relation equals the 𝓙-relation. -/
@[grind =] theorem dEquiv_iff_jEquiv : x 𝓓 y ↔ x 𝓙 y := ⟨DEquiv.to_jEquiv, JEquiv.to_dEquiv⟩

/-- Sandwich property. In stable semigroups, an element sandwiched between two factors is 𝓗-related
to its left and right partial products. -/
theorem HEquiv.of_eq_sandwich (h : u * x * v = x) : x 𝓗 u * x ∧ x 𝓗 x * v := by
  -- `x = (u * x) * v` and `x = u * (x * v)` give the two nontrivial inequalities.
  have hr : x ≤𝓡 u * x := ⟨v, by rw [← WithOne.coe_mul, h]⟩
  have hl : x ≤𝓛 x * v := ⟨u, by rw [← WithOne.coe_mul, ← mul_assoc, h]⟩
  have hj₁ : x 𝓙 u * x := ⟨hr.to_jPreorder, LPreorder.mul_left_self.to_jPreorder⟩
  have hj₂ : x 𝓙 x * v := ⟨hl.to_jPreorder, RPreorder.mul_right_self.to_jPreorder⟩
  rw [HEquiv.iff_rEquiv_and_lEquiv, HEquiv.iff_rEquiv_and_lEquiv]
  exact ⟨⟨REquiv.of_rPreorder_of_jEquiv hr hj₁,
      (LEquiv.of_lPreorder_of_jEquiv LPreorder.mul_left_self hj₁.symm).symm⟩,
    ⟨(REquiv.of_rPreorder_of_jEquiv RPreorder.mul_right_self hj₂.symm).symm,
      LEquiv.of_lPreorder_of_jEquiv hl hj₂⟩⟩

end Semigroup
