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

-/

namespace Semigroup

class Stable (S : Type*) [Semigroup S] where
  rEquiv_of_rPreorder_and_jEquiv {x y : S} (hj : x 𝓙 y) (hr : x ≤𝓡 y) : x 𝓡 y
  lEquiv_of_lPreorder_and_jEquiv {x y : S} (hj : x 𝓙 y) (hl : x ≤𝓛 y) : x 𝓛 y

variable {S : Type*} [Semigroup S] {x y : S}

lemma JEquiv.to_dEquiv [Stable S] (hj : x 𝓙 y) : x 𝓓 y := by
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
      exact Stable.rEquiv_of_rPreorder_and_jEquiv hj₂ (by simp)
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











/-- In stable semigroups, `𝓙`-equivalent elements are also `𝓓`-equivalent. -/
lemma JEquiv.to_dEquiv' [Stable S] (hj : x 𝓙 y) : x 𝓓 y := by
  have hjl : x ≤𝓙 y := hj.left
  have hjr : y ≤𝓙 x := hj.right
  obtain ⟨u1,v1,hjluv⟩ := hjl
  obtain ⟨u2,v2,hjruv⟩ := hjr
  unfold DEquiv
  cases v2
  · use x
    constructor
    · exact REquiv.refl x
    · have : y ≤𝓛 x := by
        simp at hjruv
        use u2
      apply LEquiv.symm
      apply Stable.lEquiv_of_lPreorder_and_jEquiv hj.symm this
  · expose_names
    have hylxa : y ≤𝓛 x * a := by
      use u2
      calc
        u2 * ↑( x * a) = u2 * (↑x * ↑a) := by simp
          _ = u2 * ↑x * ↑a := Eq.symm (mul_assoc u2 ↑x ↑a)
          _ = ↑y := hjruv
    use x * a
    constructor
    · have h₁: x * a ≤𝓡 x := RPreorder.mul_right_self
      have h₂ :x * a 𝓙 x := by
        constructor
        · exact RPreorder.to_jPreorder h₁
        · calc
            x ≤𝓙 y := ge (JEquiv.symm hj)
            _ ≤𝓙 x * a := LPreorder.to_jPreorder hylxa
      exact REquiv.symm (Stable.rEquiv_of_rPreorder_and_jEquiv h₂ h₁)
    · have h₁: y ≤𝓛 x * a := hylxa
      have h₂ : y 𝓙 x * a   := by
        constructor
        · exact LPreorder.to_jPreorder hylxa
        · calc
            x * a ≤𝓙 x := by
              apply RPreorder.to_jPreorder
              exact RPreorder.mul_right_self
            _ ≤𝓙 y := ge (JEquiv.symm hj)
      exact LEquiv.symm (Stable.lEquiv_of_lPreorder_and_jEquiv h₂ hylxa)

end Semigroup
