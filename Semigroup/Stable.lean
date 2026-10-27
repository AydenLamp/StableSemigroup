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

/-- In stable semigroups, the 𝓓-relation equals the 𝓙-relation. -/
theorem dEquiv_iff_jEquiv [Stable S] : x 𝓓 y ↔ x 𝓙 y := ⟨DEquiv.to_jEquiv, JEquiv.to_dEquiv⟩

end Semigroup
