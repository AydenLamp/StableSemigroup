/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Semigroup.Greens.Stable
public import Semigroup.Greens.GreensLemma

/-!
# The Location Theorem

This file proves the Location Theorem, which states that the following
conditions are equivalent for `x y : S` where `S` is a semigroup:
  1. `x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
  2. `⟦y⟧𝓡 ∩ ⟦x⟧𝓛` contains an idempotent element.

If the semigroup is stable, these conditions are equivalent to
  3. `x * y 𝓓 x` (Alternatively, `x * y 𝓓 y`) and `x 𝓓 y`

## Main Theorems

* `DEquiv.mul_mem_inter_iff` - For `x y : S` where `S` is a stable semigroup, `x * y` is in
`⟦x⟧𝓡 ∩ ⟦y⟧𝓛` iff `x 𝓓 y` and `x * y 𝓓 x`.
* `mul_mem_inter_iff_exists_isIdempotentElem` - For `x y : S`, `x * y` is in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
iff there exists an idempotent element in `⟦y⟧𝓡 ∩ ⟦x⟧𝓛`.
* `HEquiv.exists_isIdempotentElem_of_mul` - An 𝓗-class containing `x, y` with `x * y 𝓗 x`
contains an idempotent.
* `DEquiv.exists_isIdempotentElem_mem_rClass`, `DEquiv.exists_isIdempotentElem_mem_lClass` -
A 𝓓-class containing an idempotent has an idempotent in each of its 𝓡- and 𝓛-classes.
-/

public section

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- In stable semigroups, `x * y` is in the intersection of the 𝓡-class of `x` and the 𝓛-class
of `y` iff `x`, `y`, and `x * y` are 𝓓-equivalent. -/
theorem DEquiv.mul_mem_inter_iff (x y : S) [IsStable S] :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ x 𝓓 y ∧ x * y 𝓓 x := by
  simp only [Set.mem_inter_iff, REquiv.mem_set, LEquiv.mem_set]
  constructor
  · rintro ⟨hr, hl⟩
    exact ⟨⟨x * y, hr.symm, hl⟩, hr.to_dEquiv⟩
  · rintro ⟨hd, hd'⟩
    have hj := hd'.to_jEquiv
    exact ⟨REquiv.of_rPreorder_of_jEquiv RPreorder.mul_right_self hj,
      LEquiv.of_lPreorder_of_jEquiv LPreorder.mul_left_self (hj.trans hd.to_jEquiv)⟩

/-- `x * y` is 𝓡-equivalent to `x` and 𝓛-equivalent to `y` iff there exists an idempotent
element in the intersection of the 𝓡-class of `y` and the 𝓛-class of `x`. -/
theorem mul_mem_inter_iff_exists_isIdempotentElem (x y : S) :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
  simp only [Set.mem_inter_iff, REquiv.mem_set, LEquiv.mem_set]
  constructor
  · rintro ⟨hr, hl⟩
    -- Green's lemma: `w ↦ w * y` maps `⟦x⟧𝓛` onto `⟦x * y⟧𝓛 ∋ y`; `e` is a preimage of `y`.
    obtain ⟨e, he, hey⟩ := hr.symm.surjOn_lClass rfl hl.symm
    replace hey : e * y = y := hey
    have heR : e 𝓡 y := by
      rw [← hey]; exact hr.symm.rEquiv_mul_right_of_lEquiv rfl he
    refine ⟨e, ?_, heR, he⟩
    obtain rfl | ⟨u, rfl⟩ := heR.le.eq_or_exists_mul
    · exact hey
    · change y * u * (y * u) = y * u
      rw [← mul_assoc, hey]
  · rintro ⟨e, he, hr, hl⟩
    have he₁ : e * y = y := by grind
    have he₂ : x * e = x := by grind
    have h₁ := hr.symm.lmul_compat x
    have h₂ := hl.symm.rmul_compat y
    rw [he₂] at h₁
    rw [he₁] at h₂
    exact ⟨h₁, h₂⟩

/-- If `x 𝓗 y` and `x * y 𝓗 x`, then the 𝓗-class of `x` contains an idempotent. -/
theorem HEquiv.exists_isIdempotentElem_of_mul {x y : S} (h₁ : x 𝓗 y) (h₂ : x * y 𝓗 x) :
    ∃ e, e 𝓗 x ∧ IsIdempotentElem e := by
  obtain ⟨e, he, heR, heL⟩ := (mul_mem_inter_iff_exists_isIdempotentElem x y).1
    ⟨h₂.to_rEquiv, (h₂.trans h₁).to_lEquiv⟩
  exact ⟨e, (iff_rEquiv_and_lEquiv _ _).2 ⟨REquiv.trans heR h₁.to_rEquiv.symm, heL⟩, he⟩

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓡-class. -/
theorem DEquiv.exists_isIdempotentElem_mem_rClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
    ∃ f ∈ ⟦x⟧𝓡, IsIdempotentElem f := by
  obtain ⟨r, hr₁, hr₂⟩ := hx
  have her : r * e = r := by grind
  obtain rfl | ⟨u, hu⟩ := hr₂.ge.eq_or_exists_mul
  · exact ⟨_, hr₁.symm, he⟩
  -- `u * r = e`, so `r * u` is idempotent and `r * u 𝓡 r` (witness `r`).
  refine ⟨r * u, REquiv.trans (REquiv.mul_right_iff'.2 ⟨r, ?_⟩) hr₁.symm, ?_⟩
  · rw [← WithOne.coe_mul, mul_assoc, hu, her]
  · change r * u * (r * u) = r * u
    rw [← mul_assoc, mul_assoc r u r, hu, her]

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓛-class. -/
theorem DEquiv.exists_isIdempotentElem_mem_lClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
    ∃ f ∈ ⟦x⟧𝓛, IsIdempotentElem f := by
  obtain ⟨r, hr₁, hr₂⟩ := hx.symm
  have her : e * r = r := by grind
  obtain rfl | ⟨u, hu⟩ := hr₁.le.eq_or_exists_mul
  · exact ⟨_, hr₂, he⟩
  -- `r * u = e`, so `u * r` is idempotent and `u * r 𝓛 r` (witness `r`).
  refine ⟨u * r, LEquiv.trans (LEquiv.mul_left_iff'.2 ⟨r, ?_⟩) hr₂, ?_⟩
  · rw [← WithOne.coe_mul, ← mul_assoc, hu, her]
  · change u * r * (u * r) = u * r
    rw [← mul_assoc, mul_assoc u r u, hu, mul_assoc, her]

end Semigroup
