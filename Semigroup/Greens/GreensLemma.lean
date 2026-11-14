/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Mathlib.Data.Set.Function
public import Semigroup.Greens.Basic

/-!
# Green's Lemma

This file proves Green's lemma for 𝓡 and 𝓛.

## Main Theorems

Let `x 𝓡 y` such that `y * u = x` and `x * v = y`.
* `REquiv.invOn_lClass` - the map `x ↦ x * u` is the inverse of `x ↦ x * v` on the 𝓛-class of `x`.
* `REquiv.bijOn_lClass` - the map `x ↦ x * v` is a bijection from the
𝓛-class of `x` to the 𝓛-class of `y`.
* `REquiv.hEquiv_mul_right_iff` - this bijection preserves 𝓗 classes.

Let `x 𝓛 y` such that `u * y = x` and `v * x = y`.
* `LEquiv.invOn_rClass` - the map `x ↦ u * x` is the inverse of `x ↦ v * x` on the 𝓡-class of `x`.
* `LEquiv.bijOn_rClass` - the map `x ↦ v * x` is a bijection from the
𝓡-class of `x` to the 𝓡-class of `y`.

## Implementation notes

All set-theoretic statements (`InjOn`, `SurjOn`, `BijOn`) are derived from the
inverse-pair statements `invOn_*` using Mathlib's `Set.InvOn` API, so the only
semigroup computation is in `translation_id`.
-/

public section

namespace Semigroup

variable {S : Type*} [Semigroup S] {x y u v w : S}

/-! ### Right translations on 𝓛-classes -/

/-- If `x 𝓡 y` such that `x * v = y` and `y * u = x`, then right translation by `v * u` on any
element 𝓛-equivalent to `x` is the identity. -/
private lemma REquiv.translation_id (hv : x * v = y) (hu : y * u = x) (hw : w 𝓛 x) :
    w * v * u = w := by
  obtain rfl | ⟨z, rfl⟩ := hw.le.eq_or_exists_mul
  · rw [hv, hu]
  · rw [mul_assoc z, hv, mul_assoc, hu]

/-- If `x 𝓡 y` and `x * v = y`, then some `u : S` translates back: `y * u = x`.
(When `x = y` the identity witness is unavailable in `S`, but `u := v` works.) -/
lemma REquiv.exists_inverse_translation (hr : x 𝓡 y) (hv : x * v = y) : ∃ u, y * u = x := by
  obtain rfl | ⟨u, hu⟩ := hr.le.eq_or_exists_mul
  exacts [⟨v, hv⟩, ⟨u, hu⟩]

/-- If `x * v = y`, then the map `w ↦ w * v` maps the 𝓛-class of `x` to that of `y` -/
lemma RPreorder.mapsTo_lClass (hv : x * v = y) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  intro z hz
  rw [← hv]
  exact LEquiv.rmul_compat hz v

/-- If `x * v = y` and `y * u = x`, then the map `w ↦ w * u` is the inverse of
`w ↦ w * v` when restricted to the 𝓛-classes of `x` and `y` -/
theorem REquiv.invOn_lClass (hv : x * v = y) (hu : y * u = x) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 :=
  ⟨fun _ hz ↦ translation_id hv hu hz, fun _ hz ↦ translation_id hu hv hz⟩

/-- If `x 𝓡 y` such that `x * v = y` then the map `w ↦ w * v` is injective on the 𝓛-class of `x`. -/
lemma REquiv.injOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓛 := by
  obtain ⟨u, hu⟩ := hr.exists_inverse_translation hv
  exact (invOn_lClass hv hu).1.injOn

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is surjective
from the 𝓛-class of `x` to that of `y`. -/
lemma REquiv.surjOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  obtain ⟨u, hu⟩ := hr.exists_inverse_translation hv
  exact (invOn_lClass hv hu).2.surjOn (RPreorder.mapsTo_lClass hu)

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is a bijection from
the 𝓛-class of `x` to that of `y`. -/
theorem REquiv.bijOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 :=
  Set.BijOn.mk (RPreorder.mapsTo_lClass hv) (hr.injOn_lClass hv) (hr.surjOn_lClass hv)

theorem REquiv.exists_bijOn_lClass (hr : x 𝓡 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  obtain rfl | ⟨v, hv⟩ := hr.ge.eq_or_exists_mul
  exacts [⟨id, Set.bijOn_id _⟩, ⟨_, hr.bijOn_lClass hv⟩]

/-- If `x 𝓡 y` such that `x * v = y`, then for all `z 𝓛 x`, `z 𝓡 z * v`. -/
lemma REquiv.rEquiv_mul_right_of_lEquiv (hr : x 𝓡 y) (hv : x * v = y) {z : S} (hz : z 𝓛 x) :
    z 𝓡 z * v := by
  obtain ⟨u, hu⟩ := hr.exists_inverse_translation hv
  exact ⟨⟨u, by rw [← WithOne.coe_mul, translation_id hv hu hz]⟩, RPreorder.mul_right_self⟩

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` preserves 𝓗-classes. -/
lemma REquiv.hEquiv_mul_right_iff (hr : x 𝓡 y) (hv : x * v = y) {a b : S} (hw : a 𝓛 x)
    (hz : b 𝓛 x) : a 𝓗 b ↔ (fun w ↦ w * v) a 𝓗 (fun w ↦ w * v) b := by
  have ha := hr.rEquiv_mul_right_of_lEquiv hv hw
  have hb := hr.rEquiv_mul_right_of_lEquiv hv hz
  simp only [HEquiv.iff_rEquiv_and_lEquiv]
  exact ⟨fun ⟨hab, _⟩ ↦ ⟨ha.symm.trans (hab.trans hb), (hw.trans hz.symm).rmul_compat v⟩,
    fun ⟨hab, _⟩ ↦ ⟨ha.trans (hab.trans hb.symm), hw.trans hz.symm⟩⟩

/-! ### Right translations on 𝓗-classes -/

lemma REquiv.mapsTo_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  intro z hz
  obtain ⟨hzr, hzl⟩ := (HEquiv.iff_rEquiv_and_lEquiv _ _).1 hz
  refine (HEquiv.iff_rEquiv_and_lEquiv _ _).2 ⟨?_, ?_⟩
  · exact (hr.rEquiv_mul_right_of_lEquiv hv hzl).symm.trans (hzr.trans hr)
  · rw [← hv]
    exact hzl.rmul_compat v

lemma REquiv.invOn_hClass (hv : x * v = y) (hu : y * u = x) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 :=
  ⟨fun _ hz ↦ translation_id hv hu (HEquiv.to_lEquiv hz),
    fun _ hz ↦ translation_id hu hv (HEquiv.to_lEquiv hz)⟩

lemma REquiv.injOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓗 :=
  Set.InjOn.mono (fun _ hz ↦ HEquiv.to_lEquiv hz) (hr.injOn_lClass hv)

lemma REquiv.surjOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  obtain ⟨u, hu⟩ := hr.exists_inverse_translation hv
  exact (invOn_hClass hv hu).2.surjOn (hr.symm.mapsTo_hClass hu)

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is a bijection from
the 𝓗-class of `x` to that of `y`. -/
theorem REquiv.bijOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 :=
  Set.BijOn.mk (hr.mapsTo_hClass hv) (hr.injOn_hClass hv) (hr.surjOn_hClass hv)

theorem REquiv.exists_bijOn_hClass (hr : x 𝓡 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  obtain rfl | ⟨v, hv⟩ := hr.ge.eq_or_exists_mul
  exacts [⟨id, Set.bijOn_id _⟩, ⟨_, hr.bijOn_hClass hv⟩]

/-! ### Dual: left translations on 𝓡-classes -/

/-- If `x 𝓛 y` such that `u * y = x` and `v * x = y`, then left translation by `u * v` on any
element 𝓡-equivalent to `x` is the identity. -/
private lemma LEquiv.translation_id (hv : v * x = y) (hu : u * y = x) (hw : w 𝓡 x) :
    u * v * w = w := by
  obtain rfl | ⟨z, rfl⟩ := hw.le.eq_or_exists_mul
  · rw [mul_assoc, hv, hu]
  · rw [← mul_assoc, mul_assoc u, hv, hu]

/-- If `x 𝓛 y` and `v * x = y`, then some `u : S` translates back: `u * y = x`. -/
lemma LEquiv.exists_inverse_translation (hl : x 𝓛 y) (hv : v * x = y) : ∃ u, u * y = x := by
  obtain rfl | ⟨u, hu⟩ := hl.le.eq_or_exists_mul
  exacts [⟨v, hv⟩, ⟨u, hu⟩]

/-- If `v * x = y`, then the map `w ↦ v * w` maps the 𝓡-class of `x` to that of `y` -/
lemma LPreorder.mapsTo_rClass (hy : v * x = y) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  intro z hz
  rw [← hy]
  exact REquiv.lmul_compat hz v

/-- If `u * y = x` and `v * x = y`, then the map `w ↦ u * w` is the inverse of
`w ↦ v * w` when restricted to the 𝓡-classes of `x` and `y` -/
theorem LEquiv.invOn_rClass (hv : v * x = y) (hu : u * y = x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 :=
  ⟨fun _ hz ↦ (mul_assoc _ _ _).symm.trans (translation_id hv hu hz),
    fun _ hz ↦ (mul_assoc _ _ _).symm.trans (translation_id hu hv hz)⟩

/-- If `x 𝓛 y` such that `v * x = y` then the map `w ↦ v * w` is injective on the 𝓡-class of `x`. -/
lemma LEquiv.injOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓡 := by
  obtain ⟨u, hu⟩ := hl.exists_inverse_translation hv
  exact (invOn_rClass hv hu).1.injOn

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is surjective
from the 𝓡-class of `x` to that of `y`. -/
lemma LEquiv.surjOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  obtain ⟨u, hu⟩ := hl.exists_inverse_translation hv
  exact (invOn_rClass hv hu).2.surjOn (LPreorder.mapsTo_rClass hu)

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is a bijection from
the 𝓡-class of `x` to that of `y`. -/
theorem LEquiv.bijOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 :=
  Set.BijOn.mk (LPreorder.mapsTo_rClass hv) (hl.injOn_rClass hv) (hl.surjOn_rClass hv)

theorem LEquiv.exists_bijOn_rClass (hl : x 𝓛 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  obtain rfl | ⟨v, hv⟩ := hl.ge.eq_or_exists_mul
  exacts [⟨id, Set.bijOn_id _⟩, ⟨_, hl.bijOn_rClass hv⟩]

/-- If `x 𝓛 y` such that `v * x = y`, then for all `z 𝓡 x`, `z 𝓛 v * z`. -/
lemma LEquiv.lEquiv_mul_left_of_rEquiv (hr : x 𝓛 y) (hv : v * x = y) {z : S} (hz : z 𝓡 x) :
    z 𝓛 v * z := by
  obtain ⟨u, hu⟩ := hr.exists_inverse_translation hv
  exact ⟨⟨u, by rw [← WithOne.coe_mul, ← mul_assoc, translation_id hv hu hz]⟩,
    LPreorder.mul_left_self⟩

/-! ### Left translations on 𝓗-classes -/

lemma LEquiv.mapsTo_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  intro z hz
  obtain ⟨hzr, hzl⟩ := (HEquiv.iff_rEquiv_and_lEquiv _ _).1 hz
  refine (HEquiv.iff_rEquiv_and_lEquiv _ _).2 ⟨?_, ?_⟩
  · rw [← hv]
    exact hzr.lmul_compat v
  · exact (hl.lEquiv_mul_left_of_rEquiv hv hzr).symm.trans (hzl.trans hl)

lemma LEquiv.invOn_hClass (hv : v * x = y) (hu : u * y = x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 :=
  ⟨fun _ hz ↦ (mul_assoc _ _ _).symm.trans (translation_id hv hu (HEquiv.to_rEquiv hz)),
    fun _ hz ↦ (mul_assoc _ _ _).symm.trans (translation_id hu hv (HEquiv.to_rEquiv hz))⟩

lemma LEquiv.injOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓗 :=
  Set.InjOn.mono (fun _ hz ↦ HEquiv.to_rEquiv hz) (hl.injOn_rClass hv)

lemma LEquiv.surjOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  obtain ⟨u, hu⟩ := hl.exists_inverse_translation hv
  exact (invOn_hClass hv hu).2.surjOn (hl.symm.mapsTo_hClass hu)

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is a bijection from
the 𝓗-class of `x` to that of `y`. -/
theorem LEquiv.bijOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 :=
  Set.BijOn.mk (hl.mapsTo_hClass hv) (hl.injOn_hClass hv) (hl.surjOn_hClass hv)

theorem LEquiv.exists_bijOn_hClass (hl : x 𝓛 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  obtain rfl | ⟨v, hv⟩ := hl.ge.eq_or_exists_mul
  exacts [⟨id, Set.bijOn_id _⟩, ⟨_, hl.bijOn_hClass hv⟩]

end Semigroup
