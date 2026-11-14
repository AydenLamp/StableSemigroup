/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Semigroup.Ideal.Defs
public import Semigroup.Greens.Basic

/-!
# Green's Relations and Ideals

This file characterizes Green's relations in terms of principal ideals.

## Main Results

* `LPreorder.iff_leftIdeal_subset` — principal left ideal inclusion iff `x ≤𝓛 y`.
* `RPreorder.iff_rightIdeal_subset` — principal right ideal inclusion iff `x ≤𝓡 y`.
* `JPreorder.iff_mulTwoSidedIdeal_subset` — principal ideal inclusion iff `x ≤𝓙 y`.
* `LEquiv.iff_leftIdeal_eq` — principal left ideals are equal iff `x 𝓛 y`.
* `REquiv.iff_rightIdeal_eq` — principal right ideals are equal iff `x 𝓡 y`.
* `JEquiv.iff_mulTwoSidedIdeal_eq` — principal ideals are equal iff `x 𝓙 y`.
-/

public section

namespace Semigroup

variable {S : Type*} [Semigroup S] (x y : S)

/-! ### Ideals are down-closed for the corresponding preorder -/

/-- For `x ∈ i : LeftIdeal S`, if `y ≤𝓛 x` then `y ∈ i`. -/
lemma LPreorder.mem_leftIdeal_of_le {x y : S} {i : LeftIdeal S} (hx : x ∈ i) (hy : y ≤𝓛 x) :
    y ∈ i := by
  obtain rfl | ⟨z, rfl⟩ := hy.eq_or_exists_mul
  exacts [hx, i.mem hx]

/-- For `x ∈ i : RightIdeal S`, if `y ≤𝓡 x` then `y ∈ i`. -/
lemma RPreorder.mem_rightIdeal_of_le {x y : S} {i : RightIdeal S} (hx : x ∈ i) (hy : y ≤𝓡 x) :
    y ∈ i := by
  obtain rfl | ⟨z, rfl⟩ := hy.eq_or_exists_mul
  exacts [hx, i.mem hx]

/-- For `x ∈ i : MulTwoSidedIdeal S`, if `y ≤𝓙 x` then `y ∈ i`. -/
lemma JPreorder.mem_mulTwoSidedIdeal_of_le {x y : S} {i : MulTwoSidedIdeal S}
    (hx : x ∈ i) (hy : y ≤𝓙 x) : y ∈ i := by
  obtain rfl | ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, b, rfl⟩ := hy.eq_or_exists_mul
  exacts [hx, i.mul_left_mem hx, i.mul_right_mem hx, i.mem' hx]

/-! ### Membership in principal ideals -/

/-- `x` is in the principal left ideal of `y` iff `x ≤𝓛 y`. -/
@[simp] lemma LPreorder.iff_mem_leftIdeal : x ∈ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_leftIdeal_of_le ((LeftIdeal.mem_ofSet _ _).mpr (.inr rfl)) h⟩
  simp only [LeftIdeal.mem_ofSet, Set.mem_union, Set.mem_mul, Set.mem_singleton_iff] at h
  rcases h with ⟨a, -, b, rfl, rfl⟩ | rfl
  exacts [LPreorder.mul_left_self, LPreorder.refl _]

/-- `x` is in the principal right ideal of `y` iff `x ≤𝓡 y`. -/
@[simp] lemma RPreorder.iff_mem_rightIdeal : x ∈ RightIdeal.ofSet {y} ↔ x ≤𝓡 y := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_rightIdeal_of_le ((RightIdeal.mem_ofSet _ _).mpr (.inr rfl)) h⟩
  simp only [RightIdeal.mem_ofSet, Set.mem_union, Set.mem_mul, Set.mem_singleton_iff] at h
  rcases h with ⟨a, rfl, b, -, rfl⟩ | rfl
  exacts [RPreorder.mul_right_self, RPreorder.refl _]

/-- `x` is in the principal ideal of `y` iff `x ≤𝓙 y`. -/
@[simp] lemma JPreorder.iff_mem_mulTwoSidedIdeal : x ∈ MulTwoSidedIdeal.ofSet {y} ↔ x ≤𝓙 y := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_mulTwoSidedIdeal_of_le
    ((MulTwoSidedIdeal.mem_ofSet _ _).mpr (.inr ((RightIdeal.mem_ofSet _ _).mpr (.inr rfl)))) h⟩
  simp only [MulTwoSidedIdeal.mem_ofSet, Set.mem_union, SetLike.mem_coe,
    LPreorder.iff_mem_leftIdeal,
    RPreorder.iff_mem_rightIdeal, Set.mem_mul, Set.mem_singleton_iff] at h
  rcases h with (⟨_, ⟨a, -, b, rfl, rfl⟩, c, -, rfl⟩ | hl) | hr
  exacts [JPreorder.mul_sandwich_self, hl.to_jPreorder, hr.to_jPreorder]

/-! ### Inclusion and equality of principal ideals -/

/-- The principal left ideal of `x` is a subset of that of `y` iff `x ≤𝓛 y` -/
@[simp] theorem LPreorder.iff_leftIdeal_subset :
    LeftIdeal.ofSet {x} ≤ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by
  refine ⟨fun h ↦ (iff_mem_leftIdeal x y).mp (h ((iff_mem_leftIdeal x x).mpr (refl x))), ?_⟩
  intro h w hw
  exact (iff_mem_leftIdeal w y).mpr (((iff_mem_leftIdeal w x).mp hw).trans h)

/-- The principal left ideal of `x` is equal to that of `y` iff `x 𝓛 y`. -/
@[simp] theorem LEquiv.iff_leftIdeal_eq : LeftIdeal.ofSet {x} = LeftIdeal.ofSet {y} ↔ x 𝓛 y :=
  ⟨fun h ↦ ⟨(LPreorder.iff_leftIdeal_subset x y).mp h.le,
      (LPreorder.iff_leftIdeal_subset y x).mp h.ge⟩,
    fun h ↦ le_antisymm ((LPreorder.iff_leftIdeal_subset x y).mpr h.le)
      ((LPreorder.iff_leftIdeal_subset y x).mpr h.ge)⟩

/-- The principal right ideal of `x` is a subset of that of `y` iff `x ≤𝓡 y` -/
@[simp] theorem RPreorder.iff_rightIdeal_subset :
    RightIdeal.ofSet {x} ≤ RightIdeal.ofSet {y} ↔ x ≤𝓡 y := by
  refine ⟨fun h ↦ (iff_mem_rightIdeal x y).mp (h ((iff_mem_rightIdeal x x).mpr (refl x))), ?_⟩
  intro h w hw
  exact (iff_mem_rightIdeal w y).mpr (((iff_mem_rightIdeal w x).mp hw).trans h)

/-- The principal right ideal of `x` is equal to that of `y` iff `x 𝓡 y`. -/
@[simp] theorem REquiv.iff_rightIdeal_eq : RightIdeal.ofSet {x} = RightIdeal.ofSet {y} ↔ x 𝓡 y :=
  ⟨fun h ↦ ⟨(RPreorder.iff_rightIdeal_subset x y).mp h.le,
      (RPreorder.iff_rightIdeal_subset y x).mp h.ge⟩,
    fun h ↦ le_antisymm ((RPreorder.iff_rightIdeal_subset x y).mpr h.le)
      ((RPreorder.iff_rightIdeal_subset y x).mpr h.ge)⟩

/-- The principal ideal of `x` is a subset of that of `y` iff `x ≤𝓙 y` -/
@[simp] theorem JPreorder.iff_mulTwoSidedIdeal_subset :
    MulTwoSidedIdeal.ofSet {x} ≤ MulTwoSidedIdeal.ofSet {y} ↔ x ≤𝓙 y := by
  refine ⟨fun h ↦ (iff_mem_mulTwoSidedIdeal x y).mp
    (h ((iff_mem_mulTwoSidedIdeal x x).mpr (refl x))), ?_⟩
  intro h w hw
  exact (iff_mem_mulTwoSidedIdeal w y).mpr (((iff_mem_mulTwoSidedIdeal w x).mp hw).trans h)

/-- The principal ideal of `x` is equal to that of `y` iff `x 𝓙 y`. -/
@[simp] theorem JEquiv.iff_mulTwoSidedIdeal_eq :
    MulTwoSidedIdeal.ofSet {x} = MulTwoSidedIdeal.ofSet {y} ↔ x 𝓙 y :=
  ⟨fun h ↦ ⟨(JPreorder.iff_mulTwoSidedIdeal_subset x y).mp h.le,
      (JPreorder.iff_mulTwoSidedIdeal_subset y x).mp h.ge⟩,
    fun h ↦ le_antisymm ((JPreorder.iff_mulTwoSidedIdeal_subset x y).mpr h.le)
      ((JPreorder.iff_mulTwoSidedIdeal_subset y x).mpr h.ge)⟩

end Semigroup
