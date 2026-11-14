/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Semigroup.Ideal.Basic
public import Semigroup.Ideal.Green
public import Semigroup.Greens.Finite

/-!
# Simple and 0-Simple Semigroups

This file defines simple and 0-simple semigroups and proves basic properties.

## Main Definitions

* `IsSimple` — a class for semigroups where all elements are 𝓙-related (no proper ideals).
* `IsZeroSimple` — a class for semigroups with zero where `S² ≠ 0` and every ideal
  is trivial.
* `mulImage` — `S²`, the set of all products `a * b` with `a, b ∈ S`.

## Main Results

* `IsSimple.ideal_trivial` — in a simple semigroup, every nonempty ideal is `⊤`.
* `isSimple_iff_jEquiv`, `isSimple_iff_ideal_trivial` — characterisations of simplicity.
* `JPreorder.of_isZeroSimple` — in a 0-simple semigroup, `x ≤𝓙 y` for all nonzero `y`.
* `JEquiv.of_isZeroSimple` — in a 0-simple semigroup, all nonzero elements are 𝓙-related.
* `DEquiv.of_isZeroSimple` — in a stable 0-simple semigroup, all nonzero elements are 𝓓-related.
* `IsZeroSimple.mulImage_eq_univ` — if `S` is 0-simple then `S² = S`.
-/

@[expose] public section

namespace Semigroup

/-- A simple semigroup is one in which every element is 𝓙-above every other,
i.e. there is a single 𝓙-class. Equivalently, the semigroup has no proper
two-sided ideals. -/
class IsSimple (S : Type*) [Semigroup S] : Prop where
  /-- In a simple semigroup, `x ≤𝓙 y` for all `x y`. -/
  j_total : ∀ x y : S, x ≤𝓙 y

section Simple
variable {S : Type*} [Semigroup S] [IsSimple S]

/-- In a simple semigroup, any element is 𝓙-below any other. -/
@[simp] lemma JPreorder.of_isSimple (x y : S) : x ≤𝓙 y := IsSimple.j_total x y

/-- In a simple semigroup, all elements are 𝓙-related. -/
@[simp] lemma JEquiv.of_isSimple (x y : S) : x 𝓙 y :=
  ⟨IsSimple.j_total x y, IsSimple.j_total y x⟩

/-- In a stable simple semigroup, all elements are 𝓓-related. -/
@[simp] lemma DEquiv.of_isSimple [IsStable S] (x y : S) :
    x 𝓓 y :=
  JEquiv.to_dEquiv <| JEquiv.of_isSimple x y

/-- In a simple semigroup, every nonempty two-sided ideal is the whole semigroup. -/
theorem IsSimple.ideal_trivial (I : MulTwoSidedIdeal S) (hI : I ≠ ∅) : I = ⊤ := by
  ext x
  simp only [MulTwoSidedIdeal.mem_top, iff_true]
  obtain ⟨y, hy⟩ := MulTwoSidedIdeal.exists_mem_of_ne_empty hI
  exact JPreorder.mem_mulTwoSidedIdeal_of_le hy (JPreorder.of_isSimple x y)

end Simple

variable {S : Type*} [Semigroup S] in
/-- A semigroup is simple iff it consists of a single 𝓙-class. -/
theorem isSimple_iff_jEquiv : IsSimple S ↔ ∀ x y : S, x 𝓙 y :=
  ⟨fun _ ↦ JEquiv.of_isSimple, fun h ↦ ⟨fun x y ↦ (h x y).le⟩⟩

variable {S : Type*} [Semigroup S] in
/-- A semigroup is simple iff every nonempty two-sided ideal is the whole semigroup. -/
theorem isSimple_iff_ideal_trivial :
    IsSimple S ↔ ∀ I : MulTwoSidedIdeal S, I ≠ ∅ → I = ⊤ := by
  refine ⟨fun _ ↦ IsSimple.ideal_trivial, fun h ↦ ⟨fun x y ↦ ?_⟩⟩
  have hy : y ∈ MulTwoSidedIdeal.ofSet {y} := by simp
  rw [← JPreorder.iff_mem_mulTwoSidedIdeal, h (.ofSet {y}) fun h0 ↦ by rw [h0] at hy; contradiction]
  exact MulTwoSidedIdeal.mem_top

/-- A semigroup with zero is **0-simple** if `S² ≠ 0` and every ideal is `∅`, `{0}`, or `S`. -/
class IsZeroSimple (S : Type*) [SemigroupWithZero S] : Prop where
  /-- There exist elements whose product is nonzero. -/
  exists_nonzero_mul : ∃ a b : S, a * b ≠ 0
  /-- Every two-sided ideal is trivial. -/
  ideal_trivial : ∀ (I : MulTwoSidedIdeal S), I = ∅ ∨ (I : Set S) = ({0} : Set S) ∨ I = ⊤

section ZeroSimple
variable {S : Type*} [SemigroupWithZero S] [IsZeroSimple S]

/-- In a 0-simple semigroup, `x ≤𝓙 y` for every `x` and every nonzero `y`. -/
theorem JPreorder.of_isZeroSimple (x : S) {y : S} (hy : y ≠ 0) : x ≤𝓙 y := by
  -- `x ≤𝓙 y ↔ x ∈ ofSet {y}`, and `ofSet {y}` must be `⊤` since it contains `y ≠ 0`.
  have hy_mem : y ∈ MulTwoSidedIdeal.ofSet {y} := by simp
  rcases IsZeroSimple.ideal_trivial (MulTwoSidedIdeal.ofSet {y}) with h | h | h
  · rw [h] at hy_mem; contradiction
  · exact absurd (Set.mem_singleton_iff.mp (h ▸ hy_mem : y ∈ ({0} : Set S))) hy
  · rw [← JPreorder.iff_mem_mulTwoSidedIdeal, h]
    exact MulTwoSidedIdeal.mem_top

/-- In a 0-simple semigroup, all nonzero elements are 𝓙-related. -/
theorem JEquiv.of_isZeroSimple {x y : S} (hx : x ≠ 0) (hy : y ≠ 0) : x 𝓙 y :=
  ⟨JPreorder.of_isZeroSimple x hy, JPreorder.of_isZeroSimple y hx⟩

/-- In a stable 0-simple semigroup, all nonzero elements are 𝓓-related. -/
theorem DEquiv.of_isZeroSimple [IsStable S] {x y : S} (hx : x ≠ 0) (hy : y ≠ 0) : x 𝓓 y :=
  JEquiv.to_dEquiv <| JEquiv.of_isZeroSimple hx hy

end ZeroSimple


/-! ## 0-Simple Semigroups and S² -/

section zero_simple

variable (S : Type*)

open Pointwise

/-- `S²` is the set of all products `a * b` with `a, b ∈ S`. -/
abbrev mulImage [Semigroup S] : Set S := (Set.univ : Set S) * (Set.univ : Set S)

open MulTwoSidedIdeal

/-- `S²` is a two-sided ideal. -/
def mulImageIdeal [Semigroup S] : MulTwoSidedIdeal S where
  carrier := mulImage S
  mem_mul_mem := by
    intro x hx y
    obtain ⟨a, _, b, _, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨a, Set.mem_univ _, b * y, Set.mem_univ _, (mul_assoc _ _ _).symm⟩
  mul_mem_mem := by
    intro x hx y
    obtain ⟨a, _, b, _, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨y * a, Set.mem_univ _, b, Set.mem_univ _, mul_assoc _ _ _⟩

lemma mulImage_ne_singleton_zero [SemigroupWithZero S] [IsZeroSimple S] :
    (mulImage S : Set S) ≠ {0} := by
  obtain ⟨a, b, hab_ne⟩ := IsZeroSimple.exists_nonzero_mul (S := S)
  intro h_eq
  have : a * b ∈ mulImage S := Set.mul_mem_mul (Set.mem_univ _) (Set.mem_univ _)
  rw [h_eq, Set.mem_singleton_iff] at this
  exact hab_ne this

/-- If `S` is 0-simple then `S² = S`. -/
theorem IsZeroSimple.mulImage_eq_univ [SemigroupWithZero S] [IsZeroSimple S] :
    (mulImage S : Set S) = Set.univ := by
  obtain ⟨a, b, hab_ne⟩ := IsZeroSimple.exists_nonzero_mul (S := S)
  rcases IsZeroSimple.ideal_trivial (mulImageIdeal S) with h | h | h
  · have hab : a * b ∈ mulImageIdeal S := Set.mul_mem_mul (Set.mem_univ a) (Set.mem_univ b)
    rw [h] at hab; contradiction
  · exact absurd h (mulImage_ne_singleton_zero S)
  · exact congrArg SetLike.coe h

end zero_simple

end Semigroup
