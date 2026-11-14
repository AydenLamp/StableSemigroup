/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/
import Semigroup.Greens.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.WithOne.Basic

/-!
# Basic Properties of Green's Relations

This file proves basic lemmas about Green's relations.

## Main results

* `Semigroup.HEquiv.iff_rEquiv_and_lEquiv` — 𝓗 is the intersection of 𝓡 and 𝓛.

**Multiplication compatibility**
* `Semigroup.REquiv.lmul_compat` — `𝓡` is compatible with left multiplication.
* `Semigroup.LEquiv.rmul_compat` — `𝓛` is compatible with right multiplication.

**Coercion lemmas**
The `@[simp]`-tagged lemmas close goals like `x * y ≤𝓡 x` automatically.
Given `hr : x 𝓡 y` and a goal `x 𝓙 y`, `simp [hr]` or `simp_all` suffices.

**Idempotent properties**
* `Semigroup.RPreorder.le_idempotent` — `x ≤𝓡 e ↔ x = e * x`.
* `Semigroup.LPreorder.le_idempotent` — `x ≤𝓛 e ↔ x = x * e`.
* `Semigroup.HPreorder.le_idempotent` — `x ≤𝓗 e ↔ x = e * x ∧ x = x * e`.

**Morphism preservation** for all Green's relations and preorders.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- 𝓗 is the intersection of 𝓡 and 𝓛. -/
theorem HEquiv.iff_rEquiv_and_lEquiv (x y : S) : x 𝓗 y ↔ x 𝓡 y ∧ x 𝓛 y := by
  simp [HEquiv, HPreorder, LEquiv, REquiv]; tauto

/-! ### Multiplication compatibility of 𝓡 and 𝓛 -/

lemma RPreorder.lmul_compat {x y : S} (h : x ≤𝓡 y) (z : S) : z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by simp [mul_assoc, hu]⟩

theorem REquiv.lmul_compat {x y : S} (h : x 𝓡 y) (z : S) : z * x 𝓡 z * y :=
  ⟨h.1.lmul_compat z, h.2.lmul_compat z⟩

lemma LPreorder.rmul_compat {x y : S} (h : x ≤𝓛 y) (z : S) : x * z ≤𝓛 y * z := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by simp [← mul_assoc, hu]⟩

theorem LEquiv.rmul_compat {x y : S} (h : x 𝓛 y) (z : S) : x * z 𝓛 y * z :=
  ⟨h.1.rmul_compat z, h.2.rmul_compat z⟩

section DerivedAPI

variable {x y z : S}

/-! ### Coercion lemmas -/

@[grind →] lemma RPreorder.to_jPreorder (h : x ≤𝓡 y) : x ≤𝓙 y := by
  obtain ⟨u, hu⟩ := h
  exact ⟨1, u, by simp_all⟩

@[grind →] lemma LPreorder.to_jPreorder (h : x ≤𝓛 y) : x ≤𝓙 y := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, 1, by simp_all⟩

@[grind →] lemma HPreorder.to_rPreorder (h : x ≤𝓗 y) : x ≤𝓡 y := h.1
@[grind →] lemma HPreorder.to_lPreorder (h : x ≤𝓗 y) : x ≤𝓛 y := h.2

@[grind →] lemma REquiv.to_jEquiv (h : x 𝓡 y) : x 𝓙 y := ⟨h.le.to_jPreorder, h.ge.to_jPreorder⟩
@[grind →] lemma LEquiv.to_jEquiv (h : x 𝓛 y) : x 𝓙 y := ⟨h.le.to_jPreorder, h.ge.to_jPreorder⟩

@[grind →] lemma DEquiv.to_jEquiv (h : x 𝓓 y) : x 𝓙 y := by
  obtain ⟨z, ⟨⟨o, ho⟩, ⟨u, hu⟩⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := h
  exact ⟨⟨v, o, by rw [hv, ho]⟩, ⟨w, u, by rw [← hw, ← hu]; simp [← mul_assoc]⟩⟩

@[grind →] lemma HEquiv.to_rEquiv (h : x 𝓗 y) : x 𝓡 y := ((iff_rEquiv_and_lEquiv x y).mp h).1
@[grind →] lemma HEquiv.to_lEquiv (h : x 𝓗 y) : x 𝓛 y := ((iff_rEquiv_and_lEquiv x y).mp h).2

lemma HEquiv.to_jEquiv (h : x 𝓗 y) : x 𝓙 y := h.to_rEquiv.to_jEquiv

lemma HEquiv.to_dEquiv (h : x 𝓗 y) : x 𝓓 y := ⟨x, REquiv.refl x, h.to_lEquiv⟩
@[grind →] lemma REquiv.to_dEquiv (h : x 𝓡 y) : x 𝓓 y := ⟨y, h, LEquiv.refl y⟩
@[grind →] lemma LEquiv.to_dEquiv (h : x 𝓛 y) : x 𝓓 y := ⟨x, REquiv.refl x, h⟩

/-! ### Multiplication lemmas -/

@[simp] lemma RPreorder.mul_right_self : x * y ≤𝓡 x := ⟨y, WithOne.coe_mul ..⟩
@[simp] lemma LPreorder.mul_left_self : x * y ≤𝓛 y := ⟨x, WithOne.coe_mul ..⟩
@[simp] lemma JPreorder.mul_sandwich_self : x * y * z ≤𝓙 y := ⟨x, z, by simp⟩

/-! ### Witness elimination

The definitions quantify over `WithOne S`; these lemmas eliminate the adjoined identity,
so proofs can use `obtain rfl | ⟨z, rfl⟩ := h.eq_or_exists_mul` instead of case splitting. -/

lemma RPreorder.eq_or_exists_mul (h : x ≤𝓡 y) : x = y ∨ ∃ z, y * z = x := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => exact .inl (by simpa using hz.symm)
  | coe z => exact .inr ⟨z, by simpa [← WithOne.coe_mul] using hz⟩

lemma LPreorder.eq_or_exists_mul (h : x ≤𝓛 y) : x = y ∨ ∃ z, z * y = x := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => exact .inl (by simpa using hz.symm)
  | coe z => exact .inr ⟨z, by simpa [← WithOne.coe_mul] using hz⟩

lemma JPreorder.eq_or_exists_mul (h : x ≤𝓙 y) :
    x = y ∨ (∃ a, a * y = x) ∨ (∃ b, y * b = x) ∨ ∃ a b, a * y * b = x := by
  obtain ⟨u, v, h⟩ := h
  cases u with
  | one =>
    cases v with
    | one => exact .inl (by simpa using h.symm)
    | coe b => exact .inr (.inr (.inl ⟨b, by simpa [← WithOne.coe_mul] using h⟩))
  | coe a =>
    cases v with
    | one => exact .inr (.inl ⟨a, by simpa [← WithOne.coe_mul] using h⟩)
    | coe b => exact .inr (.inr (.inr ⟨a, b, by simpa [← WithOne.coe_mul] using h⟩))

lemma REquiv.of_preorder_mul_right (h : x ≤𝓡 x * y) : x 𝓡 x * y :=
  ⟨h, RPreorder.mul_right_self⟩

lemma LEquiv.of_preorder_mul_left (h : x ≤𝓛 y * x) : x 𝓛 y * x :=
  ⟨h, LPreorder.mul_left_self⟩

lemma JEquiv.of_preorder_mul_sandwich (h : x ≤𝓙 y * x * z) : x 𝓙 y * x * z :=
  ⟨h, JPreorder.mul_sandwich_self⟩

/-- Normal form: a right multiple is always `≤𝓡`, so `x 𝓡 x * y` reduces to one inequality. -/
@[simp] lemma REquiv.mul_right_iff : x 𝓡 x * y ↔ x ≤𝓡 x * y :=
  ⟨REquiv.le, REquiv.of_preorder_mul_right⟩

@[simp] lemma REquiv.mul_right_iff' : x * y 𝓡 x ↔ x ≤𝓡 x * y :=
  ⟨REquiv.ge, fun h ↦ ⟨RPreorder.mul_right_self, h⟩⟩

@[simp] lemma LEquiv.mul_left_iff : x 𝓛 y * x ↔ x ≤𝓛 y * x :=
  ⟨LEquiv.le, LEquiv.of_preorder_mul_left⟩

@[simp] lemma LEquiv.mul_left_iff' : y * x 𝓛 x ↔ x ≤𝓛 y * x :=
  ⟨LEquiv.ge, fun h ↦ ⟨LPreorder.mul_left_self, h⟩⟩

lemma REquiv.right_cancel (h : x 𝓡 x * y * z) : x 𝓡 x * y := by
  simp_all only [REquiv, RPreorder.mul_right_self, and_true]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  exact ⟨z * u, by simp_rw [WithOne.coe_mul, ← mul_assoc] at *; exact hu⟩

lemma REquiv.right_extend (h : x 𝓡 x * y * z) : x * y 𝓡 x * y * z := by
  simp_all only [REquiv, RPreorder.mul_right_self, and_true]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  exact ⟨u * y, by simp_rw [WithOne.coe_mul, ← mul_assoc] at *; rw [hu]⟩

lemma LEquiv.left_cancel (h : x 𝓛 z * y * x) : x 𝓛 y * x := by
  simp_all only [LEquiv, LPreorder.mul_left_self, and_true]
  obtain ⟨u, hu⟩ := h
  exact ⟨u * z, by simp_rw [WithOne.coe_mul, ← mul_assoc] at *; exact hu⟩

lemma LEquiv.left_extend (h : x 𝓛 z * y * x) : y * x 𝓛 z * y * x := by
  simp_all only [LEquiv, LPreorder.mul_left_self, and_true, LPreorder.rmul_compat]
  obtain ⟨u, hu⟩ := h
  exact ⟨y * u, by
    simp_rw [WithOne.coe_mul, ← mul_assoc] at *
    have : ↑y * u * ↑z * y * x = ↑y * (u * ↑z * y * x) := by simp [← mul_assoc]
    rw [this, hu]⟩

end DerivedAPI

/-! ### Idempotent properties -/

/-- An element `x` is 𝓡-below an idempotent `e` if and only if `x = e * x`. -/
theorem RPreorder.le_idempotent {e : S} (h : IsIdempotentElem e) (x : S) :
    (x ≤𝓡 e) ↔ (e * x = x) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [← hru, ← mul_assoc, h]
  · intro hl
    exact ⟨x, by rwa [← WithOne.coe_inj] at hl⟩

/-- An element `x` is 𝓛-below an idempotent `e` if and only if `x = x * e`. -/
theorem LPreorder.le_idempotent {e : S} (h : IsIdempotentElem e) (x : S) :
    (x ≤𝓛 e) ↔ (x * e = x) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [← hru, mul_assoc, h]
  · intro hl
    exact ⟨x, by rwa [← WithOne.coe_inj] at hl⟩

-- Fire only when both the idempotent and an inequality against it are already known.
grind_pattern RPreorder.le_idempotent => IsIdempotentElem e, x ≤𝓡 e
grind_pattern LPreorder.le_idempotent => IsIdempotentElem e, x ≤𝓛 e

/-- An element is 𝓗-below an idempotent if and only if it is a sandwich fixed point. -/
theorem HPreorder.le_idempotent {e : S} (he : IsIdempotentElem e) (x : S) :
    x ≤𝓗 e ↔ e * x * e = x := by
  constructor
  · rintro ⟨hr, hl⟩
    rw [RPreorder.le_idempotent he] at hr
    rw [LPreorder.le_idempotent he] at hl
    rw [hr, hl]
  · intro h; constructor
    · rw [← h]
      exact ⟨x * e, by simp [← WithOne.coe_mul, ← mul_assoc]⟩
    · rw [← h]
      exact ⟨e * x, by simp [← WithOne.coe_mul, mul_assoc]⟩

/-! ### Morphism preservations -/

section Morphism

variable {S T : Type*} [Semigroup S] [Semigroup T] {x y : S}
variable {F : Type*} [FunLike F S T] [MulHomClass F S T] (f : F)

/-- The 𝓡-preorder is preserved by semigroup morphisms: transport the witness along
`WithOne.mapMulHom f`. -/
lemma RPreorder.map (h : x ≤𝓡 y) : f x ≤𝓡 f y := by
  obtain ⟨z, hz⟩ := h
  have := congrArg (WithOne.mapMulHom (f : S →ₙ* T)) hz
  rw [map_mul, WithOne.mapMulHom_coe, WithOne.mapMulHom_coe] at this
  exact ⟨_, this⟩

/-- The 𝓛-preorder is preserved by semigroup morphisms. -/
lemma LPreorder.map (h : x ≤𝓛 y) : f x ≤𝓛 f y := by
  obtain ⟨z, hz⟩ := h
  have := congrArg (WithOne.mapMulHom (f : S →ₙ* T)) hz
  rw [map_mul, WithOne.mapMulHom_coe, WithOne.mapMulHom_coe] at this
  exact ⟨_, this⟩

/-- The 𝓙-preorder is preserved by semigroup morphisms. -/
lemma JPreorder.map (h : x ≤𝓙 y) : f x ≤𝓙 f y := by
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (WithOne.mapMulHom (f : S →ₙ* T)) huv
  rw [map_mul, map_mul, WithOne.mapMulHom_coe, WithOne.mapMulHom_coe] at this
  exact ⟨_, _, this⟩

/-- The 𝓗-preorder is preserved by semigroup morphisms. -/
lemma HPreorder.map (h : x ≤𝓗 y) : f x ≤𝓗 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓡 equivalence is preserved by semigroup morphisms. -/
lemma REquiv.map (h : x 𝓡 y) : f x 𝓡 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓛 equivalence is preserved by semigroup morphisms. -/
lemma LEquiv.map (h : x 𝓛 y) : f x 𝓛 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓙 equivalence is preserved by semigroup morphisms. -/
lemma JEquiv.map (h : x 𝓙 y) : f x 𝓙 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓗 equivalence is preserved by semigroup morphisms. -/
lemma HEquiv.map (h : x 𝓗 y) : f x 𝓗 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓓 equivalence is preserved by semigroup morphisms. -/
lemma DEquiv.map (h : x 𝓓 y) : f x 𝓓 f y := by
  obtain ⟨z, hxz, hyz⟩ := h
  exact ⟨f z, hxz.map f, hyz.map f⟩

end Morphism

end Semigroup
