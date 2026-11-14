/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

import Mathlib.Algebra.Group.PNatPowAssoc
import Semigroup.Greens.Stable
import Semigroup.Greens.Lemma
import Semigroup.Substructures

/-!
# The Location Theorem

This file proves the Location Theorem, which states that the following
conditions are equivalent for `x y : S` where `S` is a semigroup:
  1. `x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
  2. `⟦x⟧𝓡 ∩ ⟦y⟧𝓛` contains an idempotent element.

If the semigroup is stable, these conditions are equivalent to
  3. `x * y 𝓓 x` (Alternatively, `x * y 𝓓 y`) and `x 𝓓 y`

Additionally, we prove that the 𝓗-class of an idempotent element is a group,
and we define this as a subgroup of the underlying semigroup.

## Main Definitions

* `HEquiv.subgroup_of_idempotent` - Given an idempotent element `e : S`, the 𝓗-class of `e`
* `HEquiv.group_of_idempotent` - Given an idempotent element `e : S`, the H-class of `e`
as a group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}`

## Main Theorems

* `DEquiv.mul_in_inter_iff_equiv` - For `x y : S` where `S` is a stable semigroup, `x * y` is in
`⟦x⟧𝓡 ∩ ⟦y⟧𝓛` iff `x 𝓓 y` and `x * y 𝓓 x`.
* `mul_in_inter_iff_exists_idempotent` - For `x y : S`, `x * y` is in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
iff there exists an idempotent element in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`.
* `DEquiv.maximal_subgroups_equiv` - Two maximal subgroups of a 𝓓-class are isomorphic.
* `HEquiv.hClass_of_subgroup` - Every maximal subgroup is the 𝓗-class of an idempotent element.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- In stable semigroups, `x * y` is in the intersection of the 𝓡-class of `x` and the 𝓛-class
of `y` iff `x`, `y`, and `x * y` are 𝓓-Equivalent. -/
theorem DEquiv.mul_in_inter_iff_equiv (x y : S) [Stable S] :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ x 𝓓 y ∧ x * y 𝓓 x := by
  simp only [Set.mem_inter_iff, REquiv.mem_set, LEquiv.mem_set]
  constructor
  · rintro ⟨hr, hl⟩
    exact ⟨⟨x * y, hr.symm, hl⟩, hr.to_dEquiv⟩
  · rintro ⟨hd, hd'⟩
    have hj := hd'.to_jEquiv
    exact ⟨Stable.rEquiv_of_rPreorder_and_jEquiv hj RPreorder.mul_right_self,
      Stable.lEquiv_of_lPreorder_and_jEquiv (hj.trans hd.to_jEquiv) LPreorder.mul_left_self⟩

/-- `x * y` is 𝓡-equivalent to `x` and 𝓛-equivalent to `y` iff there exists an idempotent
element in the intersection of the 𝓡-class of `y` and the 𝓛-class of `x`. -/
theorem mul_in_inter_iff_exists_idempotent (x y : S) :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
  simp only [Set.mem_inter_iff, REquiv.mem_set, LEquiv.mem_set]
  constructor
  · rintro ⟨hr, hl⟩
    -- Green's lemma: `w ↦ w * y` maps `⟦x⟧𝓛` onto `⟦x * y⟧𝓛 ∋ y`; `e` is a preimage of `y`.
    obtain ⟨e, he, hey⟩ := hr.symm.surjOn_lClass rfl hl.symm
    replace hey : e * y = y := hey
    have heR : e 𝓡 y := by
      rw [← hey]; exact hr.symm.bijOn_lClass_rEquiv rfl he
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

/-- Idempotent-containing 𝓗-classes are closed under multiplication. -/
lemma HEquiv.mul_closed_of_idempotent {e x y : S} (he : IsIdempotentElem e)
    (hx : x ∈ ⟦e⟧𝓗) (hy : y ∈ ⟦e⟧𝓗) : x * y ∈ ⟦e⟧𝓗 := by
  rw [mem_set] at hx hy ⊢
  obtain ⟨h₁, h₂⟩ := (mul_in_inter_iff_exists_idempotent x y).2
    ⟨e, he, hy.symm.to_rEquiv, hx.symm.to_lEquiv⟩
  exact (iff_rEquiv_and_lEquiv _ _).2
    ⟨REquiv.trans h₁ hx.to_rEquiv, LEquiv.trans h₂ hy.to_lEquiv⟩

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
left identity. -/
lemma HEquiv.idempotent_mul {e : S} (he : IsIdempotentElem e) {x : S} (hx : x ∈ ⟦e⟧𝓗) :
    e * x = x := by
  grind

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
right identity. -/
lemma HEquiv.mul_idempotent {e : S} (he : IsIdempotentElem e) {x : S} (hx : x ∈ ⟦e⟧𝓗) :
    x * e = x := by
  grind

/-- All idempotent elements in an 𝓗 class are equal. -/
lemma HEquiv.idempotent_eq {e x : S} (hh : x 𝓗 e)
    (he : IsIdempotentElem e) (hx : IsIdempotentElem x) : e = x := by
  grind

/-- The 𝓗-class of an idempotent element is closed under inverses. -/
private lemma HEquiv.exists_inverse_of_idempotent {e x : S}
  (he : IsIdempotentElem e) (hh : x ∈ ⟦e⟧𝓗) :
    ∃ y, y 𝓗 e ∧ x * y = e ∧ y * x = e := by
  rw [mem_set] at hh
  have hex : e * x = x := by grind
  have hxe : x * e = x := by grind
  -- Green's lemma: `w ↦ w * x` maps `⟦e⟧𝓛` bijectively onto `⟦x⟧𝓛 ∋ e`, preserving
  -- 𝓗-classes. The preimage `z` of `e` is a left inverse lying in `⟦e⟧𝓗`; injectivity
  -- then shows it is also a right inverse.
  have hr : e 𝓡 x := hh.symm.to_rEquiv
  obtain ⟨z, hz, hzx⟩ := hr.surjOn_lClass hex hh.symm.to_lEquiv
  replace hzx : z * x = e := hzx
  have hzh : z 𝓗 e := by
    rw [hr.bijOn_lClass_pres_hClass hex hz (LEquiv.refl e)]
    simpa only [hzx, hex] using hh.symm
  refine ⟨z, hzh, ?_, hzx⟩
  have hxz : x * z 𝓛 e := to_lEquiv (mul_closed_of_idempotent he hh hzh)
  apply hr.injOn_lClass hex hxz (LEquiv.refl e)
  change x * z * x = e * x
  rw [mul_assoc, hzx, hxe, hex]

open Classical in
/-- The 𝓗-class of an idempotent element as a subgroup of the semigroup. -/
noncomputable def HEquiv.subgroup_of_idempotent {e : S} (he : IsIdempotentElem e) : Subgroup S where
  carrier := ⟦e⟧𝓗
  mul_mem := HEquiv.mul_closed_of_idempotent he
  one := e
  one_mem := by simp
  one_mul {x : S} (hx : x 𝓗 e) := HEquiv.idempotent_mul he hx
  mul_one {x : S} (hx : x 𝓗 e) := HEquiv.mul_idempotent he hx
  inv x := if hx : x ∈ ⟦e⟧𝓗 then (exists_inverse_of_idempotent he hx).choose else x
  inv_not_mem hx := by simp only [hx, ↓reduceDIte]
  inv_mem hx := by
    simpa only [hx, ↓reduceDIte, mem_set] using
      (exists_inverse_of_idempotent he hx).choose_spec.1
  inv_mul hx := by
    simpa only [hx, ↓reduceDIte] using (exists_inverse_of_idempotent he hx).choose_spec.2.2
  mul_inv hx := by
    simpa only [hx, ↓reduceDIte] using (exists_inverse_of_idempotent he hx).choose_spec.2.1

@[simp] lemma HEquiv.subgroup_of_idempotent_carrier_def {e : S} (he : IsIdempotentElem e) :
    (HEquiv.subgroup_of_idempotent he).carrier = ⟦e⟧𝓗 := by
  rfl

/-- The 𝓗-class of a semigroup as a Group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}` -/
@[instance_reducible] noncomputable def HEquiv.group_of_idempotent' {e : S}
  (he : IsIdempotentElem e) :
    Group ({x // x ∈ ⟦e⟧𝓗}) :=
  inferInstanceAs (Group (HEquiv.subgroup_of_idempotent he))

/-- If there exists an `x, y` in an 𝓗 class such that `x * y` remains in the 𝓗-class,
then that 𝓗 class contains an idempotent. -/
theorem HEquiv.idempotent_in_subgroup {x y : S} (h₁ : x 𝓗 y) (h₂ : x * y 𝓗 x) :
    ∃ e, e 𝓗 x ∧ IsIdempotentElem e := by
  obtain ⟨e, he, heR, heL⟩ := (mul_in_inter_iff_exists_idempotent x y).1
    ⟨h₂.to_rEquiv, (h₂.trans h₁).to_lEquiv⟩
  exact ⟨e, (iff_rEquiv_and_lEquiv _ _).2 ⟨REquiv.trans heR h₁.to_rEquiv.symm, heL⟩, he⟩

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓡-class. -/
theorem DEquiv.idempotent_in_rClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
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
theorem DEquiv.idempotent_in_lClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
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

/-- All elements within a subgroup are 𝓗-related. -/
lemma HEquiv.ofSubgroup {x y : S} {H : Subgroup S} (hx : x ∈ H) (hy : y ∈ H) : x 𝓗 y := by
  simp_all only [iff_rEquiv_and_lEquiv, REquiv, LEquiv]
  constructor <;> constructor
  · use (H.inv y * x)
    simp [← WithOne.coe_mul, ← mul_assoc, H.mul_inv hy, H.one_mul hx]
  · use (H.inv x * y)
    simp [← WithOne.coe_mul, ← mul_assoc, H.mul_inv hx, H.one_mul hy]
  · use (x * H.inv y)
    simp [← WithOne.coe_mul, mul_assoc, H.inv_mul hy, H.mul_one hx]
  · use (y * H.inv x)
    simp [← WithOne.coe_mul, mul_assoc, H.inv_mul hx, H.mul_one hy]

/-- A maximal subgroup is the 𝓗-class of an idempotent. -/
theorem HEquiv.hClass_of_subgroup {H : Subgroup S} (hH : H.IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ H.carrier = ⟦e⟧𝓗 := by
  use H.one
  have hidem : IsIdempotentElem H.one := by
    simp only [IsIdempotentElem]
    apply H.one_mul
    exact H.one_mem
  let K := HEquiv.subgroup_of_idempotent hidem
  have hle : H ≤ K := by
    intros x hx
    simp only [subgroup_of_idempotent, set, Set.mem_ofPred_eq, K]
    apply HEquiv.ofSubgroup hx H.one_mem
  refine ⟨hidem, ?_⟩
  specialize hH K hle
  rw [hH]
  simp [subgroup_of_idempotent, K]

/-- Let `e f : S` be idempotent elements.
Let `e 𝓓 f` such that we have a `s` with `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
Then, the map `x ↦ t * x * s` is a bijection from the 𝓗-class of `e` to the 𝓗-class of `f`. -/
lemma DEquiv.bij_on_hClass {e f s t : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
  (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    Set.BijOn (fun x ↦ t * x * s) ⟦e⟧𝓗 ⟦f⟧𝓗 := by
  have hes : e * s = s := by grind
  have hsf : s * f = s := by grind
  -- `x ↦ x * s` is a bijection from ⟦e⟧𝓗 to ⟦s⟧𝓗
  obtain ⟨hs_map, hs_inj, hs_surj⟩ := hr.bijOn_hClass hes
  -- `x ↦ t * x` is a bijection from ⟦s⟧𝓗 to ⟦f⟧𝓗
  obtain ⟨ht_map, ht_inj, ht_surj⟩ := hl.bijOn_hClass ht
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro x hx
    change t * x * s ∈ _
    rw [mul_assoc]
    exact ht_map (hs_map hx)
  · intros x hs y hy heq
    simp only [mul_assoc] at heq
    have heq : x * s = y * s := by exact ht_inj (hs_map hs) (hs_map hy) heq
    exact hs_inj hs hy heq
  · intros y hy
    specialize ht_surj hy
    simp only [HEquiv.set, Set.mem_image, Set.mem_ofPred_eq] at ht_surj
    rcases ht_surj with ⟨z, hz, hz_eq⟩
    specialize hs_surj hz
    rcases hs_surj with ⟨w, hw, hw_eq⟩
    refine ⟨w, hw, ?_⟩
    simp_all only [HEquiv.set, Set.mem_ofPred_eq]
    simp only [mul_assoc]
    rw [hw_eq, hz_eq]

/-- Let `e f : S` be idempotent elements.
Let `e 𝓓 f` such that we have a `s` with `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
Let `u` be the witness of `e ≤𝓡 s` such that `s * u = e`.
Then, the map `x ↦ t * x * s` is a bijection which preserves multiplication (like a morphism). -/
private lemma DEquiv.bij_on_hClass_map_mul {e f s t x y : S} (_ : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f)
  (_ : x 𝓗 e) (hy : y 𝓗 e) :
    (fun x ↦ t * x * s) x * (fun x ↦ t * x * s) y = (fun x ↦ t * x * s) (x * y) := by
  simp only
  have hsf : s * f = s := by grind
  have hidem : IsIdempotentElem (s * t) := by
    simp only [IsIdempotentElem]
    rw [← mul_assoc, mul_assoc s, ht, hsf]
  have hsty : s * t * y = y := by
    rw [← RPreorder.le_idempotent hidem]
    apply REquiv.le
    have hr₂ : s 𝓡 s * t :=
      REquiv.mul_right_iff.2 ⟨s, by rw [← WithOne.coe_mul, mul_assoc, ht, hsf]⟩
    exact hy.to_rEquiv.trans (hr.trans hr₂)
  nth_rw 2 [← hsty]
  simp [← mul_assoc]

/-- For idempotents `e, f`, with `e 𝓓 f` such that `e 𝓡 s` and `s 𝓛 f` such that
`t * s = f`, the isomorphism between `⟦e⟧𝓗` and `⟦f⟧𝓗` -/
private noncomputable def DEquiv.hClass_equiv' {e f s t : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    HEquiv.subgroup_of_idempotent he ≃* HEquiv.subgroup_of_idempotent hf := by
  refine Subgroup.hom_of_bijOn (fun x ↦ t * x * s) (DEquiv.bij_on_hClass he hf hr hl ht) ?_
  intros w z hw hz
  exact (DEquiv.bij_on_hClass_map_mul he hf hr hl ht hw hz).symm

/-- For idempotents `e, f`, if `e 𝓓 f`, then `⟦e⟧𝓗` and `⟦f⟧𝓗` are isomorphic subgroups. -/
lemma DEquiv.hClass_equiv {e f : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hd : e 𝓓 f) :
    Nonempty (HEquiv.subgroup_of_idempotent he ≃* HEquiv.subgroup_of_idempotent hf) := by
  obtain ⟨s, hr, hl⟩ := hd
  -- let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
  obtain rfl | ⟨t, ht⟩ := hl.ge.eq_or_exists_mul
  · exact ⟨hClass_equiv' he hf hr hl hf.eq⟩ -- `f = s`: take `t := f`, as `f * f = f`
  · exact ⟨hClass_equiv' he hf hr hl ht⟩

/-- Two maximal subgroups of a 𝓓-class are isomorphic. -/
theorem DEquiv.maximal_subgroups_equiv {x y : S} {H K : Subgroup S}
  (hH : H.IsMaximal) (hK : K.IsMaximal) (hx : x ∈ H) (hy : y ∈ K) (hd : x 𝓓 y) :
    Nonempty (H ≃* K) := by
  obtain ⟨e₁, hi₁, h₁⟩ := HEquiv.hClass_of_subgroup hH
  obtain ⟨e₂, hi₂, h₂⟩ := HEquiv.hClass_of_subgroup hK
  simp only [Subgroup.mem_def, h₁, HEquiv.set, Set.mem_ofPred_eq, h₂] at hx hy
  have he : e₁ 𝓓 e₂ := hx.to_dEquiv.symm.trans (hd.trans hy.to_dEquiv)
  have heq₁ : H = HEquiv.subgroup_of_idempotent hi₁ := by ext; simp [Subgroup.mem_def, h₁]
  have heq₂ : K = HEquiv.subgroup_of_idempotent hi₂ := by ext; simp [Subgroup.mem_def, h₂]
  rw [heq₁, heq₂]
  exact DEquiv.hClass_equiv hi₁ hi₂ he

end Semigroup
