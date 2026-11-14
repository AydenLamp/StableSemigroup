/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Semigroup.Greens.Location
public import Semigroup.Substructures

/-!
# Groups of 𝓗-classes

The 𝓗-class of an idempotent element is a group. We define it as a subgroup of the
underlying semigroup and show that maximal subgroups are exactly such 𝓗-classes, and that
maximal subgroups within one 𝓓-class are isomorphic.

## Main Definitions

* `HEquiv.subgroupOfIdempotent` - Given an idempotent element `e : S`, the 𝓗-class of `e`
as a subgroup of `S`.
* `HEquiv.groupOfIdempotent` - Given an idempotent element `e : S`, the 𝓗-class of `e`
as a group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}`.

## Main Theorems

* `Subgroup.IsMaximal.exists_eq_hClass` - Every maximal subgroup is the 𝓗-class of an
idempotent element.
* `DEquiv.maximal_subgroups_equiv` - Two maximal subgroups of a 𝓓-class are isomorphic.
-/

@[expose] public section

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- Idempotent-containing 𝓗-classes are closed under multiplication. -/
lemma HEquiv.mul_closed_of_idempotent {e x y : S} (he : IsIdempotentElem e)
    (hx : x ∈ ⟦e⟧𝓗) (hy : y ∈ ⟦e⟧𝓗) : x * y ∈ ⟦e⟧𝓗 := by
  rw [mem_set] at hx hy ⊢
  obtain ⟨h₁, h₂⟩ := (mul_mem_inter_iff_exists_isIdempotentElem x y).2
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

/-- All idempotent elements in an 𝓗-class are equal. -/
lemma HEquiv.idempotent_eq {e x : S} (hh : x 𝓗 e)
    (he : IsIdempotentElem e) (hx : IsIdempotentElem x) : e = x := by
  grind

/-- The 𝓗-class of an idempotent element is closed under inverses. -/
lemma HEquiv.exists_inverse_of_idempotent {e x : S}
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
    rw [hr.hEquiv_mul_right_iff hex hz (LEquiv.refl e)]
    simpa only [hzx, hex] using hh.symm
  refine ⟨z, hzh, ?_, hzx⟩
  have hxz : x * z 𝓛 e := to_lEquiv (mul_closed_of_idempotent he hh hzh)
  apply hr.injOn_lClass hex hxz (LEquiv.refl e)
  change x * z * x = e * x
  rw [mul_assoc, hzx, hxe, hex]

open Classical in
/-- The 𝓗-class of an idempotent element as a subgroup of the semigroup. -/
noncomputable def HEquiv.subgroupOfIdempotent {e : S} (he : IsIdempotentElem e) : Subgroup S where
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

@[simp] lemma HEquiv.subgroupOfIdempotent_carrier {e : S} (he : IsIdempotentElem e) :
    (HEquiv.subgroupOfIdempotent he).carrier = ⟦e⟧𝓗 :=
  rfl

@[simp] lemma HEquiv.mem_subgroupOfIdempotent {e x : S} (he : IsIdempotentElem e) :
    x ∈ HEquiv.subgroupOfIdempotent he ↔ x 𝓗 e :=
  Iff.rfl

@[simp] lemma HEquiv.subgroupOfIdempotent_one {e : S} (he : IsIdempotentElem e) :
    (HEquiv.subgroupOfIdempotent he).one = e :=
  rfl

/-- The 𝓗-class of an idempotent `e`, as a group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}`. -/
@[instance_reducible] noncomputable def HEquiv.groupOfIdempotent {e : S}
  (he : IsIdempotentElem e) :
    Group ({x // x ∈ ⟦e⟧𝓗}) :=
  inferInstanceAs (Group (HEquiv.subgroupOfIdempotent he))

/-- All elements within a subgroup are 𝓗-related. -/
lemma HEquiv.of_mem_subgroup {x y : S} {H : Subgroup S} (hx : x ∈ H) (hy : y ∈ H) : x 𝓗 y := by
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
theorem Subgroup.IsMaximal.exists_eq_hClass {H : Subgroup S} (hH : H.IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ H.carrier = ⟦e⟧𝓗 := by
  have hidem : IsIdempotentElem H.one := H.one_mul H.one_mem
  refine ⟨H.one, hidem, ?_⟩
  have hK := hH (HEquiv.subgroupOfIdempotent hidem) fun _ hx ↦
    HEquiv.of_mem_subgroup hx H.one_mem
  exact congrArg (·.carrier) hK

/-- Let `e : S` be idempotent, and let `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s`, so `t * s = f`.
Then the map `x ↦ t * x * s` is a bijection from the 𝓗-class of `e` to the 𝓗-class of `f`. -/
lemma DEquiv.bijOn_hClass {e f s t : S} (he : IsIdempotentElem e)
  (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    Set.BijOn (fun x ↦ t * x * s) ⟦e⟧𝓗 ⟦f⟧𝓗 := by
  have hes : e * s = s := by grind
  -- compose `x ↦ x * s : ⟦e⟧𝓗 → ⟦s⟧𝓗` with `x ↦ t * x : ⟦s⟧𝓗 → ⟦f⟧𝓗`
  convert (hl.bijOn_hClass ht).comp (hr.bijOn_hClass hes) using 1
  funext x
  simp [mul_assoc]

/-- With `e, f, s, t` as in `DEquiv.bijOn_hClass` and `f` idempotent, the map
`x ↦ t * x * s` preserves multiplication on the 𝓗-class of `e`. -/
private lemma DEquiv.bijOn_hClass_map_mul {e f s t x y : S} (_ : IsIdempotentElem e)
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

/-- For idempotents `e, f` with `e 𝓡 s`, `s 𝓛 f` and `t * s = f`, the isomorphism
`x ↦ t * x * s` between `⟦e⟧𝓗` and `⟦f⟧𝓗`. -/
private noncomputable def DEquiv.hClassEquivAux {e f s t : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    HEquiv.subgroupOfIdempotent he ≃* HEquiv.subgroupOfIdempotent hf := by
  refine Subgroup.mulEquivOfBijOn (fun x ↦ t * x * s) (DEquiv.bijOn_hClass he hr hl ht) ?_
  intros w z hw hz
  exact (DEquiv.bijOn_hClass_map_mul he hf hr hl ht hw hz).symm

/-- For idempotents `e, f`, if `e 𝓓 f`, then `⟦e⟧𝓗` and `⟦f⟧𝓗` are isomorphic subgroups. -/
lemma DEquiv.hClass_equiv {e f : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hd : e 𝓓 f) :
    Nonempty (HEquiv.subgroupOfIdempotent he ≃* HEquiv.subgroupOfIdempotent hf) := by
  obtain ⟨s, hr, hl⟩ := hd
  -- let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
  obtain rfl | ⟨t, ht⟩ := hl.ge.eq_or_exists_mul
  · exact ⟨hClassEquivAux he hf hr hl hf.eq⟩ -- `f = s`: take `t := f`, as `f * f = f`
  · exact ⟨hClassEquivAux he hf hr hl ht⟩

/-- Two maximal subgroups of a 𝓓-class are isomorphic. -/
theorem DEquiv.maximal_subgroups_equiv {x y : S} {H K : Subgroup S}
  (hH : H.IsMaximal) (hK : K.IsMaximal) (hx : x ∈ H) (hy : y ∈ K) (hd : x 𝓓 y) :
    Nonempty (H ≃* K) := by
  obtain ⟨e₁, hi₁, h₁⟩ := hH.exists_eq_hClass
  obtain ⟨e₂, hi₂, h₂⟩ := hK.exists_eq_hClass
  simp only [Subgroup.mem_def, h₁, HEquiv.set, Set.mem_ofPred_eq, h₂] at hx hy
  have he : e₁ 𝓓 e₂ := hx.to_dEquiv.symm.trans (hd.trans hy.to_dEquiv)
  have heq₁ : H = HEquiv.subgroupOfIdempotent hi₁ := by ext; simp [Subgroup.mem_def, h₁]
  have heq₂ : K = HEquiv.subgroupOfIdempotent hi₂ := by ext; simp [Subgroup.mem_def, h₂]
  rw [heq₁, heq₂]
  exact DEquiv.hClass_equiv hi₁ hi₂ he

end Semigroup
