import Mathlib.Data.Finite.Card
import Semigroup.Greens.Defs
import Semigroup.Greens.Basic
import Semigroup.Greens.Finite

/- This file defines stable semigroups and proves that
stable semigroups satisfy the J = D property and the
sandwich property for H-equivalence. Both these theorems
are proved for finite semigroups in the Finite file, but the
results here are more general.

It goes on to prove that finite semigroups are stable using the theorems REquiv.
of_rPreorder_and_jEquiv and
LEquiv.of_lPreorder_and_jEquiv in the Finite file.
This is  then used to prove (trivially) that finite semigroups have the D = J
property and the sandwich property for H-equivalence in finite semigroups.

SUGGESTED RE-ORGANIZATION: Change the Finite file so that it only contains
the proofs of REquiv.of_rPreorder_and_jEquiv and
LEquiv.of_lPreorder_and_jEquiv. The theorems that D = J for finite semigroups
and the sandwich property for H-equivalence for finite semigroups may not be
needed since they will be subsumed under the results for stability.

-/


namespace Semigroup



class Stable (T : Type*) [Semigroup T] where
  hstable : ∀ x y : T,
(x 𝓙 y →  x ≤𝓡 y → x  𝓡 y) ∧ (x 𝓙 y →  x ≤𝓛 y → x  𝓛 y)


variable {S : Type*} [Semigroup S] {x y u v : S}




-- in stable semigroups, J-equivalence implies D-equivalence.  Note that
-- this should be used in place of a theorem asserting the same thing
-- for finite semigroups in the file Finite.lean

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
      apply (Stable.hstable y x).right
      · exact JEquiv.symm hj
      exact this
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
      exact REquiv.symm ((Stable.hstable  (x * a) x).left  h₂ h₁ )
    · have h₁: y ≤𝓛 x * a := hylxa
      have h₂ : y 𝓙 x * a   := by
        constructor
        · exact LPreorder.to_jPreorder hylxa
        · calc
            x * a ≤𝓙 x := by
              apply RPreorder.to_jPreorder
              exact RPreorder.mul_right_self
            _ ≤𝓙 y := ge (JEquiv.symm hj)
      exact LEquiv.symm ((Stable.hstable y (x * a)).right h₂ h₁ )

/-- In stable semigroups, the 𝓓-relation equals the 𝓙-relation. -/
theorem dEquiv_iff_jEquiv' [Stable S] : x 𝓓 y ↔ x 𝓙 y := ⟨DEquiv.to_jEquiv, JEquiv.to_dEquiv'⟩

/-- Sandwich property. In stable  semigroups, an element sandwiched between two factors is 𝓗-related
to its left and right partial products. -/
theorem HEquiv.of_eq_sandwich' [Stable S] (h : u * x * v = x) : x 𝓗 u * x ∧ x 𝓗 x * v := by
  have hxrleux : x ≤𝓡 u * x := by
    calc
      x = u * x * v := Eq.symm h
      _ ≤𝓡 u * x := RPreorder.mul_right_self
  have huxllex : u * x ≤𝓛 x := LPreorder.mul_left_self
  have hxllexv : x ≤𝓛 x * v := by
    calc
      x =  u * x * v := Eq.symm h
      _ = u * (x * v) := by rw [mul_assoc]
      _ ≤𝓛 x * v := LPreorder.mul_left_self
  have hxvrlex : x * v ≤𝓡 x := RPreorder.mul_right_self
  have hxjux : x 𝓙 u * x :=
   by
    constructor
    ·  exact RPreorder.to_jPreorder hxrleux
    ·  exact LPreorder.to_jPreorder huxllex
  have hxjxv : x 𝓙 x * v := by
    constructor
    · exact LPreorder.to_jPreorder hxllexv
    · exact RPreorder.to_jPreorder hxvrlex
  constructor
  · apply (Semigroup.HEquiv.iff_rEquiv_and_lEquiv x (u * x)).mpr
    constructor
    · exact (Stable.hstable x (u * x)).left hxjux hxrleux
    · exact LEquiv.symm ((Stable.hstable (u * x) x).right (JEquiv.symm hxjux) huxllex )
  · apply (Semigroup.HEquiv.iff_rEquiv_and_lEquiv x (x * v)).mpr
    constructor
    · exact REquiv.symm ((Stable.hstable (x * v) x).left (JEquiv.symm hxjxv) hxvrlex)
    · exact (Stable.hstable x (x * v)).right hxjxv hxllexv


/- finite semigroups are stable -/

instance stable_if_finite [Finite S]
 [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)] : Stable S where
  hstable := by
    intro x y
    constructor
    · intro h
      exact fun a ↦ REquiv.of_rPreorder_and_jEquiv a h
    · intro h
      exact fun a ↦ LEquiv.of_lPreorder_and_jEquiv a h

/- J = D in finite semigroups-/
@[simp] lemma JEquiv.to_dEquiv'' [Finite S] [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)]
 (hj : x 𝓙 y) : x 𝓓 y := to_dEquiv' hj

/- Sandwich property for finite semigroups -/
theorem HEquiv.of_eq_sandwich'' [Finite S] [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)]
(h : u * x * v = x) : x 𝓗 u * x ∧ x 𝓗 x * v :=  of_eq_sandwich' h




end  Semigroup
