import Semigroup.Greens.Stable
import Semigroup.Greens.HClassGroup
import Semigroup.Greens.Finite
import Semigroup.Ideal.Green

namespace Semigroup

variable {S : Type*} [Semigroup S] {x y z e : S}

/-! `grind`: forward chaining along the implication lattice of Green's relations. -/
example (h : x 𝓡 y) : y ≤𝓡 x := by grind
example (h : x 𝓗 y) : x ≤𝓗 y ∧ y ≤𝓗 x := by grind
example (h : x 𝓗 y) : x 𝓙 y := by grind
example (h : x 𝓗 y) : x 𝓓 y := by grind
example (h : x ≤𝓗 y) : x ≤𝓙 y := by grind

/-! `grind`: idempotents act as identities on their 𝓡/𝓛-lower sets. -/
example (he : IsIdempotentElem e) (hx : x 𝓗 e) : e * x = x ∧ x * e = x := by grind

/-! `grind`: stability, and 𝓓 = 𝓙 in stable semigroups. -/
example [IsStable S] (hj : x 𝓙 y) (hr : x ≤𝓡 y) : x 𝓡 y := by grind
example [IsStable S] (h : x 𝓙 y) : x 𝓓 y := by grind
example [IsStable S] (h : x 𝓓 y) (h' : y 𝓙 z) : x 𝓓 z := by grind [JEquiv.trans]

/-! `simp` normal forms. -/
example : y ∈ ⟦x⟧𝓡 ↔ y 𝓡 x := by simp
example : x ∈ ⟦x⟧𝓓 := by simp
example : x * y ≤𝓡 x := by simp
example : x 𝓡 x * y ↔ x ≤𝓡 x * y := by simp
example : x * y 𝓡 x ↔ x ≤𝓡 x * y := by simp
example : x ∈ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by simp
example : MulTwoSidedIdeal.ofSet {x} = MulTwoSidedIdeal.ofSet {y} ↔ x 𝓙 y := by simp
example : x * y ∈ RightIdeal.ofSet {x} := by simp

/-! `rfl` closes reflexivity goals via `@[refl]`. -/
example : x 𝓙 x := by rfl

/-! Finite semigroups are stable with no extra power instances on `WithOne S`. -/
example [Finite S] (h : x 𝓙 y) : x 𝓓 y := by grind
example [Finite S] : IsStable S := inferInstance

end Semigroup
