/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Data.Fintype.Option

/-!
# Finiteness of `WithOne`

Lemmas intended for `Mathlib/Algebra/Group/WithOne/`.
-/

@[expose] public section

/-- If `α` is finite, then `WithOne α` is also finite. -/
instance WithOne.finite {α : Type*} [Finite α] : Finite (WithOne α) :=
  inferInstanceAs (Finite (Option α))
