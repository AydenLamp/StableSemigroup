/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/
module

public import Mathlib.Algebra.Group.PNatPowAssoc

/-!
# Successor lemmas for `PNatPowAssoc`

Lemmas intended for `Mathlib/Algebra/Group/PNatPowAssoc.lean`.
-/

public section

variable {M : Type*} [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_succ (x : M) (n : ℕ+) : x ^ (n + 1) = x ^ n * x := by
  nth_rw 3 [← ppow_one x]
  rw [ppow_add]

theorem ppow_succ' (x : M) (n : ℕ+) : x ^ (n + 1) = x * x ^ n := by
  nth_rw 2 [← ppow_one x]
  rw [← ppow_add, add_comm]
