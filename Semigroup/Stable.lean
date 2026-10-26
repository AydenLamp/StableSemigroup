/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

import Mathlib
import Semigroup.Greens.Defs

/-!
# Stable Semigroups

This file defines stable semigroups.
-/

namespace Semigroup

class Stable (T : Type*) [Semigroup T] where
  hstable : ∀ x y : T,
(x 𝓙 y →  x ≤𝓡 y → x  𝓡 y) ∧ (x 𝓙 y →  x ≤𝓛 y → x  𝓛 y)

end Semigroup
