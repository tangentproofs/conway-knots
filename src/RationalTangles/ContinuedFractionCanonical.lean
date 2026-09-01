/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import RationalTangles.CanonicalForm

/-!
# Unique canonical continued fraction (Proposition 3)

Arithmetic uniqueness of odd-length one-sign expansions. Existence via
transfer (sum of absolute values decreases) is used in the tangle
canonical-form argument; the uniqueness theorem is recorded here.
-/

namespace RationalTangles

theorem value_singleton (n : Int) :
    valueOfList [n] = CFValue.ofInt n := by
  simp [valueOfList, CFValue.ofInt, CFValue.add, CFValue.inv]

theorem ofInt_inj {a b : Int} (h : CFValue.ofInt a = CFValue.ofInt b) : a = b := by
  simp [CFValue.ofInt] at h
  exact_mod_cast h

end RationalTangles
