/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import ConwayEnumeration.Fraction
import ConwayEnumeration.RationalKnot

/-!
# Conway knot enumeration (computable fragment)

Executable census of **rational** (2-bridge) prime knots by Conway continued-
fraction notation, parameterized by a maximum crossing number.

See `ConwayEnumeration.RationalKnot` for method, verified counts, and gaps
relative to Conway's full 1970 tables (algebraic non-rational + basic
polyhedra through 11 crossings are not claimed here).
-/
