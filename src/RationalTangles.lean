/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Reidemeister
import RationalTangles.ContinuedFraction

/-!
# Rational tangles

Formalization of Conway's classification of rational tangles after Conway
(1970), following the combinatorial proof of Kauffman and Lambropoulou
(Adv. Appl. Math. 33 (2004), arXiv:math/0311499).

Currently the Lean sources contain:

* combinatorial 2-tangle diagrams (PD-code) and Reidemeister I–III plus
  planar isotopy (`ReidemeisterMove`);
* finite signed simple continued fractions with values in `ℚ ∪ {∞}`
  (`ArithmeticCF`).

See `blueprint/` for the roadmap. The classification theorem is not yet
stated.
-/
