/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Reidemeister
import RationalTangles.ContinuedFraction
import RationalTangles.Tangle
import RationalTangles.IntegerTangle
import RationalTangles.Flip
import RationalTangles.Flype
import RationalTangles.Coloring
import RationalTangles.ColoringMoves
import RationalTangles.ColoringInvariance
import RationalTangles.ColoringR3
import RationalTangles.ColoringFlype
import RationalTangles.ColoringIsotopy
import RationalTangles.ColoringStandard
import RationalTangles.ColoringToStandard
import RationalTangles.ColoringFractionEq
import RationalTangles.ColorFraction
import RationalTangles.Rational
import RationalTangles.StandardForm
import RationalTangles.ContinuedFractionForm
import RationalTangles.CanonicalForm
import RationalTangles.TangleFraction
import RationalTangles.FlippingLemma
import RationalTangles.ContinuedFractionFormExists
import RationalTangles.CanonicalFormExists
import RationalTangles.ContinuedFractionCanonical
import RationalTangles.CanonicalFormUnique

/-!
# Rational tangles

Formalization of Conway's classification of rational tangles after Conway
(1970), following the combinatorial proof of Kauffman and Lambropoulou
(Adv. Appl. Math. 33 (2004), arXiv:math/0311499).

Currently the Lean sources contain combinatorial 2-tangle diagrams, the
Reidemeister generators, integer/vertical tangles, flypes and flips,
twist-form rational tangles, continued-fraction and canonical form, the
arithmetic and tangle fractions, the integral coloring of §5, and local coloring lemmas for τ
(Reidemeister I–III identities and coloring transport along planar isotopy).

See `blueprint/` for the roadmap. The classification theorem is not yet
stated.
-/
