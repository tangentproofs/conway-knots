/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Tangle

/-!
# Flips

A flip is a 180° rotation in space of a 2-tangle (Kauffman–Lambropoulou
Definition 3). The horizontal flip rotates around a horizontal axis in the
plane of the diagram (top and bottom endpoints swap; crossings are
mirrored). The vertical flip rotates around a vertical axis (left and right
endpoints swap; crossings are mirrored).

In general a flip switches endpoints and need not be an isotopy of
2-tangles. For rational tangles it is, by the flipping lemma.
-/

namespace RationalTangles

namespace TangleDiagram

/-- Horizontal flip `T^{hflip}`: 180° rotation around a horizontal axis in
    the plane of `T`. Top and bottom endpoints swap, and every crossing is
    switched. -/
def hflip (T : TangleDiagram) : TangleDiagram :=
  let T' := T.mirror
  { T' with NW := T'.SW, NE := T'.SE, SE := T'.NE, SW := T'.NW }

/-- Vertical flip `T^{vflip}`: 180° rotation around a vertical axis in the
    plane of `T`. Left and right endpoints swap, and every crossing is
    switched. -/
def vflip (T : TangleDiagram) : TangleDiagram :=
  let T' := T.mirror
  { T' with NW := T'.NE, NE := T'.NW, SE := T'.SW, SW := T'.SE }

end TangleDiagram

end RationalTangles
