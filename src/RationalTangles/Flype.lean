/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.IntegerTangle
import RationalTangles.Flip

/-!
# Flypes

A flype is an isotopy of a 2-tangle applied on a 2-subtangle of the form
`[±1] + t` or `[±1] * t` (Kauffman–Lambropoulou Definition 2, Figure 5).
It fixes the endpoints of the subtangle. Combinatorially the replacement is

```
[±1] + t  ↦  t^{hflip} + [±1]
[±1] * t  ↦  t^{vflip} * [±1]
```

After the flipping lemma, a *rational* flype is the commutation
`[±1] + t ∼ t + [±1]` (and likewise for `*`).
-/

namespace RationalTangles

/-- One flype of a 2-tangle, in the direction that moves the `[±1]` twist
    from the left (resp. top) to the right (resp. bottom), flipping the
    subtangle `t` as in Figure 5. -/
inductive Flype : TangleDiagram → TangleDiagram → Prop where
  | add_pos (t : TangleDiagram) :
      Flype (one.add t) (t.hflip.add one)
  | add_neg (t : TangleDiagram) :
      Flype (negOne.add t) (t.hflip.add negOne)
  | mul_pos (t : TangleDiagram) :
      Flype (one.mul t) (t.vflip.mul one)
  | mul_neg (t : TangleDiagram) :
      Flype (negOne.mul t) (t.vflip.mul negOne)

/-- A flype in either direction. -/
def IsFlype (D E : TangleDiagram) : Prop :=
  Flype D E ∨ Flype E D

end RationalTangles
