/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

/-!
# 2-tangle diagrams and Reidemeister moves

Representation choice. A 2-tangle diagram is stored as a *planar diagram code*:
a finite list of crossings, each carrying four arc identifiers in
counterclockwise cyclic order together with a sign, plus the four arc
identifiers incident to the fixed boundary endpoints NW, NE, SE, SW.

This is the tangle analogue of the classical PD-code used for knots. It is
chosen so that an integral coloring (Kauffman–Lambropoulou §5) is later just
a function from arc identifiers to `ℤ` satisfying the crossing rule
`α + γ = 2β`: the overstrand occupies ports `0` and `2` (same color `β`) and
the two under-arcs occupy ports `1` and `3` (colors `α` and `γ`).

We do **not** quotient by planar isotopy in the type itself. Two codes that
differ by renaming arcs, by reordering the crossing list, or by rotating a
crossing 180° (which preserves the overstrand pair `{0,2}` and the cyclic
order) represent the same embedded diagram; that identification is the
`PlanarIsotopy` generator. Reidemeister I–III are local replacements of
crossing data in the interior of the disc; the four endpoints stay fixed.

The type is an inductive finite list of crossings with four endpoints, as
hypothesized in the blueprint. Loops (an arc appearing twice at one
crossing) and closed components (circles) are allowed, matching a general
2-tangle: two arcs and finitely many circles in the disc.
-/

namespace RationalTangles

/-- The four fixed endpoints of a 2-tangle on the boundary of the projection
    disc, in counterclockwise order starting from the north-west corner. -/
inductive Endpoint where
  | NW
  | NE
  | SE
  | SW
  deriving DecidableEq, Repr

/-- Crossing sign, matching Kauffman–Lambropoulou Figure 2 (Ernst–Sumners
    convention, the opposite of Conway 1970): `pos` as in `[+1]`, `neg` as
    in `[-1]`. -/
inductive CrossingSign where
  | pos
  | neg
  deriving DecidableEq, Repr

namespace CrossingSign

/-- Reverse a crossing type: positive ↔ negative. -/
def flip : CrossingSign → CrossingSign
  | .pos => .neg
  | .neg => .pos

@[simp] theorem flip_flip (s : CrossingSign) : s.flip.flip = s := by
  cases s <;> rfl

end CrossingSign

/-- A single crossing of a 2-tangle diagram.

    Ports are read counterclockwise. Ports `0` and `2` are the overstrand;
    ports `1` and `3` are the two under-arcs. An integral coloring will
    assign one color `β` to `a0` and `a2`, and colors `α`, `γ` to `a1`, `a3`
    with `α + γ = 2β`. -/
structure Crossing where
  /-- Arc identifier at overstrand port 0. -/
  a0 : Nat
  /-- Arc identifier at understrand port 1. -/
  a1 : Nat
  /-- Arc identifier at overstrand port 2. -/
  a2 : Nat
  /-- Arc identifier at understrand port 3. -/
  a3 : Nat
  sign : CrossingSign
  deriving DecidableEq, Repr

instance : Inhabited Crossing :=
  ⟨⟨0, 1, 2, 3, .pos⟩⟩

namespace Crossing

/-- The four incident arc identifiers, indexed by port. -/
def arcs (C : Crossing) (p : Fin 4) : Nat :=
  match p.val with
  | 0 => C.a0
  | 1 => C.a1
  | 2 => C.a2
  | _ => C.a3

/-- The four incident arc identifiers as a list. -/
def arcList (C : Crossing) : List Nat :=
  [C.a0, C.a1, C.a2, C.a3]

/-- 180° rotation of the local picture: swaps the two over-ports and the two
    under-ports, preserving sign, cyclic order, and the overstrand pair. -/
def rotate180 (C : Crossing) : Crossing :=
  { a0 := C.a2, a1 := C.a3, a2 := C.a0, a3 := C.a1, sign := C.sign }

/-- Rename arc identifiers by `f`. -/
def rename (f : Nat → Nat) (C : Crossing) : Crossing :=
  { a0 := f C.a0, a1 := f C.a1, a2 := f C.a2, a3 := f C.a3, sign := C.sign }

/-- Reverse the cyclic reading of the two under-ports and flip the sign.
    For an unoriented diagram this is the same geometric crossing (clockwise
    versus counterclockwise PD convention). -/
def reverseUnders (C : Crossing) : Crossing :=
  { a0 := C.a0, a1 := C.a3, a2 := C.a2, a3 := C.a1, sign := C.sign.flip }

/-- Equal as PD-data after a 180° rotation of ports, or after reversing the
    cyclic reading of the unders with a compensating sign flip. -/
def sameUpToRotation (C D : Crossing) : Prop :=
  C = D ∨ C = D.rotate180 ∨ C = D.reverseUnders ∨ C = D.reverseUnders.rotate180

/-- `a` is incident to `C`. -/
def memArc (C : Crossing) (a : Nat) : Prop :=
  a = C.a0 ∨ a = C.a1 ∨ a = C.a2 ∨ a = C.a3

/-- Port occupied by arc `a`, if any. -/
def portOf (C : Crossing) (a : Nat) : Option (Fin 4) :=
  if C.a0 = a then some ⟨0, by decide⟩
  else if C.a1 = a then some ⟨1, by decide⟩
  else if C.a2 = a then some ⟨2, by decide⟩
  else if C.a3 = a then some ⟨3, by decide⟩
  else none

/-- Arc at the opposite port from `a` (same strand through the crossing),
    or `a` itself if `a` is not incident. -/
def oppositeArc (C : Crossing) (a : Nat) : Nat :=
  match C.portOf a with
  | some p => C.arcs (p + 2)
  | none => a

/-- A kink: two consecutive ports carry a loop arc, and the other two ports
    carry distinct through-arcs different from the loop. This is the local
    picture of Reidemeister I (a twist of writhe `±1`). -/
def IsKink (C : Crossing) (loopPort : Fin 4) : Prop :=
  C.arcs loopPort = C.arcs (loopPort + 1) ∧
    C.arcs loopPort ≠ C.arcs (loopPort + 2) ∧
    C.arcs loopPort ≠ C.arcs (loopPort + 3) ∧
    C.arcs (loopPort + 2) ≠ C.arcs (loopPort + 3)

@[simp] theorem rotate180_a0 (C : Crossing) : C.rotate180.a0 = C.a2 := rfl
@[simp] theorem rotate180_a1 (C : Crossing) : C.rotate180.a1 = C.a3 := rfl
@[simp] theorem rotate180_a2 (C : Crossing) : C.rotate180.a2 = C.a0 := rfl
@[simp] theorem rotate180_a3 (C : Crossing) : C.rotate180.a3 = C.a1 := rfl
@[simp] theorem rotate180_sign (C : Crossing) : C.rotate180.sign = C.sign := rfl

@[simp] theorem rotate180_involutive (C : Crossing) : C.rotate180.rotate180 = C := by
  cases C; rfl

@[simp] theorem reverseUnders_involutive (C : Crossing) :
    C.reverseUnders.reverseUnders = C := by
  cases C
  simp [reverseUnders]

theorem reverseUnders_rotate180 (C : Crossing) :
    C.reverseUnders.rotate180 = C.rotate180.reverseUnders := by
  cases C
  simp [reverseUnders, rotate180]

theorem sameUpToRotation_rotate180 (C : Crossing) :
    C.sameUpToRotation C.rotate180 :=
  Or.inr (Or.inl (rotate180_involutive C ▸ rfl))

end Crossing

/-- Combinatorial 2-tangle diagram in the disc: PD-code of the interior
    crossings, together with the arc incident to each of the four fixed
    endpoints. The trivial tangles `[0]` and `[∞]` have an empty crossing
    list; their two arcs run endpoint-to-endpoint. -/
structure TangleDiagram where
  crossings : List Crossing
  /-- Arc meeting the north-west endpoint. -/
  NW : Nat
  /-- Arc meeting the north-east endpoint. -/
  NE : Nat
  /-- Arc meeting the south-east endpoint. -/
  SE : Nat
  /-- Arc meeting the south-west endpoint. -/
  SW : Nat
  deriving DecidableEq, Repr

namespace TangleDiagram

/-- The horizontal trivial tangle `[0]`: arcs NW–NE and SW–SE, no crossings. -/
def zero : TangleDiagram where
  crossings := []
  NW := 0
  NE := 0
  SE := 1
  SW := 1

/-- The vertical trivial tangle `[∞]`: arcs NW–SW and NE–SE, no crossings. -/
def infinity : TangleDiagram where
  crossings := []
  NW := 0
  NE := 1
  SE := 1
  SW := 0

/-- Boundary arc at an endpoint. -/
def boundary (D : TangleDiagram) : Endpoint → Nat
  | .NW => D.NW
  | .NE => D.NE
  | .SE => D.SE
  | .SW => D.SW

/-- Rename every arc identifier by `f`. -/
def rename (D : TangleDiagram) (f : Nat → Nat) : TangleDiagram where
  crossings := D.crossings.map (Crossing.rename f)
  NW := f D.NW
  NE := f D.NE
  SE := f D.SE
  SW := f D.SW

/-- Drop the crossing at index `k` (no-op if `k` is out of range). -/
def eraseCrossing (D : TangleDiagram) (k : Nat) : TangleDiagram :=
  { D with crossings := D.crossings.eraseIdx k }

/-- An occurrence of one end of an arc. -/
inductive ArcEnd where
  | crossing (i : Nat) (p : Fin 4)
  | boundary (e : Endpoint)
  deriving DecidableEq, Repr

/-- All locations at which arc `a` appears. -/
def endsOf (D : TangleDiagram) (a : Nat) : List ArcEnd :=
  (List.finRange D.crossings.length).flatMap (fun i =>
    (List.finRange 4).flatMap (fun p =>
      if D.crossings[i].arcs p = a then [ArcEnd.crossing i.val p] else []))
  ++
  [Endpoint.NW, Endpoint.NE, Endpoint.SE, Endpoint.SW].flatMap (fun e =>
    if D.boundary e = a then [ArcEnd.boundary e] else [])

/-- A diagram is well-formed when every arc identifier that appears does so
    at exactly two ends (a matching of half-edges of the 4-valent graph).
    Boundary-to-boundary arcs (as in `[0]` and `[∞]`) and loops at a single
    crossing (kinks) are included. -/
def WellFormed (D : TangleDiagram) : Prop :=
  ∀ a : Nat, (D.endsOf a).length = 0 ∨ (D.endsOf a).length = 2

end TangleDiagram

/-- Pairwise relation on lists of the same length. -/
def pairRel {α} (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ pairRel R as bs
  | _, _ => False

/-- Planar isotopy of the projection disc with the four endpoints held
    fixed: a renaming of arcs, a permutation of the crossing list, and a
    180° rotation of any crossing (preserving overstrand pair and cyclic
    order). No crossing data is created or destroyed. -/
def PlanarIsotopy (D E : TangleDiagram) : Prop :=
  ∃ f : Nat → Nat, Function.Injective f ∧
    E.NW = f D.NW ∧ E.NE = f D.NE ∧ E.SE = f D.SE ∧ E.SW = f D.SW ∧
    ∃ Cs : List Crossing,
      pairRel Crossing.sameUpToRotation (D.crossings.map (Crossing.rename f)) Cs ∧
      List.Perm Cs E.crossings

/-- Identify arc `src` with arc `tgt`. -/
def mergeArc (src tgt : Nat) (a : Nat) : Nat :=
  if a = src then tgt else a

/-- Remove a kink at index `k` with loop occupying `loopPort` and `loopPort + 1`,
    merging the two through-arcs. On a genuine kink this is Reidemeister I
    in the deleting direction. -/
def collapseKink (D : TangleDiagram) (k : Nat) (loopPort : Fin 4) : TangleDiagram :=
  let C := D.crossings.getD k default
  let thru0 := C.arcs (loopPort + 2)
  let thru1 := C.arcs (loopPort + 3)
  (D.eraseCrossing k).rename (mergeArc thru1 thru0)

/-- `E` is obtained from `D` by adding one R1 kink on an existing strand. -/
def IsReidemeisterIAdd (D E : TangleDiagram) : Prop :=
  ∃ (k : Fin E.crossings.length) (loopPort : Fin 4),
    (E.crossings[k]).IsKink loopPort ∧
      PlanarIsotopy D (collapseKink E k.val loopPort)

/-- Reidemeister I: a kink may be added to or removed from a single strand
    (a twist of writhe `±1`), in the interior of the disc. -/
def IsReidemeisterI (D E : TangleDiagram) : Prop :=
  IsReidemeisterIAdd D E ∨ IsReidemeisterIAdd E D

/-- An arc occupies an overstrand port (0 or 2). -/
def Crossing.isOverArc (C : Crossing) (a : Nat) : Prop :=
  a = C.a0 ∨ a = C.a2

/-- An arc occupies an understrand port (1 or 3). -/
def Crossing.isUnderArc (C : Crossing) (a : Nat) : Prop :=
  a = C.a1 ∨ a = C.a3

/-- Consecutive ports of `C` carry distinct arcs (no kink at `C`). -/
def Crossing.adjacentDistinct (C : Crossing) : Prop :=
  C.a0 ≠ C.a1 ∧ C.a1 ≠ C.a2 ∧ C.a2 ≠ C.a3 ∧ C.a3 ≠ C.a0

/-- Two crossings of opposite sign sharing exactly two distinct arcs
    (a bigon), with one shared arc over at both crossings and the other
    under at both. This is Reidemeister II: one strand passes entirely
    over the other, so both crossings have the same over-color and `τ`
    is an involution on the understrand. Neither crossing is a kink. -/
def IsR2Pair (C D : Crossing) : Prop :=
  C.sign ≠ D.sign ∧
    C.adjacentDistinct ∧ D.adjacentDistinct ∧
    ∃ p q : Nat, p ≠ q ∧
      C.memArc p ∧ C.memArc q ∧ D.memArc p ∧ D.memArc q ∧
      (∀ a : Nat, (C.memArc a ∧ D.memArc a) → a = p ∨ a = q) ∧
      ((C.isOverArc p ∧ D.isOverArc p ∧ C.isUnderArc q ∧ D.isUnderArc q) ∨
        (C.isOverArc q ∧ D.isOverArc q ∧ C.isUnderArc p ∧ D.isUnderArc p))

/-- Boolean incidence test, for use in executable collapse maps. -/
def memArcB (C : Crossing) (a : Nat) : Bool :=
  a == C.a0 || a == C.a1 || a == C.a2 || a == C.a3

/-- Merge map collapsing an R2 pair: each external arc of `C` whose opposite
    port is a shared (bigon) arc is identified with the corresponding
    external arc of `D`. -/
def r2Merge (C D : Crossing) (a : Nat) : Nat :=
  let opp := C.oppositeArc a
  if memArcB C a && !memArcB D a && memArcB D opp then D.oppositeArc opp else a

/-- Remove crossings at indices `i` and `j` (larger index first). -/
def eraseTwo (D : TangleDiagram) (i j : Nat) : TangleDiagram :=
  if i < j then (D.eraseCrossing j).eraseCrossing i
  else if j < i then (D.eraseCrossing i).eraseCrossing j
  else D.eraseCrossing i

/-- Collapse an R2 pair at indices `i`, `j`. -/
def collapseR2 (D : TangleDiagram) (i j : Nat) : TangleDiagram :=
  let C := D.crossings.getD i default
  let E := D.crossings.getD j default
  (eraseTwo D i j).rename (r2Merge C E)

/-- `E` is obtained from `D` by adding one R2 pair (two opposite crossings). -/
def IsReidemeisterIIAdd (D E : TangleDiagram) : Prop :=
  ∃ (i j : Fin E.crossings.length),
    i ≠ j ∧ IsR2Pair E.crossings[i] E.crossings[j] ∧
      PlanarIsotopy D (collapseR2 E i.val j.val)

/-- Reidemeister II: two strands with two opposite crossings may be pulled
    apart, or two uncrossed strands may be overlapped to create two opposite
    crossings. -/
def IsReidemeisterII (D E : TangleDiagram) : Prop :=
  IsReidemeisterIIAdd D E ∨ IsReidemeisterIIAdd E D

/-- Three crossings form a triangle: each pair shares exactly one of three
    distinct internal arcs, and the third crossing of the triple does not
    carry that arc. This is the local picture of Reidemeister III. -/
def IsTriangle (C D E : Crossing) : Prop :=
  ∃ a b c : Nat, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
    C.memArc a ∧ D.memArc a ∧ ¬ E.memArc a ∧
    D.memArc b ∧ E.memArc b ∧ ¬ C.memArc b ∧
    E.memArc c ∧ C.memArc c ∧ ¬ D.memArc c

/-- Opposite over-port from `u` (the other end of the overstrand). -/
def Crossing.extOverArc (C : Crossing) (u : Nat) : Nat :=
  if C.a0 = u then C.a2 else C.a0

/-- Opposite under-port from `w`. -/
def Crossing.otherUnderArc (C : Crossing) (w : Nat) : Nat :=
  if C.a1 = w then C.a3 else C.a1

/-- Four ports carry pairwise distinct arcs. -/
def Crossing.portsDistinct (C : Crossing) : Prop :=
  C.a0 ≠ C.a1 ∧ C.a0 ≠ C.a2 ∧ C.a0 ≠ C.a3 ∧
    C.a1 ≠ C.a2 ∧ C.a1 ≠ C.a3 ∧ C.a2 ≠ C.a3

/-- Reidemeister III over-slide: slider over at `P` and `Q` (shared
    internal over-arc `u`); `R` is the crossing being slid over, with
    internal arcs `v` (over at `R`) and `w` (under at `P` and `R`). -/
def IsR3OverSlide (P Q R : Crossing) (u v w : Nat) : Prop :=
  P.adjacentDistinct ∧ Q.adjacentDistinct ∧ R.adjacentDistinct ∧
    P.portsDistinct ∧ Q.portsDistinct ∧ R.portsDistinct ∧
    u ≠ v ∧ v ≠ w ∧ w ≠ u ∧
      P.isOverArc u ∧ Q.isOverArc u ∧ ¬ R.memArc u ∧
      Q.isUnderArc v ∧ R.isOverArc v ∧ ¬ P.memArc v ∧
      P.isUnderArc w ∧ R.isUnderArc w ∧ ¬ Q.memArc w

/-- Matching of the six external triangle legs after renaming by `f`. -/
def r3ExtMatch (f : Nat → Nat) (PD QD RD PE QE RE : Crossing)
    (uD vD wD uE vE wE : Nat) : Prop :=
  PE.extOverArc uE = f (PD.extOverArc uD) ∧
    QE.extOverArc uE = f (QD.extOverArc uD) ∧
    PE.otherUnderArc wE = f (PD.otherUnderArc wD) ∧
    QE.otherUnderArc vE = f (QD.otherUnderArc vD) ∧
    RE.extOverArc vE = f (RD.extOverArc vD) ∧
    RE.otherUnderArc wE = f (RD.otherUnderArc wD)

/-- Exterior diagrams agree up to crossing permutation and 180° rotation
    of ports, with no further arc renaming. -/
def sameCrossingData (D E : TangleDiagram) : Prop :=
  D.NW = E.NW ∧ D.NE = E.NE ∧ D.SE = E.SE ∧ D.SW = E.SW ∧
    ∃ Cs : List Crossing,
      pairRel Crossing.sameUpToRotation D.crossings Cs ∧
        List.Perm Cs E.crossings

/-- Drop list entries whose original indices are `i`, `j`, or `k`. -/
def dropIdxs {α} (i j k : Nat) : Nat → List α → List α
  | _, [] => []
  | n, x :: xs =>
    if n = i ∨ n = j ∨ n = k then dropIdxs i j k (n + 1) xs
    else x :: dropIdxs i j k (n + 1) xs

/-- Drop the three crossings at indices `i`, `j`, `k`. -/
def eraseThree (D : TangleDiagram) (i j k : Nat) : TangleDiagram :=
  { D with crossings := dropIdxs i j k 0 D.crossings }

/-- The complement of an R3 triple: crossings other than `i,j,k`, with
    boundary unchanged. Used to require that R3 does not touch the rest of
    the diagram. -/
def exterior (D : TangleDiagram) (i j k : Nat) : TangleDiagram :=
  eraseThree D i j k

/-- Reidemeister III: a strand may be slid over a crossing of two other
    strands. The diagrams have the same crossing count, the same signs on
    a triangular triple, matching external triangle legs after renaming by
    `f`, and the same exterior (up to permutation / 180°). Internals of
    the triple are not boundary arcs and do not meet the exterior. -/
def IsReidemeisterIII (D E : TangleDiagram) : Prop :=
  ∃ (hlen : D.crossings.length = E.crossings.length)
      (f : Nat → Nat) (i j k : Fin D.crossings.length)
      (uD vD wD uE vE wE : Nat),
    Function.Injective f ∧
      i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      E.NW = f D.NW ∧ E.NE = f D.NE ∧ E.SE = f D.SE ∧ E.SW = f D.SW ∧
      uE ≠ E.NW ∧ uE ≠ E.NE ∧ uE ≠ E.SE ∧ uE ≠ E.SW ∧
      vE ≠ E.NW ∧ vE ≠ E.NE ∧ vE ≠ E.SE ∧ vE ≠ E.SW ∧
      wE ≠ E.NW ∧ wE ≠ E.NE ∧ wE ≠ E.SE ∧ wE ≠ E.SW ∧
      (∀ C ∈ (exterior E i.val j.val k.val).crossings,
        ¬ C.memArc uE ∧ ¬ C.memArc vE ∧ ¬ C.memArc wE) ∧
      D.crossings[i].sign = (E.crossings[i.val]'(hlen ▸ i.isLt)).sign ∧
      D.crossings[j].sign = (E.crossings[j.val]'(hlen ▸ j.isLt)).sign ∧
      D.crossings[k].sign = (E.crossings[k.val]'(hlen ▸ k.isLt)).sign ∧
      ((IsR3OverSlide D.crossings[i] D.crossings[j] D.crossings[k] uD vD wD ∧
          IsR3OverSlide (E.crossings[i.val]'(hlen ▸ i.isLt))
            (E.crossings[j.val]'(hlen ▸ j.isLt))
            (E.crossings[k.val]'(hlen ▸ k.isLt)) uE vE wE ∧
          r3ExtMatch f D.crossings[i] D.crossings[j] D.crossings[k]
            (E.crossings[i.val]'(hlen ▸ i.isLt))
            (E.crossings[j.val]'(hlen ▸ j.isLt))
            (E.crossings[k.val]'(hlen ▸ k.isLt)) uD vD wD uE vE wE) ∨
        (IsR3OverSlide D.crossings[j] D.crossings[k] D.crossings[i] uD vD wD ∧
          IsR3OverSlide (E.crossings[j.val]'(hlen ▸ j.isLt))
            (E.crossings[k.val]'(hlen ▸ k.isLt))
            (E.crossings[i.val]'(hlen ▸ i.isLt)) uE vE wE ∧
          r3ExtMatch f D.crossings[j] D.crossings[k] D.crossings[i]
            (E.crossings[j.val]'(hlen ▸ j.isLt))
            (E.crossings[k.val]'(hlen ▸ k.isLt))
            (E.crossings[i.val]'(hlen ▸ i.isLt)) uD vD wD uE vE wE) ∨
        (IsR3OverSlide D.crossings[k] D.crossings[i] D.crossings[j] uD vD wD ∧
          IsR3OverSlide (E.crossings[k.val]'(hlen ▸ k.isLt))
            (E.crossings[i.val]'(hlen ▸ i.isLt))
            (E.crossings[j.val]'(hlen ▸ j.isLt)) uE vE wE ∧
          r3ExtMatch f D.crossings[k] D.crossings[i] D.crossings[j]
            (E.crossings[k.val]'(hlen ▸ k.isLt))
            (E.crossings[i.val]'(hlen ▸ i.isLt))
            (E.crossings[j.val]'(hlen ▸ j.isLt)) uD vD wD uE vE wE)) ∧
      sameCrossingData
        ((exterior D i.val j.val k.val).rename f)
        (exterior E i.val j.val k.val)

/-- One Reidemeister generator: R1, R2, or R3 in the interior of the disc,
    or a planar isotopy that does not change crossing data. The four
    endpoints remain fixed. -/
inductive ReidemeisterMove : TangleDiagram → TangleDiagram → Prop where
  | r1 {D E} : IsReidemeisterI D E → ReidemeisterMove D E
  | r2 {D E} : IsReidemeisterII D E → ReidemeisterMove D E
  | r3 {D E} : IsReidemeisterIII D E → ReidemeisterMove D E
  | isotopy {D E} : PlanarIsotopy D E → ReidemeisterMove D E

end RationalTangles
