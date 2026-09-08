---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_slideReady RationalTangles.HasColoringFraction.mirror_slideReady RationalTangles.HasColoringFraction.of_ColoringIsotopy RationalTangles.ColoringIsotopy.of_ReidemeisterMove RationalTangles.sharpColTwo RationalTangles.not_coloring_invert_transport
proof: formalized
---

# Invert, mirror, and isotopy lift

Invert/mirror existence on slideReady diagrams and the Reidemeister-move lift. Single crossings always transport across invert (the rotate step realigns the switched rule), but on two crossings transport is false in general: the `sharpColTwo` witness on `[+1]+[+1]` forces contradictory values on the invert (`not_coloring_invert_transport`, closed by linear arithmetic). Proof part of the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Flype](../../definitions/flype.md)
