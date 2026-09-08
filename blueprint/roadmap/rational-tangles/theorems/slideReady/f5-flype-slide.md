---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_flype_slide_add_slideReady RationalTangles.coloring_flype_slide_mul_slideReady RationalTangles.coloring_flype_slide_add_any_slideReady RationalTangles.coloring_flype_slide_mul_any_slideReady RationalTangles.HasColoringFraction.flype_slide_add RationalTangles.HasColoringFraction.flype_slide_mul RationalTangles.HasColoringFraction.flype_slide_add_any_slideReady RationalTangles.HasColoringFraction.flype_slide_mul_any_slideReady
proof: formalized
---

# Restricted flype slides at the fraction level

Sign-preserving slides with diagonal and port hypotheses, with `HasColoringFraction` versions. The `*_any_slideReady` variants transport every (non-monochrome) coloring of a `slideReady` left-add / top-mul, discharging `DiagonalSum` via `twist_coloring_diagonal_slideReady`; unrestricted slides remain outstanding. Proof part of the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Flype](../../definitions/flype.md)
