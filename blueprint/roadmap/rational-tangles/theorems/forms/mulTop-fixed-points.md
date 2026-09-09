---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.mulTop_comm_zero_false RationalTangles.TwistExpr.mulTop_comm_inf_false RationalTangles.TwistExpr.mulTop_comm_necessity RationalTangles.TwistExpr.mulTop_two_inner_ne_toStandard
proof: formalized
---

# Fixed points of the mulTop commutativity equation

The `mulTop` commutativity equation $(s^{-1}+F)^{-1}=(F^{-1}+s)^{-1}$ holds
exactly at $F=\pm 1$ (per sign, hence jointly): $0$ and $\infty$ fail by
direct computation, and for finite nonzero values injectivity of `inv`
reduces the equation to $q=q^{-1}$, i.e. $q^2=1$. Together with the
sufficiency direction, the unit-fraction hypothesis for `mulTop`
normalization is therefore both necessary and sufficient on finite
values — blocker (b) is closed on the finiteness fragment. The
necessity is sharp at expression level: on
`mulTop (addRight one pos) pos` (inner fraction $2$), algebraic $F$
is $1/3$ while the standard-form evaluation is $2/3$
(`mulTop_two_inner_ne_toStandard`), so the agreement hypotheses of
`twist_same_fraction_isotopic` cannot be dropped in general.

## Sources

- [Kauffman–Lambropoulou Definition 8](../../../../sources/kauffman-lambropoulou.md#definition-8)

## Depends on

- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
- [Standard form](../../definitions/standard-form.md)
