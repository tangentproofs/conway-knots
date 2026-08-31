---
declaration: lemma
origin: cited
statement: formalized
lean: RationalTangles.coloring_affine RationalTangles.ColorMatrix.fraction_affine
proof: formalized
---

# Affine freedom of coloring

If $\alpha\mapsto n\alpha+k$ is applied to every arc color of a coloring of
a 2-tangle, for $n,k\in\mathbb{Z}$, the result is again a coloring. In
matrix form, if $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ is a color matrix
then so is
$$
M'=\begin{pmatrix}na+k&nb+k\\nc+k&nd+k\end{pmatrix}.
$$
Indeed, $\gamma=2\beta-\alpha$ implies
$n\gamma+k=2(n\beta+k)-(n\alpha+k)$.

Consequently the starting colors of a rational tangle may be taken to be
$0$ and $1$, at the cost of an affine transformation of this type. For
$n\neq 0$ the coloring fraction is unchanged:
$(nb+k-(na+k))/(nb+k-(nd+k))=(b-a)/(b-d)$.

## Sources

- [Kauffman–Lambropoulou, affine freedom](../../../../sources/kauffman-lambropoulou.md#color-matrix)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Color matrix](../definitions/color-matrix.md)
