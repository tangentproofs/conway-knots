---
declaration: def
origin: cited
statement: formalized
lean: RationalTangles.integerTangle RationalTangles.verticalTangle RationalTangles.verticalTwists
---

# Integer and vertical tangles

The simplest rational tangles are $[0]$, $[\infty]$, $[+1]$ and $[-1]$. The
next simplest are:

- the **integer tangles** $[n]$, made of $n$ horizontal twists, $n\in\mathbb{Z}$;
- the **vertical tangles** $[n]^{-1}$, made of $n$ vertical twists,
  $n\in\mathbb{Z}$.

Crossing type follows the checkerboard shading of the paper (Figure 2):
positive type as in $[+1]$, negative type as in $[-1]$. These sign conventions
agree with Ernst–Sumners and are the *opposite* of Conway 1970; this project
follows Kauffman–Lambropoulou.

In particular $[0]^r=[0]^i=[\infty]$ and $[\infty]^r=[\infty]^i=[0]$, and
$-[n]=[-n]$.

The stacked diagram of $|n|$ vertical twists below $[\infty]$ is the
right-and-bottom picture of Conway $[n]^i=1/[n]$. It is not the PD-code
of inverting $[n]$, which mirrors every crossing.

## Sources

- [Kauffman–Lambropoulou §2, Figure 2](../../../sources/kauffman-lambropoulou.md#source-map)

## Depends on

- [2-tangle and isotopy](two-tangle-isotopy.md)
