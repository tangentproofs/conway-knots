# About this site

**The theorem.** J.H. Conway, *An enumeration of knots and links, and some of their algebraic properties* (1970): two rational tangles are isotopic **if and only if** they have the same fraction. The proof followed here is Louis H. Kauffman and Sofia Lambropoulou, *On the classification of rational tangles*, Adv. Appl. Math. 33 (2004) 199–237 ([arXiv:math/0311499](https://arxiv.org/abs/math/0311499)). It computes the fraction by **integer colorings** of the arcs.

**The Lean.** [tangentproofs/conway-knots](https://github.com/tangentproofs/conway-knots): about 26,000 lines of Lean 4 on Mathlib (v4.32.2) in 32 files, by Michal Wallace, developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot). The project's own blueprint is the [project home](../).

**What it proves, in one paragraph.** Tangles are given as twist recipes (one crossing glued on at a time). If two top-product-free recipes have the same fraction, their diagrams are isotopic. That is the reconstruction half, proved through the unique canonical continued fraction. Every non-constant integer coloring of a (slideReady) twist diagram reads off the fraction (f = F). Fractions and coloring fractions are unchanged along a restricted, one-way set of moves (`ColoringIsotopy`). **Conway's theorem itself is not proved:** the two halves are about different move sets and don't combine into an "if and only if". See [the review](#/review).

**This site** reads the formal statements back into plain English, so you can judge whether they say what their names suggest. Each node is one Lean declaration with its verbatim Lean, a plain-English reading that leads with its most surprising point, faithfulness notes, and a short quiz. Tick **I think I understand this** when you do. The four headline theorems have step-by-step proof outlines linked to their exact lines.

The [Lean source](src/index.html) is on the site, highlighted. Names defined in the project link to their definitions, Mathlib names link to the Mathlib docs, and every "File.lean lines a–b" reference opens those exact lines.

Start with [the statements](#/start), then read the [review](#/review) and what was and wasn't [checked](#/trust).

Proof outlines and quizzes are summaries, not evidence: the Lean is the ground truth.

**Credit.** Theorem: J.H. Conway; proof followed: Kauffman and Lambropoulou. Lean: Michal Wallace with AutoformBot. Explanations: drafts by Grok Bot for Michal Wallace (`review: draft`), possibly wrong. Site engine: the tangentproofs proof-site kit (star-height, subexponential-sat).
