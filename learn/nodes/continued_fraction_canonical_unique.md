---
id: continued_fraction_canonical_unique
title: Canonical continued fractions are unique
summary: '**The surprise:** uniqueness here is literal equality of lists, so two canonical tangle diagrams of the
  same value are the same PD-code, with no isotopy needed.'
review: draft
authors:
- grok-bot
quiz:
- q: What does it conclude?
  type: choice
  choices:
  - cf₁ = cf₂
  - Isotopic cf₁.tangle cf₂.tangle
  answer: 0
  explain: Equality, which is stronger.
- q: Does it involve diagrams?
  type: choice
  choices:
  - No, pure arithmetic
  - 'Yes'
  answer: 0
  explain: It is about lists of integers.
- q: Can a canonical expansion have value ∞?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: That case is excluded.
---
## Plain English

**Theorem (`continued_fraction_canonical_unique`, ContinuedFractionCanonical.lean lines 885-893).** Two [canonical](#/node/ArithmeticCF.IsCanonical) continued fractions with the same value are equal. Kauffman–Lambropoulou's Proposition 3. Both equal `canonicalCF q`, built by an 'oddified' Euclidean algorithm.
