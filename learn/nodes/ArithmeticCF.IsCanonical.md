---
id: ArithmeticCF.IsCanonical
title: 'Canonical continued fraction: odd length, one sign'
summary: '**The surprise:** each rational has many continued fractions, but exactly one that has odd length with
  all terms the same sign, and that''s the tangle''s normal form.'
review: draft
authors:
- grok-bot
quiz:
- q: Which is canonical?
  type: choice
  choices:
  - '[1, 1, 3]'
  - '[1, 1]'
  - '[2, −1, 3]'
  answer: 0
  explain: Odd length, one sign.
- q: Is [2, 1] canonical?
  type: choice
  choices:
  - No, even length
  - 'Yes'
  answer: 0
  explain: Length 2 is even. Its value is 2 + 1/1 = 3, whose canonical form is [3].
- q: Can ∞ have a canonical expansion?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: '`isCanonical_value_ne_inf`.'
---
## Plain English

**Definition (`ArithmeticCF.IsCanonical`, CanonicalForm.lean lines 24-26).** A continued fraction [a₁, …, aₙ] ([`ArithmeticCF`](#/node/ArithmeticCF)) is canonical when n is odd and all terms are ≥ 0 or all are ≤ 0. Example: 7/4 = 1 + 1/(1 + 1/3) = [1, 1, 3].
