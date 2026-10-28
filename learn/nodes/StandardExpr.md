---
id: StandardExpr
title: 'Standard form: right additions and bottom products'
summary: '**The surprise:** standard forms are continued fractions in disguise: runs of right additions are the
  terms, and each bottom product starts a new level.'
review: draft
authors:
- grok-bot
quiz:
- q: Which steps are allowed?
  type: choice
  choices:
  - Right additions and bottom products
  - All four
  - Only additions
  answer: 0
  explain: 'Constructors: zero, infinity, addRight, mulBottom.'
- q: Can a standard form start from [+1]?
  type: choice
  choices:
  - 'Yes'
  - 'No: it starts from [0] or [∞]; [+1] is [0] + [+1]'
  answer: 1
  explain: There is no `one` constructor.
- q: Is every standard form slideReady and noMulTop?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: Neither condition restricts right additions or bottom products.
---
## Plain English

**Definition (`StandardExpr`, StandardForm.lean lines 22-27).** Start from [0] or [∞]; then add [±1] on the right or multiply [±1] at the bottom, repeatedly. That is Kauffman–Lambropoulou's Definition 4.
