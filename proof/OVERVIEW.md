# Proof outline

The complete exposition is in [the paper](../paper/main.pdf), with editable
[LaTeX source](../paper/main.tex). This overview identifies the mathematical
steps and the corresponding Lean modules.

## Board and goal

Work in F = Z/23Z. A cell is a pair (r,c). Queens cover cells with the same
row r, column c, sum r+c, or difference r−c. An independent set has no repeated
label in any of these four projections. A dominating set occupies or covers
every cell. These definitions are in `Basic.lean`.

## Upper bound

The twelve queens are

```text
(2,13), (3,9), (6,3), (7,22), (9,2), (11,5),
(12,8), (15,18), (16,14), (18,7), (20,4), (21,0).
```

`Upper.lean` checks cardinality, independence and coverage by ordinary `decide`.
The small Python witness verifier is an additional finite check.

## Excluding ten queens or fewer

For a hypothetical dominating placement, enlarge each of its four projection
sets to ten field elements. The product of their four root polynomials after
substitution of x, y, x+y and x−y has degree at most 40 and vanishes on F × F.
Its coefficient of x²⁰y²⁰ is −252 = 1 in F. A finite-grid coefficient extraction
identity forces that coefficient to vanish, a contradiction.

`Grid.lean`, `Lift.lean` and `LowerTen.lean` prove this argument. The finite-field
power-sum identity used in coefficient extraction is the first native computation.

## Excluding eleven independent queens

Translate an eleven-queen placement so that its row and column sums are zero;
11 is invertible modulo 23. Independence makes all four projection sets have
eleven elements, and their sums are zero.

Write u and v for the second and third coefficients of each reversed root
polynomial. Vanishing of the degree-44 covering polynomial gives coefficient
equations. They imply uR = uC, uS = uD, and all four v values are zero.
The identity (r+c)²+(r−c)² = 2(r²+c²) gives uS = 2uR.

`RootCoefficients.lean`, `Kernels.lean`, `Expansion.lean`, `Equations.lean` and
`Geometry.lean` derive these necessary conditions from the board definitions.

Every possible eleven-element projection is represented by a 23-bit mask.
`ProfileEnumeration.lean` checks all 2²³ masks and certifies that every mask
with the required cardinality and coefficients occurs in `ProfileData.lean`.
`ProfileBridge.lean` proves that the executable coefficient recurrence matches
the actual polynomial coefficients.

For each compatible row, column and sum projection, consider the difference
labels d for which some cell (r,r−d) remains uncovered by the first three
directions. All 40,620,104 compatible triples require at least twelve distinct
difference labels. The proposed eleven-queen placement supplies only eleven.

`CoverCheck.lean` performs the closed native computation. `Masks.lean` and
`CoverSemantics.lean` prove the bit operations and counts express exactly the
required difference-label set. `Main.lean` derives the contradiction and combines
the lower bound with the explicit construction.

The candidate masks and their compatibility conditions are established inside
the formal argument. The final theorem has no unproved profile or algebraic
conditions as hypotheses.

## Trust and quantifiers

The complete theorem uses Lean's kernel-checked derivations together with three
`native_decide` results. Its axiom list explicitly includes the native computation
axioms. It concerns all independent dominating placements on the 23 × 23 torus,
and only that fixed board size.

The older paper proof and SAT-related records in `historical/` are supplementary
history. They are not inputs required by the current Lean proof.
