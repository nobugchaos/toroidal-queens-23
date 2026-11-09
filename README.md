# Independent domination on the 23 × 23 toroidal queens board

[中文说明](README.zh-CN.md) · [Paper (PDF)](paper/main.pdf) · [Proof outline](proof/OVERVIEW.md) · [Lean theorem](formal/ToroidalQueens23/Main.lean)

This project proves the fixed-instance result

$$i(Q_{23}^{t})=12.$$

Twelve mutually nonattacking queens can occupy or attack every cell of the
23 × 23 board with opposite edges identified. Every independent dominating
placement on this board contains at least twelve queens.

**Author:** Weixin Yu, Independent Researcher · iweixin1214@gmail.com

The result has a complete Lean 4 formalization with three explicitly disclosed
`native_decide` computations. The project does not claim a general formula for
other board sizes, historical priority, external peer review, or an arXiv submission.

## Build and check

Install [elan](https://github.com/leanprover/elan), Git, and a working C compiler
supported by Lean. The toolchain is pinned by `formal/lean-toolchain`.

```sh
git clone https://github.com/nobugchaos/toroidal-queens-23.git
cd toroidal-queens-23/formal
lake update
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean SemanticAudit.lean
```

Lean is pinned to **4.34.0**, and mathlib to commit
[`5ed2965256430c3649e86755f9576b54eca72435`](https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435).
The cache command downloads compiled dependencies; the project's own finite
computations run during `lake build`. Allow several minutes for them.
If the dependency cache is unavailable, dependencies can be compiled normally.

For quick source and witness checks, using Python 3.10 or newer:

```sh
python scripts/check_sources.py
python scripts/verify_witness.py
```

The [GitHub Actions workflow](.github/workflows/lean.yml) builds from the portable
configuration and runs the theorem, axiom, semantic, source, and witness checks.
Its live status is separate from the saved local verification evidence.

## What Lean proves

The definitions in [`Basic.lean`](formal/ToroidalQueens23/Basic.lean) use
`ZMod 23 × ZMod 23`. Two squares lie on a queen's line exactly when their row,
column, coordinate sum, or coordinate difference agrees modulo 23.

The principal declarations in [`Main.lean`](formal/ToroidalQueens23/Main.lean) are:

| Declaration | Statement |
|---|---|
| `independent_dominating_card_at_least_twelve` | Every independent dominating set has cardinality at least 12. |
| `minimum_is_twelve` | A 12-element placement exists, and all such placements have at least 12 elements. |
| `independentDominationNumber_eq_twelve` | The minimum attainable cardinality is exactly 12. |

These final statements assume the board definitions, without taking polynomial
constraints, candidate-table membership, or a solver's result as premises.
[`SemanticAudit.lean`](formal/SemanticAudit.lean) also restates the result using
pairwise distinct line labels and the explicit requirement that each cell is
occupied or attacked by a different queen, and proves equivalence to the definitions.

## Computation and trust

No `sorry`, `admit`, or manually declared axiom occurs in the proof source.
The twelve-queen witness is checked by ordinary `decide` and depends only on
Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The complete minimum theorem additionally depends on these three native computations:

| Declaration | Closed computation |
|---|---|
| `powerSum_table` | The finite-field power sums for exponents 0 through 88. |
| `all_profile_masks_checked` | All 8,388,608 masks, establishing candidate-table completeness. |
| `all_profile_covers_checked` | All 23 coefficient groups and 40,620,104 candidate triples. |

These use Lean's native compiler and runtime. Their three generated native axioms
are listed by `Audit.lean`; the complete theorem therefore has a larger trust
base than standard axioms and kernel reduction alone. Python outputs and historical
SAT/LRAT certificates are not premises of the Lean theorem.

## Verification evidence

The distributed proof was extracted to a new project directory and all 17 proof
modules plus the root module were rebuilt successfully: **1492 jobs**, approximately
983 seconds on the development machine. All three native computations were rerun.
The dependency sources were compared against their retained pinned archives;
compiled dependency caches were reused. This local run was not a fresh network bootstrap.

See [`evidence/recheck-2026-11-09`](evidence/recheck-2026-11-09) for the fresh build,
axiom audit, semantic audit, and dependency comparison. Earlier logs remain in
`round3/` as historical evidence. A summary describes the exact checks and limits.

## Files

| Path | Contents |
|---|---|
| `formal/` | Portable Lake project, all proof modules, candidate data, and audit files. |
| `paper/` | Nine-page English preprint and self-contained LaTeX source. |
| `proof/` | Readable explanation of the proof and its connection to Lean. |
| `data/witness.json` | Explicit twelve-queen placement, with zero-based coordinates. |
| `scripts/` | Lightweight source, axiom-list, and witness checks. |
| `evidence/` | Dependency locks and fresh verification records. |
| `literature-check/` | Dated literature checks and their limits. |
| `historical/`, `round2/`, `round3/` | Preserved earlier proofs, data, generators, and audit records. |
| `provenance/` | Original bundle manifest and publication transformations. |

Large historical LRAT archives and compiled `.olean` files are excluded. Neither
is needed to rebuild the complete Lean theorem. Dependency sources are obtained
from their upstream repositories rather than vendored here. Local machine paths
in published records are redacted; provenance records distinguish original and
published hashes. Original Lean proof files are unchanged.

## Literature status

The public sources inspected through November 8, 2026 did not reveal an earlier
proof of this same exact value. The retrieved [OEIS A279404](https://oeis.org/A279404)
entry listed values through order 21. The 2001 and 2003 toroidal queens papers
were checked for applicable constructions and exact-value statements.

This is a bounded literature search, not a priority certification. Some sources,
including a subscription survey chapter, were not available in full. See the
[literature report](literature-check/2026-11-08/REPORT.txt) and
[follow-up search](literature-check/2026-11-08/FOLLOWUP_SEARCH.txt).

## Citation and licensing

Author and project metadata are provided in [CITATION.cff](CITATION.cff).
No DOI or arXiv identifier has been assigned. No project-wide redistribution
license has been selected; upstream dependencies retain their own licenses.
