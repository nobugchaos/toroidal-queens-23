Toroidal queens, board size 23: complete Lean formalization

From this directory, using elan and Git:
  lake update
  lake exe cache get
  lake build
  lake env lean Audit.lean
  lake env lean SemanticAudit.lean

Lean: 4.34.0.
mathlib: 5ed2965256430c3649e86755f9576b54eca72435.
The root README.md explains the complete theorem, trust, computation and evidence.
The three native_decide computations run during the project build.
The dependency cache is optional; ordinary dependency compilation also works.

The 17 proof modules and root were rebuilt from the delivered source in a fresh
local project. Dependency sources were compared to pinned upstream archives and
compiled dependency objects were reused. All three native computations ran anew.
The additional SemanticAudit.lean proves equivalence to the explicit physical
board conditions. Its theorem and all proof modules passed Lean kernel replay.
Native computation axioms remain part of the trust base after kernel replay.

Fresh records: ../evidence/recheck-2026-11-09/.
The portable configuration is committed; no local absolute dependency path is
needed. No standard-axioms-only, external-peer-review or priority claim is made.
