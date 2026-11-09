Fresh proof verification, finalized 2026-11-09

PASS: 71 original bundle entries checked against their manifests.
PASS: all 19 original proof/audit source files match the delivered ZIP.
PASS: fresh rebuild of all 17 library modules and the root, 1492 jobs.
PASS: all three native computations rerun (8,388,608 masks; 40,620,104 triples;
      finite-field power sums for exponents 0..88).
PASS: exact final axiom lists, with no sorryAx and the disclosed native axioms.
PASS: the additional semantic-equivalence proof and ordinary boundary examples.
PASS: Lean kernel replay of the 17 proof modules plus the semantic audit.
PASS: 9816 dependency source/configuration files across nine fixed packages
      match retained upstream archives, with no extra Lean source files.

The fresh project began without project build objects. Its dependency locations
were changed to existing fixed local dependencies in that copy only. Compiled
dependency caches were reused. This local audit is not a clean network bootstrap.
The public portable configuration is checked separately by GitHub Actions.

The kernel replay checks proof declarations and still accepts the three native
computation axioms. It does not eliminate native compiler/runtime trust and is
not an independently implemented proof checker or external peer review.

The additional semantic-audit examples initially lacked unfolding/recursion
settings; a runner then needed UTF-8 console output. The corrected additional
file and its final log pass. No original Lean proof module was modified.
