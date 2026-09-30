# Endpoint implementation iterations

This work implements a theorem **statement** and its concrete definitions.
The unconditional geometrization proof remains the team's subsequent task.

## Iteration 1 — fixed geometric models

* Added exactly eight model tags, five explicit normalized coordinate tensors,
  positivity/symmetry proofs, and metric-atlas bindings to the three existing
  PC-based model metrics.
* Defined actual local/global metric homogeneity and `GeometricStructure`,
  binding completeness, fixed-model charts and conditional finite volume to the
  same metric and carrier.
* Added a real Euclidean model consumer and source-formula checks.
* Source review: `ENDPOINT_SOURCES.md`; source bodies and three matrix-page
  images checked. No archive or accepted PC source changed.
* Validation: narrow module build, then the complete team gate passed:
  **131 modules, 3645 declarations**, with only the accepted standard axioms.
  This reused the audited local dependency cache. It is not a cold-machine
  build and does not prove the geometrization conjecture.
* The complete decomposition statement is the next increment; it is not yet
  present in this first increment.

## Iteration 2 — complete endpoint proposition

* Added actual primeness and oriented prime decomposition, compact closed or
  smooth-boundary cut carriers, exhaustive finite components, paired torus
  boundary data and its actual PC quotient.
* Added compatible smooth quotient interiors and signed seams, explicit
  boundary orientation reversal, and oriented reconstruction into each prime.
  Incompressibility is π₁-injectivity in that actual prime.
* Defined `GeometrizationCertificate`, `Geometrizes`, and
  `GeometrizationConjecture`; proved equivalence with the unbundled smooth
  statement and transport along an oriented diffeomorphism.
* Proved quotient interior fibers are singletons and torus images are embedded
  and pairwise disjoint. A real certificate consumer extracts a prime factor
  together with its geometric decomposition, ruling out empty-list vacuity.
* Full team build and axiom gate passed: **136 modules, 3905 declarations**.
  The proposition is fully defined, not asserted to be true. Concrete zero-cut
  certificate construction and the final semantic audit are the next iteration.

## Iteration 3 — canonical interiors and a complete sphere certificate

* Proved coframe linearity and metric-atlas transport for every model. Complete
  geometric structures, including their actual volume condition, pull back
  along diffeomorphisms with the required boundaryless source model.
* Normalized whole-piece interiors to PC's ordinary boundaryless atlas and
  proved the adapter from the original compact-carrier atlas. This resolves
  the precise source-model requirement of the volume-pullback theorem.
* Proved boundary/seam coverage and smooth embedded torus consequences in
  the exact reconstructed prime carrier, including two-sided seam charts.
* Constructed all zero-cut data for a closed geometric manifold and then a
  complete certificate for the actual standard lifted S³, using accepted PC
  to prove its primeness. This example has one prime, one piece and zero tori;
  it does not assume any endpoint producer.
* Completed the author's semantic/source audit in `ENDPOINT_AUDIT.md` and
  identified the remaining general producers without marking them complete.
* Final verification passed: `LEAN_NUM_THREADS=4 python3 tools/gc/check.py
  --verify-promotion`, **139 modules and 4009 audited declarations**, only
  `propext`, `Classical.choice` and `Quot.sound`. The frozen 123 promoted
  modules are unchanged. Receipt: `evidence/endpoint_final_verification.json`.
  Its precommit HEAD and dirty flag describe the checked worktree; its source
  hashes identify the exact Lean files subsequently committed.
* Blueprint consistency also passed: 13 guard groups, 3319 rejection controls,
  and `audit_blueprint.py`. No TeX revision or new PDF build was needed.

The complete statement-and-foundations milestone is ready for team review.
The universal geometrization proof, general cut/gluing producers and the
remaining global model realization lemmas are subsequent work.
