# Endpoint specification audit — 2026-09-28

The statement-and-definitions milestone is implemented. The universal
geometrization theorem is **not proved**. This is the author's source/semantic
review plus Lean verification of the declarations and example, not an
independent team review or a formal equivalence with every textbook convention.
T01 is offered for team review; T09's general producer remains open.

Current207 update: the five coordinate metrics, homogeneity and completeness
are proved. Revisions205–206 also prove arbitrary smooth endpoint transport,
bounded actual-history descent and full endpoints for PC's standard factors.
The raw terminal consumer needs only actual empty observation; the late
consumer retains same-tower LateComponentSupply. General controlled analytic
production, relative graph realization and the universal theorem remain open.
See INTERFACE_ITERATION203–206 and MODULE_PLACEMENT.json for current paths.
No stronger protected-port or decorated-history export is inferred.

## Mathematical contract review

| Requirement | Concrete binding and review result |
|---|---|
| Closed connected orientable smooth dimension three | `ConnectedClosedOrientedManifold 3`; equivalent unbundled statement quantifies over an actual supplied orientation. No flow hypothesis occurs. |
| Genuine prime factors | `IsPrime` quantifies over PC's actual smooth connected sums and requires a sphere summand in every factorization. No group-theoretic surrogate replaces primeness. |
| Finite nonempty prime list | `PrimeDecomposition.factors_nonempty`; an actual oriented diffeomorphism from PC `finiteConnectedSum factors` to the input. Repeated slots remain distinct; S³ is an allowed unit prime. |
| Compact cut carriers and all pieces | Actual compact Hausdorff smooth manifolds with exactly Euclidean or half-space models, a finite exhaustive clopen connected partition, and nonempty connected whole interiors. No higher-codimension corner model or selected-subset metric domain. |
| Actual torus sides and matching | Standard `Circle × Circle`, homeomorphic parametrizations of disjoint boundary subsets, smooth half-collars agreeing at height zero, actual smooth torus matching maps agreeing with PC gluing, and exhaustive boundary coverage. |
| Smooth orientation reversal | Ambient orientations pulled back through the two inward collars differ by a sign, including the specified matching map. This is the normal-first reversal convention; the quotient inclusion preserves ambient orientation on each side. |
| Actual glued carrier | The underlying space is the quotient of the cut carrier by the specified PC boundary relation, with its quotient topology. It is not assigned to be the final prime. |
| Compatible smooth structure | Actual smooth quotient map, exact interior diffeomorphism, signed seam charts agreeing with both half-collars, and oriented quotient-to-prime diffeomorphism. Interior/seam coverage follows from the boundary exhaustion and quotient relation. |
| Embedded, two-sided, disjoint tori | New theorems prove quotient torus embeddings and pairwise disjointness. `torusInPrime_smooth`, `torusInPrime_isEmbedding`, and `primeSeam` bind smoothness and two-sided charts to the exact reconstruction map. |
| Ambient incompressibility | Actual induced fundamental-group maps of those torus embeddings into the reconstructed prime, at every basepoint. Model-peripheral injection is not substituted. |
| Fixed eight geometries | Exactly eight tags. Round, Euclidean and round-cylinder reference metrics reuse PC; the other five local tensors are explicit normalized coframes, with checked linearity, symmetry and positivity. Callers cannot supply their own geometry predicate or reference tensor. |
| Complete whole-interior geometry | Every component's entire intrinsic interior has a smooth metric in PC's ordinary boundaryless interior atlas, with completeness and the exact fixed-model atlas. The metric is not restricted to a compact core. |
| Precise volume policy | The same metric's actual Riemannian measure of the whole interior is finite whenever the model is hyperbolic. No blanket finite-volume restriction on other models. |
| Marked reconstruction | Boundary-side ownership, matching maps, quotient map, prime reconstruction and the final oriented connected-sum map are all retained. Transport changes only the final marking. |

The source translation is documented in `ENDPOINT_SOURCES.md`. Martelli's
canonical finite-volume geometric decomposition is not silently equated with
the blueprint's potentially finer E1 torus-only endpoint. JSJ uniqueness is not
required. Both later Ricci-flow outcomes can target this flow-independent
certificate; no finite-extinction hypothesis has been added to the general
statement.

## Executed semantic checks

* Coframe linearity, injectivity, symmetry and positive-definiteness proofs
  rule out degenerate or nonlinear reference forms in the five coordinate models.
* `interior_fiber_singleton` excludes interior identifications. The explicit
  gluing relation and block disjointness prevent different paired blocks from
  merging; torus embeddings and disjointness are proved.
* `boundary_maps_to_torus` and `interior_or_torus` exclude unrecorded quotient
  points or boundary components. `descend` and uniqueness expose the actual
  quotient's universal reconstruction map.
* `interiorGeometryOfOriginal` uses PC's actual interior diffeomorphism and
  metric/volume pullback to discharge the boundary-atlas interface, preserving
  completeness and finite volume on the whole carrier. The source-model
  boundarylessness hypothesis of PC volume pullback is met by the ordinary
  interior atlas, not silently dropped.
* `NoCuts.geometricDecomposition` constructs the entire zero-torus cut package
  from a closed geometric manifold. It proves compatibility of the canonical
  empty-pairing quotient's smooth structure and orientation with the original
  carrier; it does not infer primeness from mere geometricity.
* `sphereCertificate` constructs a complete endpoint certificate for the
  actual universe-lifted standard S³: one prime factor, one geometric piece,
  zero tori, and both smooth oriented reconstructions. Its primeness proof
  reuses accepted PC and the connected-sum fundamental-group theorem.
  `standardThreeSphereLift_geometrizes` has no endpoint-production assumption.
* Downstream checks use the public statement and real sphere certificate;
  they also extract an actual prime factor and its geometric decomposition
  from any certificate, excluding empty-list vacuity.

These checks establish meaningful examples and consequences. They do not
establish existence of such a certificate for arbitrary manifolds.

## Remaining implementation work and producer boundaries

| Consumer of the new interface | Still-required general work |
|---|---|
| `PrimeDecomposition`, component ownership and reconstruction | T08: general relative prime refinement and essential cuts. Bounded smooth history descent is proved; T03's stronger port/cycle/decorated exports remain separate. |
| `SmoothAssembly` with nonzero torus count | T03/T08: bind actual topological constructions to this wrapper; prove the corresponding general gluing/cut producers. A nonzero-torus worked example is a useful next integration test. |
| Complete structures on general geometric pieces | T08: general Seifert/hyperbolic cut-piece realization and exact model transports. The five coordinate metrics, transitive actions and completeness are proved; actual standard-factor endpoints are also proved. General quotient/interior producers remain open. |
| Actual incompressible late interfaces | T06/T07: persistence and ambient cusp incompressibility on the actual flow carriers. |
| Universal certificate production | T02/T04–T09: controlled global flow, local/static collapse, actual thick/thin and ambient/relative geometry supplying the same-tower late obligation. The empty-observation endpoint consumer is proved; actual emptiness is not asserted for all flows. |

The new definitions do not declare these producer tasks complete. Ziyang can
refactor the wrappers or implementation while preserving the mathematical
conditions; there are no permanent ownership assignments or extra service
requirements imposed by this work.

## Historical initial verification scope

Narrow model, transport, topology, statement, zero-cut and sphere modules have
elaborated successfully. The final full team gate passed with **139 modules
and 4009 audited declarations** using `LEAN_NUM_THREADS=4 python3
tools/gc/check.py --verify-promotion`. Its receipt is stored in
`evidence/endpoint_final_verification.json`; iteration 2's receipt is retained
separately. The final gate includes the original-promotion comparison, full
library/check targets, and collection of transitive axioms for all owned
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` were used.
No proof placeholders or custom mathematical axioms were introduced.
The receipt records the precommit HEAD and exact checked Lean source hashes.

The existing blueprint reference inventory/manifest link the new source check.
Their locator-only changes required refreshing the specification-guard receipt;
the prior receipt was preserved. All 3319 rejection controls passed, followed
by `audit_blueprint.py`. These are static consistency checks, not mathematical
proofs. The blueprint TeX files remain revision202; no new PDF or Overleaf build
was performed. Lean builds reused the accepted local dependency cache; a cold
machine build and full Lean CI rollout were not performed.
