# Revision 205: smooth reconstruction feeds the full endpoint

The endpoint definition is unchanged. This increment proves that an arbitrary
smooth diffeomorphism transports its full certificate, then uses the existing
actual smooth surgery reconstruction to remove revision204's extra oriented
event-refinement premise from the endpoint consumer. It does not prove that
stronger refinement or its protected-port extensions.

## Proved transports and compositions

`Topology/Endpoint/OrientationTransport.lean` reverses the orientations of the
prime factors, compact cut carriers and assembled quotients. The actual torus
parametrizations, gluing maps, collars, charts, ownership, interior metrics,
completeness, volume condition and torus maps into the primes are unchanged.
The two orientation equations follow from `Orientation.map_neg`. The accepted
finite-sum opposite law supplies the oriented global reconstruction. Prime
slots and multiplicities are retained. No model isometry reversing orientation
is assumed. The existing metric-chart definition imposes no orientation sign.

`geometrizes_of_diffeomorph` applies PC's orientation dichotomy on a connected
carrier, using the opposite certificate when needed. Actual component
restrictions handle disconnected carriers component by component. An empty
component predicate is vacuous, as before.

`Topology/Reconstruction/SmoothEndpointDescent.lean` consumes the actual
`CutCapSumData`: literal capped-component lists, multiplicities and stored smooth
reconstruction. Actual retained/discarded comparisons give geometry on each
capped slot; finite-family assembly and smooth transport give the source
component endpoints. `componentsGeometrize_of_cutCap` obtains the reconstruction
from its existing producer. No proposed oriented refinement is a premise.

`StandardFactorEndpoints` is the exact remaining proposition that every PC
`isStandardFactor` has the full endpoint: its actual oriented spherical space
forms and sphere-product models. **This proposition is defined, not proved.**
The consumer `geometrizes_of_poincareStandard` handles the actual smooth PC
presentation, including its literal factors and empty-list convention. The
cycle adapter uses the exact universe-lifted sphere product appearing in the
actual reconstruction, with its accepted orientation comparison.

`Endpoint/RawHistoryAssembly.lean` proves backward descent on an actual observed
history, then uses the raw tower's existing event controls to supply completion
and discarded-component classification on every observation. PC's restriction
proofs ensure these refer to the same actual events. The original
`InitialIdentification.map` transports the resulting endpoint to the initial
manifold; its metric identity remains available but asserts no analytic bound.

`geometrizes_of_raw_standard_late` has two open producer hypotheses:

- `StandardFactorEndpoints` as above.
- `LateComponentSupply F.observation` on the **same** raw tower, with one
  threshold preceding all later regular nonempty observations.

The existing late-nonempty/absorbing-empty dichotomy supplies the observation.
The terminal consumer uses only standard-factor realization and actual
emptiness. No late supply, reconstruction hypothesis or extinction theorem is
required in that branch. The late supply remains a coarse output obligation
to refine through a common controlled profile and actual geometric producers.

`GeometrizationChecks/SmoothHistoryConsumers.lean` compiles the actual
`RawSurgery.ofInitial` use, the terminal use, and an opposite-oriented sphere
through the actual zero-event history without any event, standard-factor or
late premise. A repeated two-sphere certificate still has two prime slots.

## Source review

Accepted PC v0.1.3 at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`, Lean4.33.1,
and the pinned Mathlib are unchanged. Exact file hashes and inspected intervals
are in `evidence/iteration205_sources.json`. Source bodies checked include:

- `Manifold/DiffeomorphOrientationDichotomy:11-40` and
  `OrientationDiffeomorphTransport:190-263`: connected-target hypothesis,
  push-forward orientation and one-point-to-global comparison.
- `Manifold/Orientation:35-80,240-297`, `ClosedOriented:1-85`, Mathlib
  `LinearAlgebra/Orientation:134-141`: opposite orientations and negation.
- `ConnectedSum/FiniteLawInstances:1-48`, `FiniteLaws:203-215`,
  `SumLaws:198-223`, `OppositeSumOrientation:184-203`: actual finite-sum opposite
  producer, including the empty sphere and singleton cases. The earlier body
  of the binary orientation construction is inherited, not freshly reaudited.
- `Manifold/ComponentDiffeomorph:1-90`, `DisjointUnion:1-37`,
  `DisjointUnionComponent:1-89`: actual maps, component inclusions and
  orientation comparisons.
- `ThreeManifold/PoincareStandard:1-100`, `StandardFactors:530-609`,
  `SphereTwoTimesCircleLift:1-110`, `PoincareStandardModels:1-37`,
  `CappedPoincareStandard:1-83`, `CutCapPoincareStandard:1-99`: exact model,
  classification and reconstruction conventions. Standard classification is
  not itself a full prime-and-geometric endpoint certificate.
- `Surgery/Topology/RetainedCorePresentation:175-252`: actual completion and
  classification restricted to an observation. Existing GC event control,
  actual event geometry, coherent tower and reconstruction bodies are reused
  unchanged; revision204's initial-marking source checks remain applicable.

Scott's archived 1983 paper was reopened at printed403/PDF3 (metric definition),
462,465/PDF62,65 (the orientation components of the SL2-cover isometry group),
and467-469/PDF67-69 (Nil and its metric/isometries). SHA256:
`98387f6fecebfd93f8d0c4f6b43df711ce71d5753364ce9b1f58135ad80147c5`.
This confirms the existing revision104 distinction between manifold orientation
and metric charts. No change to that definition or claim of a model reflection
is needed. Revision104's publisher check is reused; its inaccessible author
errata remains an explicit limitation, not an absence-of-corrections claim.

The unchanged Kleiner-Lott reconstruction/discard route reuses revision204's
source reading: archived February20,2013 version, Lemmas67.5/67.13/73.4 and
Definition73.1/Remark73.3, printed2740-2741,2745,2760-2762/PDF154-155,159,174-176.
Archive SHA256 `55a24f25c1b7cfc793706b9b6b937fefbbd6030755f7c3d6f56878d7c60b1f1b`.
That increment's author-index check and revision181's author-copy comparison
are reused with their stated limits; no fresh external PDF comparison is claimed.
The BooksPapers archive is unchanged. Morgan-Tian remains the global spine.

## Audit boundary and next work

The same actual smooth map is used for endpoint transport. It is not asserted
to preserve the originally prescribed factor orientations. Neither the
stronger `OrientedEventReconstruction` existence nor protected ports, a
prescribed cycle comparison, a flattened decorated history or torus maps into
the original manifold is proved here. Those DAG obligations remain separate.
All old DAG dependencies and parent acceptance states are preserved; new
bindings identify partial results and compiling consumers. T03/T09 remain
open and unclaimed. There is no second tracking system.

Next produce the classified-factor endpoints, and refine the late obligation
through one global controlled profile and the shared collapse, persistence,
incompressibility and relative-refinement interfaces. Do not infer analytic
control from raw tower coherence or spend this phase expanding unrelated model
examples. General geometrization and the semantic premise census remain open.

All four new modules passed narrow builds. The full team gate and document
checks are recorded in the accompanying receipts. These distinguish kernel
checking and axiom evidence from mathematical adequacy and missing producers.
No cold-machine build, Overleaf run or independent teammate acceptance is claimed.

Full team gate passed:151 modules,4269 audited declarations, only propext,
Classical.choice and Quot.sound. All123 promoted modules and PC pins remain
unchanged. The receipt records exact Lean source hashes, the precommit parent
HEAD and dirty flag; it used accepted caches. A final contract audit checked
carrier identity, componentwise orientation signs, unchanged metrics and torus
maps, literal slots, zero/empty histories and the same-tower threshold order.
