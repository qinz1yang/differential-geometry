# Revision203 source and contract check

# Revision 203 — complete coordinate metrics and conditional assembly

The current user priority is a bounded, reviewed network of concrete Lean
interfaces around the existing mathematical DAG. The general geometrization
proof and the complete semantic premise census remain open. No task is released
as a complete chapter merely because its interface compiles.

## Checked mathematical increment

`Geometry/Models/CoordinateMetrics.lean` constructs the five fixed coordinate
metrics as actual PC smooth Riemannian metrics, proves their exact tensors, and
binds the endpoint's coordinate atlas to the existing actual-metric atlas.
`CoordinateHomogeneity.lean` constructs explicit smooth affine diffeomorphisms
between any two points and proves preservation of each coframe and metric.
`HomogeneousCompleteness.lean` proves completeness using transitive isometries
and compact neighborhoods. No curvature classification or completeness premise
is assumed. It supplies whole-model geometric structures for H²×R, the
universal-cover SL₂ tensor, Nil and Sol. The hyperbolic metric is complete, but
the whole hyperbolic model is not asserted to meet finite volume.

`Endpoint/Assembly.lean` proves:

* `GeometrizationCertificate.connectedSum`: concatenate the literal prime
  slots and retain the per-slot cut/metric data, composing actual oriented
  connected-sum maps. Repeated types remain separate slots.
* `geometrizes_finiteConnectedSum`: assemble any finite family whose members
  geometrize. The empty list uses the actual sphere certificate.
* `MarkedFactorReconstruction`: an exact proposition requiring an oriented
  diffeomorphism from PC's finite connected sum to the input manifold.
* `geometrizes_of_markedFactors`: consume that map and geometric certificates
  for all factors to obtain the public endpoint on the input manifold.

The last theorem is **conditional**. Its missing map is not constructed from
an arbitrary surgery history. No port compatibility, discarded-factor
classification, terminal geometry, or controlled-flow theorem is inferred from
the composition. The same distinction applies to the task cards T08/T09.

`GeometrizationChecks/AssemblyConsumers.lean` builds real Nil and Sol structures,
uses hyperbolic completeness without asserting finite volume, assembles two
sphere certificates with two distinct prime slots, tests the empty family, and
consumes the exact marked reconstruction proposition.

## Source and interface review

Model formulas and normalization reuse the verified archive records in
`ENDPOINT_SOURCES.md`: Martelli v4 (September 2025), Prop.2.1.23 and proof
printed54–55/PDF62–63; §12.4 printed385–386/PDF393–394; §12.5.1–2
printed388–389/PDF396–397; Lemma12.6.1 and proof printed394–396/PDF402–404,
§12.6.3 printed397/PDF405; §12.7.1 printed398–399/PDF406–407. The Nil group law
and left-translation construction and the SL₂ metric derivation were reopened.
The existing same-day author/errata checks and limitations remain applicable;
no newly corrected edition is substituted. The affine transitivity and compact
neighborhood completeness arguments are new proofs of these explicit models,
not a citation to an unformalized classification theorem.

Accepted PC v0.1.3 at `7a48598d35109aa99d1cc678e2724c213cdf4ff3` is unchanged.
Bodies/signatures used in this iteration:

* `Geometry/Metric/Construction/Existence.lean:23`: positive finite-dimensional
  bilinear forms have the required bounded unit ball.
* `Geometry/Metric/PullbackCompleteness.lean:51`: exact Riemannian extended
  distance equality under a genuine cross-model diffeomorphism pullback.
  Its path-integral proof was inspected; it does not assume completeness.
* `Topology/ThreeManifold/ConnectedSum/Finite.lean:11`: actual finite-sum
  constructor, including empty/singleton/multiple cases.
* `ConnectedSum/SumLaws.lean:98`: append theorem and its full induction,
  including unit and association maps.
* `ConnectedSum/OrientedTransport.lean:137–152`: orientation-preserving chart
  transport and the actual oriented transport export.
* `ConnectedSum/OrientedLawsAssembly.lean:12–19` and
  `ConnectedSum/FiniteCongruence.lean:12–35`: accepted producers and finite-sum
  adapters. These export genuine oriented maps, not just homeomorphisms.

Pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` reuse:
`Geometry/Manifold/Riemannian/Basic.lean:103–125` for vector-space bundle-section
smoothness; `Topology/EMetricSpace/Basic.lean:98` for the Cauchy-filter criterion;
`Topology/EMetricSpace/Defs.lean:516` for metric neighborhoods;
`Topology/UniformSpace/Cauchy.lean:36,745` for complete sets and compactness;
and `Topology/MetricSpace/Isometry.lean` for actual distance-preserving maps.
The new proof works with extended metrics and does not silently assume finite
distance or a global lower Euclidean metric bound.

## Existing DAG correspondence and next interface work

The current-view overlay of the existing blueprint DAG links GA06 to the
bounded model proofs, GA14 to the certificate definition, GA22 to conditional
finite-family assembly and GA23 to the public proposition and sphere example.
None of those parent nodes is promoted to accepted. The recorded consumers
are actual compiling Lean uses; this is not a complete census of their premises.

Next, review and expose the actual observed-history interface: final-stage
components, discarded components, cycle factors, the initial identification,
and port/boundary compatibility. Do not replace it with an arbitrary family
having the desired output. Bind both late and terminal alternatives to the
same initial manifold, then expose one controlled profile before analytic time
choices. Shared collapse/persistence/incompressibility/refinement interfaces
follow in dependency order. The user explicitly prefers this interface work
before assigning large independent chapter implementations.

## Verification

All new production modules and the downstream consumers passed their narrow
Lean builds. `LEAN_NUM_THREADS=4 python3 tools/gc/check.py --verify-promotion`
then passed: 144 modules, 4157 audited declarations, only propext,
Classical.choice and Quot.sound. All 123 promoted baseline/vendor modules are
unchanged. Receipt: `evidence/iteration203_verification.json`, retaining the
precommit HEAD/dirty flag and exact Lean source hashes. No general geometrization
theorem, full DAG semantic acceptance, or cold-machine build is claimed.

Archive identities and source hashes remain those in reference_checks_endpoint_statement_20260928.md. The detailed source/contract comparison above is mirrored into the shared private repository. No archive source or accepted PC file was changed.
