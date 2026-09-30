# Revision 206: actual standard-factor endpoints

`GC.Endpoint.standardFactorEndpoints` now proves the proposition that
revision205 left open. It produces full certificates for the actual PC
spherical space forms and sphere products, with no additional primeness,
metric, reconstruction or endpoint premise. The public endpoint is unchanged.

## Proof and consumers

`Topology/Endpoint/StandardPrimes.lean` first proves that nonidentity letters
from different free-product factors do not commute. Their reduced two-letter
words have different first indices. Mathlib's actual `Word.equiv` proves
uniqueness; PC's indexed/binary equivalence retains both universe lifts.
Consequently a commutative binary free product has a trivial factor. The
finite-group case reuses revision192's arbitrary-length reduced-word proof.

`isPrime_of_freelyIndecomposable` works on the actual smooth PC connected sum.
Given a smooth map P to A#B, its fundamental-group isomorphism, the explicit
basepoint-change isomorphism and PC's actual connected-sum isomorphism show
that one factor has trivial fundamental group. The connected factor is then
simply connected; accepted smooth Poincare gives its actual diffeomorphism
to the sphere. This proves the existing smooth `IsPrime` definition, not a
group-theoretic surrogate. The criterion needs only one basepoint. It assumes
neither irreducibility nor a prime-decomposition producer.

The exact PC standard classification supplies a finite fundamental group for
the spherical quotient and an actual isomorphism to Z for the sphere product.
`isPrime_of_isStandardFactor` binds both cases. The classification contains an
actual model map and finite free isometric action; finite abstract fundamental
group alone is not being used to produce a spherical metric.

`Topology/Endpoint/StandardCertificates.lean` maps the existing three-case
elementary metric registry to the corresponding tags in the full eight-model
endpoint. The exact metric tensor, model charts and completeness are retained
on the same whole carrier. None of the three cases is hyperbolic, so the
conditional hyperbolic volume field is vacuous for the correct reason.

`primeGeometricCertificate` uses actual primeness and geometry with the existing
`NoCuts.geometricDecomposition`. `standardFactorCertificate` supplies both
inputs from the classification. It has the literal singleton prime list [P],
one whole cut piece, zero tori, an actual empty-pairing quotient and oriented
reconstruction. The singleton-list and zero-torus properties are proved.
The theorem `standardFactorEndpoints` is therefore an actual supplier.

`geometrizes_of_isPoincareStandard` now consumes an actual PC classified
finite-sum presentation with no additional exceptional-geometry hypothesis.
Revision205's smooth transport and revision203's finite-family composition
retain repeated slots and handle the empty-list sphere convention.

`Endpoint/StandardHistoryAssembly.lean` connects this supplier immediately:

- `geometrizes_of_raw_final_components` requires component endpoints on an
  actual final observation of the same raw tower.
- `geometrizes_of_raw_empty` needs only an actual empty observation. Completion,
  discarded classification and standard-factor endpoints are already produced.
  It asserts no finite extinction and has no late or reconstruction premise.
- `geometrizes_of_raw_late` retains only `LateComponentSupply F.observation`.
  It applies the existing late-nonempty/absorbing-empty dichotomy and the
  original initial marking. The one late threshold still precedes time choice.

`GeometrizationChecks/StandardFactorConsumers.lean` verifies the actual antipodal
quotient endpoint together with its nontrivial fundamental group, two repeated
antipodal factors with two prime slots, the exact universe-lifted sphere-product
cycle, and late/terminal consumers of `RawSurgery.ofInitial`.

## Source review and translation

Accepted PC v0.1.3 at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`, Lean4.33.1
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` remain unchanged.
Exact hashes and inspected intervals are in `evidence/iteration206_sources.json`.
Key source bodies and definitions read:

- Mathlib `GroupTheory/CoprodI:260-333,540-605`: actual reduced words, product,
  first-index and equivalence. Revision192's full reading of the action and
  inverse proof is reused for unchanged dependencies.
- PC `Topology/Algebra/Group/FreeProduct:177-235`: bool family with universe
  lifts, maps, both inverse proofs and actual binary equivalence.
- PC `Topology/VanKampen/FiniteConnectedSumFreeProduct:70-92,229-283`:
  connected/path-connected instances, actual chosen points, neck realization,
  basepoint comparisons and connected-sum free-product theorem.
- PC `Topology/VanKampen/SimplyConnectedUnion:18-33`: one-basepoint triviality
  is equivalent to simple connectivity under actual path connectedness.
- PC `Topology/ThreeManifold/StandardFactors:22-33,540-609`: actual finite
  free positive action, quotient group, sphere-product group and classification.
- PC `Topology/FundamentalGroup/Sphere:150-181` and `Product:1-90`: circle
  and product isomorphisms; the quotient group producer in
  `SphericalQuotient:1-78` was also reopened.
- PC `Surgery/Skeleton/PoincareEndgame:90-111`: actual smooth Poincare theorem
  with compact, connected, Hausdorff, smooth and simply connected hypotheses.
  Its accepted analytic proof is reused, not freshly reconstructed.
- Existing GC `FiniteFreeFactors:1-101`, `StandardFactorGeometry:1-77`,
  `SphericalProductPiece:1-93`, `ElementaryModels:1-90`,
  `ExplicitSphericalConsumers:1-88`, `ModelAtlas:1-84`, `NoCuts:1-163`,
  `SphereExample:1-70`, and `Endpoint/Assembly:1-97`: actual previously proved
  metric and reconstruction interfaces. Precise bounds are clamped to each
  file's length in the machine record; untouched deeper dependencies retain
  their previous source-review scope.

Hatcher's archive `Hatcher3ManifoldNotes.pdf` is the 61-page version whose
front matter records revisions in1999/2000. SHA256:
`f3781c43b4ed981f98fab36761d5eefe92bb53cc1a7100a0146954f9af5a029b`.
Reopened: Section1.1 definitions and Proposition1.4 proof, printed4-5/PDF5-6;
the preceding smooth context and the free-product discussion on
printed50/PDF51 were also inspected.

The [author page](https://pi.math.cornell.edu/~hatcher/3M/3Mdownloads.html),
checked September28,2026, identifies its current PDF as revised in2023 with
75pages. The separately retained [author PDF](https://pi.math.cornell.edu/~hatcher/3M/3Mfds.pdf)
has SHA256 `c8add1a8633f36cb50de313f8f340a3f2b63b5548077d6e30f9c51a073398ff6`.
The matching definitions/proof are printed5-6/PDF6-7. The page has no separate
erratum link; no exhaustive absence-of-corrections claim is made. The archive
is not overwritten or described as the2023 copy.

Both versions use the free-product obstruction for sphere-product primeness.
The new Lean route replaces the final covering/Alexander step by accepted
smooth Poincare on the closed simply connected factor. This is a proved adapter
route, not a stronger theorem attributed to Hatcher. No canonical prime
uniqueness or irreducibility theorem is needed. The existing quotient/product
metric source checks are reused; no new model-classification theorem is inferred.

## Remaining frontier and audit boundary

The standard-factor leaf is complete. The general late supplier remains a
coarse output obligation: it must still be produced through one common global
profile and actual collapse, persistence, incompressibility and refinement
interfaces. Raw tower coherence is not analytic control. The controlled producer may need
to construct its own raw tower F; no claim is made that every raw tower, or an
arbitrary default classical choice, satisfies the late supply. Full protected-port,
prescribed-cycle and decorated-history statements remain separate; this
increment does not accept their parent DAG nodes. The existing DAG and task
register are extended with exact declarations and consumers, not replaced.

All four new modules and consumers passed narrow builds. The first reduced-word
proof needed explicit definitional reductions; the zero-torus property needed
eliminating the unique factor index. Corrected proofs compile without
placeholders. Full gate and blueprint verification are in the accompanying
receipts. No cold-machine build, Overleaf execution, independent teammate
acceptance or general Geometrization proof is claimed.

Final full gate: **155 modules and 4311 audited declarations**, standard three
axioms only. All123 promoted modules and accepted pins unchanged. Exact
receipts: `evidence/iteration206_verification.json` and
`evidence/iteration206_gate_console.log`. Subsequent user steering requests
blueprint wrap-up; no further Lean development is part of revision207.
