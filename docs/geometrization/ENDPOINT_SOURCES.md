# Endpoint statement: source and contract record

Implementation started 2026-09-28 at team commit
`3ea7ad1a997908e1136523667731df515968f116`. The task is to state the full
blueprint endpoint in Lean, not to prove geometrization. The mathematical
blueprint remains revision202; source and model conventions below implement its
Chapter 1 C1–C4, Chapter 5 K1–K3 and Chapter 7 E1 policy.

## Sources actually checked

The archive is read-only. These identities match the existing blueprint source
manifest and revision169–171 comparison records.

* Bruno Martelli, *An Introduction to Geometric Topology*, Version 4,
  September 2025, `MartelliGeometricTopologyBookV4.pdf`, 496 PDF pages,
  SHA256 `66285ca091682ad54f75bc5f900aeb2d79becb0805761c4888c186096d2a19eb`.
  PDF page = printed page + 8.
* Peter Scott, *The Geometries of 3-Manifolds*, Bull. London Math. Soc. 15
  (1983), 401–487, `Scott1983Geometries.pdf`, SHA256
  `98387f6fecebfd93f8d0c4f6b43df711ce71d5753364ce9b1f58135ad80147c5`.
  Printed page403/PDF3 defines local homogeneity and describes cutting along
  spheres and tori and taking complete geometry on interiors.

New targeted body/proof readings in this iteration:

| Contract | Martelli locator | Translation |
|---|---|---|
| Eight fixed models, geometric local charts | §12.1, printed371–372/PDF379–380 | Local metric pullback equalities under smooth partial diffeomorphisms |
| Hyperbolic metric | Prop.2.1.23 and proof, printed54–55/PDF62–63 | Substitute positive height `exp z`; the tensor becomes `exp(-2z)(dx²+dy²)+dz²` |
| Product models | §12.4.1–2, printed385–386/PDF393–394 | Round S²×R reuses PC; H²×R uses logarithmic H² height |
| Nil | §12.5.1–2, Ex.12.5.2, printed388–389/PDF396–397 | Coframe `dx, dy, dz-x dy` |
| Universal-cover SL₂ | Lemma12.6.1 and proof, printed394–396/PDF402–404; §12.6.3, printed397/PDF405 | Lift angle to R, write height `exp y`; coframe `exp(-y)dx, dy, dz+exp(-y)dx` |
| Sol | §12.7.1, printed398–399/PDF406–407 | Coframe `exp(z)dx, exp(-z)dy, dz` |
| Prime convention | Def.9.2.13, printed278/PDF286; Prop.9.2.14 and proof, printed279/PDF287 | Every connected sum has a sphere summand; S³ remains an allowed prime unit |
| Comparison with geometrization | §12.9.1, printed403/PDF411 | The source's canonical geometric decomposition/finite-volume convention differs from our E1 endpoint; no equivalence is silently imported |

The metric matrices on PDF397,402,407 were also visually checked against the
rendered pages. Text extraction alone can obscure their entries.

On 2026-09-28 the [author's book page](https://people.dm.unipi.it/martelli/geometric_topology.html)
was checked: it links the current book; no separate errata sheet was exposed
there. The moving download is not substituted for the archived version.
Scott's [publisher record](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/blms/15.5.401)
was checked. The historical Michigan correction-sheet URL remained inaccessible;
this is not a claim that Scott has no corrections. His classification is not
being imported as a proved Lean theorem.

## Exact model interface

`ThurstonModel` has precisely eight constructors. Three reference metrics reuse
`ElementaryModels`; five reference tensors are explicit sums of squares of the
coframes above. Lean checks their positive definiteness and symmetry. Local
atlases compare the actual piece metric against those fixed tensors. This is a
concrete definition, with no caller-supplied geometry predicate. The equivalence
with the established `ModelAtlas` API is proved whenever a global metric has
the prescribed tensor. Constructing those five global bundled metrics and
proving their completeness, curvature and homogeneous actions remain useful
future model lemmas, not assumptions or unproved declarations in this code.

`GeometricStructure` stores an actual smooth metric, completeness for that
metric on its whole carrier, the fixed-model atlas, and finite Riemannian volume
of that same metric when its tag is hyperbolic. The volume uses PC's actual
`riemannianVolumeMeasure`. No metric on a truncated compact core substitutes
for the complete interior metric.

## PC reuse and evidence boundary

Accepted PC v0.1.3 is pinned at
`7a48598d35109aa99d1cc678e2724c213cdf4ff3`; Lean and Mathlib pins are unchanged.
Existing `ModelAtlas`, round/Euclidean/cylinder metrics, PC smooth metric
completeness and Riemannian measure APIs are reused. Later cut definitions will
reuse actual PC connected sums, manifold interiors, smooth collars and
fundamental-group maps. No absence of an adapter is classified as absence of
the inherited mathematics.

A successful Lean build checks the definitions and theorems stated in code.
It does not prove existence of an endpoint certificate for every manifold.

## Cut and reconstruction contract (iteration 2)

Further source body checks: Martelli Def.9.2.13 and Prop.9.2.14 (locators above),
§9.4.3/Prop.9.4.9 printed298/PDF306, the statement and setup of Thm.9.4.14
printed302/PDF310, and §11.5.1 printed366–367/PDF374–375. The endpoint defines
incompressibility directly as π₁-injectivity, so no unproved disk-to-π₁ adapter is
imported. No canonical/minimal JSJ choice or uniqueness claim is added.

`CompactCarrier` permits exactly the Euclidean and half-space 3-models; it
excludes higher-codimension corner models. Its finite clopen connected pieces
cover the entire carrier. Every component interior is connected and nonempty.
The open-interior σ-compactness proof reuses PC `Topology/SigmaCompactOpen.lean`.

`TorusGluing` binds smooth half-collars to torus parametrizations of actual
boundary subsets. Smooth torus matching diffeomorphisms determine PC's actual
`BoundaryGluing` homeomorphisms. Every boundary point belongs to exactly one
paired block; no unmatched side is permitted. The assembled underlying space
is definitionally `Quotient gluing.setoid`, with its quotient topology. It is
not defined to be the final prime carrier. PC `BoundaryGluing` supplies the
Hausdorff quotient and the explicit relation. New proofs establish that interior
fibers are singletons, torus maps are embeddings, and different torus images
are disjoint. `descend` and its uniqueness theorem expose the universal map.

`SmoothAssembly` supplies a smooth structure on that quotient, with the actual
quotient map smooth and orientation preserving on each side, an exact
interior diffeomorphism, and smooth signed seam charts equal to the two
half-collars. Smoothness is therefore checked against the supplied cut data,
not merely transported along an unrelated homeomorphism. The boundary reversal
field compares ambient orientations pulled back to the same inward collar
coordinates, with a minus sign. Moving the normal from last to first across
two tangent coordinates is even; replacing inward by outward on both sides
preserves this reversal condition. This is the explicit normal-first
orientation convention, consistent with PC's
`Topology/Manifold/BoundaryOrientationOutwardFrame.lean`, whose definitions and
normal-reflection identities were inspected. The new wrapper uses this direct
collar condition; a separately packaged two-dimensional induced-boundary API
can later be derived from it.

`GeometricDecomposition P` retains boundary-side ownership, the actual oriented
quotient-to-P diffeomorphism, π₁-injectivity of its torus images **in P**, and
geometry on every entire piece interior. `PrimeDecomposition` uses PC's actual
smooth `connectedSum`/`finiteConnectedSum` and keeps a nonempty list, allowing S³
as a prime unit. `GeometrizationConjecture` quantifies over all closed connected
oriented smooth 3-manifolds and requests these certificates. Its equivalence to
the unbundled smooth-manifold statement is proved. Neither proposition has
been asserted as a theorem.

## Final interface refinement and example (iteration 3)

Every component's metric is now in PC's **ordinary boundaryless interior
atlas**, through `CompactCarrier.InteriorGeometry`. This refines iteration2's
original-atlas representation without changing the carrier or mathematical
conditions. `interiorGeometryOfOriginal` supplies the actual adapter from a
metric written in the compact carrier's atlas. It uses the source model's
boundarylessness exactly where required by PC volume pullback.

Additional PC bodies/signatures inspected and reused:

* `Topology/Manifold/InteriorAtlas.lean`: `interiorChartedSpace`,
  `interiorIsManifold`, `interiorAtlasDiffeomorph`, intrinsic interior and its
  boundarylessness; actual identity maps with checked smoothness.
* `Analysis/Integration/Measure/PullbackCross.lean:249`:
  `riemannianVolumeMeasure_pullback_cross`, including its `I.Boundaryless`
  assumption, genuine pullback metric, and pushforward by the inverse map.
* `Topology/Manifold/ClosedOrientedPullback.lean`: actual smooth/oriented
  pullback along a homeomorphism, used only after the canonical empty-pairing
  quotient homeomorphism has been constructed; interior compatibility is proved.
* `Topology/VanKampen/Pi1FiniteConnectedSumSimplyConnected.lean:32`:
  `simplyConnectedSpace_of_mem_finiteConnectedSum` and its proof, and the
  equivalence at line46. These are applied to the actual two-factor sum.
* `Geometry/Flow/RicciFlow/Surgery/Skeleton/PoincareEndgame.lean:103`:
  `smoothPoincareConjecture_holds`, full statement and proof. Its actual smooth
  sphere diffeomorphism is composed with `standardThreeSphereLiftDiffeomorph`.
  This is accepted-foundation reuse, not a new proof of PC or an assumption of
  general finite extinction in the GC route.

`SphereExample.lean` proves primeness of a simply connected closed 3-manifold
using these accepted results, then constructs a complete certificate for the
standard lifted S³. `NoCuts.lean` separately builds a genuine zero-torus
geometric decomposition for any supplied closed geometric manifold; it does not
claim all closed geometric manifolds are prime (S²×R quotients provide a reason
to keep those statements separate).
