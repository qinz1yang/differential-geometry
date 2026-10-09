# Differential Geometry in Lean 4

An ongoing Lean 4 library for differential geometry and geometric analysis, currently focused on Ricci flow.

## How to use

Use DifferentialGeometry as an upstream dependency and build on its geometric-analysis infrastructure:

```toml
[[require]]
name = "DifferentialGeometry"
git = "https://github.com/qinz1yang/differential-geometry.git"
rev = "v0.1.5"
```

Release `v0.1.5` is pinned to Lean and Mathlib `v4.35.0-rc3`.
The current development branch uses Lean and Mathlib `v4.35.0-rc3`.

Import the full library with

```lean
import DifferentialGeometry
```

or a specific module, for example the scalar strong maximum principle:

```lean
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Strong
```

We aim to keep pace with Mathlib releases and update the pinned Mathlib version accordingly.

## Formalized theorems

Each is `sorry`-free (axioms: `propext, Classical.choice, Quot.sound`).

> These three are the standard axioms of Lean's core library — propositional extensionality, the axiom of choice, and quotient soundness — on which all of classical mathematics in Mathlib rests. `#print axioms` lists everything a theorem transitively assumes: a `sorry` would surface as `sorryAx`, and any ad-hoc axiom would be named. An output of exactly these three therefore certifies that the proof is fully kernel-checked, with no `sorry` and no assumptions beyond the classical foundations.

- [Geometrization conjecture](DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/Geometrization.lean#L49) — every closed, connected, oriented smooth three-manifold is a finite connected sum of prime manifolds, each of which can be cut along finitely many pairwise disjoint smooth incompressible tori into pieces whose interiors carry complete metrics locally isometric to one of the eight Thurston geometries; the hyperbolic interiors have finite volume.
- [Mostow–Prasad rigidity](DifferentialGeometry/Geometry/Hyperbolic/MostowRigidity.lean#L259) — every homotopy equivalence between complete, connected, finite-volume Riemannian three-manifolds with the same constant negative sectional curvature is homotopic to a unique isometry.
- [Poincaré conjecture](DifferentialGeometry/Topology/ThreeManifold/Poincare.lean#L27) — every compact, Hausdorff, simply connected topological three-manifold without boundary is homeomorphic to the unit sphere $S^3 \subset \mathbb{R}^4$. The final statement uses only Lean/Mathlib concepts. The [smooth version](DifferentialGeometry/Topology/ThreeManifold/Poincare.lean#L15) gives a diffeomorphism for smooth three-manifolds.
- [Finite-time extinction with surgery, simply connected case](DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Extinction/Existence.lean#L15) — every simply connected closed oriented smooth three-manifold, with any initial smooth Riemannian metric, admits a controlled finite surgery history ending in the empty manifold at a positive finite time. The [extinction structure](DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/ControlledExtinction.lean#L14) records the initial metric identification and the empty terminal stage.
- [Moise's theorem: compatible smooth structures in dimension three](DifferentialGeometry/Topology/PiecewiseLinear/Moise352Producer.lean#L33) — every compact Hausdorff topological three-manifold admits a smooth atlas compatible with its given topology. The development supplies [PL approximation](DifferentialGeometry/Topology/PiecewiseLinear/Moise352Producer.lean#L27) and [compact PL smoothing](DifferentialGeometry/Topology/PiecewiseLinear/Moise352Producer.lean#L30), providing the bridge from smooth to topological Poincaré.
- [Perelman's canonical neighborhood theorem](DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureModelBounds.lean#L539) — in a Ricci flow on a closed connected oriented three-manifold over a finite time interval, every point of sufficiently large scalar curvature lies in a controlled neck, cap, positively curved compact component, or nearly round component. The development also gives [curvature-scale bounds for all mixed space-time curvature derivatives](DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureModelBounds.lean#L586).
- [Compactness of ancient κ-solutions](DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureModelBounds.lean#L566) — three-dimensional ancient κ-solutions with fixed κ and basepoint scalar curvature normalized to one admit smoothly convergent pointed subsequences with an ancient κ-solution limit, together with [universal mixed curvature-derivative estimates](DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/HighCurvatureModelBounds.lean#L579).
- [Hamilton's compactness theorem](DifferentialGeometry/Geometry/Flow/RicciFlow/Compactness/Limits/Hamilton.lean#L27) — complete connected pointed Ricci flows on a common open time interval, with uniform curvature bounds on compact time intervals and a uniform positive basepoint injectivity-radius bound at time zero, admit a smooth pointed Cheeger–Gromov–Hamilton convergent subsequence with a complete limit.
- [Hamilton's theorem (1982)](DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/PositiveRicci/Hamilton.lean#L29) — a closed three-manifold admitting a positive-Ricci metric admits a constant-positive-sectional-curvature metric and is a spherical space form.
- [Ricci flow short-time existence](DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/Existence.lean#L34) — on every closed Riemannian manifold $(M, g_0)$ the Ricci flow $\partial_t g = -2\,\mathrm{Ric}_{g(t)}$ has a solution on some $[0, T)$ with $g(0) = g_0$, jointly smooth in $(t, x)$ up to and including the initial time. Proved via the DeTurck's trick and a conjugating flow of the DeTurck vector field.
- [Perelman's reduced-volume monotonicity](DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/LGeometry/ReducedVolume/Basic.lean#L384) — along a Ricci flow on a closed connected manifold, the reduced volume is nonincreasing in backward time, built on the L-length minimizer, L-cut-locus, and reduced-Jacobian theory.
- [Perelman's no local collapsing theorem](DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/Noncollapsing/FiniteTime.lean#L33) — every smooth Ricci flow on a closed connected manifold over a finite time interval is uniformly κ-noncollapsed below any prescribed scale on curvature-controlled spacetime balls.
- [Perelman's W-entropy monotonicity](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/W/Variation/Monotonicity.lean#L726) — along Ricci flow on a closed manifold, a positive conjugate-heat solution determines a W-entropy that is nonincreasing in backward time, with the [exact integral-square derivative formula](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/W/Variation/Monotonicity.lean#L281).
- [Ricci–DeTurck flow short-time existence](DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/DeTurck/InitialData.lean#L143) — the gauge-fixed, strictly parabolic flow behind the reduction: a solution whose chart-Gram entries are jointly smooth on the closed time slab, together with joint smoothness of the DeTurck vector field.
- [Ricci-tensor naturality under diffeomorphisms](DifferentialGeometry/Geometry/Curvature/CurvatureOperator/Ricci/Naturality.lean#L250) — $\mathrm{Ric}_{\Phi^* g}(v, w) = \mathrm{Ric}_g(d\Phi\, v, d\Phi\, w)$, the equivariance that transports the DeTurck solution back to a Ricci flow.
- [Scalar-curvature evolution under Ricci flow](DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/Scalar/IntrinsicDerivation.lean#L736).
- [Hamilton–Ivey pinching estimate](DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonIvey/MaximumPrinciple.lean#L5324) — the scalar-curvature lower bound and logarithmic pinching estimate for closed three-dimensional Ricci flows with an initial curvature-operator lower bound, together with an [asymptotic pinching estimate](DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonIvey/MaximumPrinciple.lean#L5395).
- [Shi's derivative estimates](DifferentialGeometry/Geometry/Flow/RicciFlow/Estimates/Shi/TimeWeighted.lean#L20) — uniform curvature bounds and completeness of the initial metric give time-weighted bounds for every covariant derivative of curvature along Ricci flow.
- [Hamilton's matrix Harnack inequality for Ricci flow](DifferentialGeometry/Geometry/Flow/RicciFlow/HamiltonHarnack/MatrixHarnack.lean#L10209) — the matrix Harnack quadratic is nonnegative on closed Ricci flows with nonnegative curvature operator. In dimension three, [nonnegative initial curvature operator suffices](DifferentialGeometry/Geometry/Flow/RicciFlow/HamiltonHarnack/MatrixHarnack.lean#L10247).
- [Bonnet–Myers diameter bound](DifferentialGeometry/Geometry/Comparison/BonnetMyers/Diameter.lean#L506) — a positive Ricci lower bound forces a bounded diameter.
- [Bochner formula](DifferentialGeometry/Analysis/Elliptic/Regularity/Bochner/PolarisedLpSmooth.lean#L66) — the polarised, pointwise form.
- [Weitzenböck identity](DifferentialGeometry/Analysis/Elliptic/ConnectionLaplacian/Weitzenbock/IntegratedCovariantTensor.lean#L98) — the integrated $L^2$ form.
- [Lichnerowicz eigenvalue bound](DifferentialGeometry/Analysis/Elliptic/Lichnerowicz.lean#L598) on closed manifolds.
- [Voss–Weyl divergence formula](DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Local/ChartInvariance.lean#L576) — the chart-invariant divergence.
- [de Rham cohomology](DifferentialGeometry/Tensor/Exterior/Cochain.lean#L72) — intrinsic differential forms with [nilpotent exterior derivative](DifferentialGeometry/Tensor/Exterior/Basic.lean#L607), [graded Leibniz rule](DifferentialGeometry/Tensor/Exterior/Leibniz.lean#L604), and [functorial pullback maps](DifferentialGeometry/Tensor/Exterior/Cochain.lean#L159).
- [Morse lemma](DifferentialGeometry/Topology/Morse/NormalForm/Manifold.lean#L950), the [no-critical-values theorem](DifferentialGeometry/Topology/Morse/RegularLevel/NoCriticalValues.lean#L187), and [single-critical-point cell attachment](DifferentialGeometry/Topology/Morse/Attachment/SmoothHandle.lean#L932), with [smooth handle-adjunction diffeomorphisms](DifferentialGeometry/Topology/Morse/Attachment/SublevelTransport.lean#L1033).
- [Elliptic variable-coefficient Schauder estimates](DifferentialGeometry/Analysis/Schauder/Elliptic/VariableCoefficient/Basic.lean#L1349) and [parabolic nondivergence Schauder estimates](DifferentialGeometry/Analysis/Parabolic/Euclidean/Nondivergence/Schauder.lean#L550).
- [Strong parabolic maximum principles](DifferentialGeometry/Analysis/Parabolic/MaximumPrinciple/Scalar/Strong.lean#L2412) — scalar equations on fixed and moving metrics, [parallel proper cones](DifferentialGeometry/Analysis/Parabolic/MaximumPrinciple/Cone/Parallel/DualStrong.lean#L30), and [symmetric tensors](DifferentialGeometry/Analysis/Parabolic/MaximumPrinciple/Tensor/Strong.lean#L193), with a [Hopf boundary point theorem](DifferentialGeometry/Analysis/Parabolic/MaximumPrinciple/Scalar/Hopf/ManifoldBoundary.lean#L168).
- [Li–Yau Harnack inequality](DifferentialGeometry/Analysis/Parabolic/Harnack/LiYauHarnack.lean#L792) and [Hamilton differential Harnack inequality](DifferentialGeometry/Analysis/Parabolic/Harnack/HamiltonDifferentialHarnack.lean#L1483) for positive heat solutions.
- [Quasilinear parabolic local existence](DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/Existence/LocallyLipschitz.lean#L702) for locally Lipschitz Sobolev nonlinearities.
- [Generalized Poincaré conjecture, dimension ≥ 5](DifferentialGeometry/Topology/HighDimensional/PoincareHighDim.lean) — every Hausdorff topological manifold without boundary homotopy equivalent to $S^n$, with $n ≥ 5$, is homeomorphic to $S^n$.

## Verification

```bash
git clone https://github.com/qinz1yang/differential-geometry.git
cd differential-geometry
lake build DifferentialGeometry.Topology.ThreeManifold.Poincare
```

To inspect the Poincaré theorem's transitive axioms, temporarily add

```lean
#print axioms DifferentialGeometry.Topology.poincare_conjecture
```

to [`Poincare.lean`](DifferentialGeometry/Topology/ThreeManifold/Poincare.lean), then run

```bash
lake build DifferentialGeometry.Topology.ThreeManifold.Poincare
```

## PDE infrastructure

Underlying these results is a substantial geometric-analysis backbone:

- [**Integration & the divergence theorem**](DifferentialGeometry/Analysis/Integration) — Riemannian measures, integration by parts and surface measures, with and without boundary.
- [**Elliptic regularity**](DifferentialGeometry/Analysis/Elliptic) — the connection (rough) Laplacian, Green identities, Gårding / Caccioppoli estimates, Hölder–Schauder spaces, variable-coefficient estimates, and interior bootstrap.
- [**Spectral theory**](DifferentialGeometry/Analysis/Spectral) — the scalar theory on closed manifolds (discrete Laplacian spectrum, compact resolvent, eigenbasis); an iterated covariant-gradient jet calculus for tensor fields with fibre-norm towers and Sobolev-scale spectral estimates; and the intrinsic heat-semigroup / Galerkin machinery driving the DeTurck flow.
- [**Sobolev spaces**](DifferentialGeometry/Analysis/Sobolev) — chart-based and intrinsic $H^k$ / $W^{k,p}$ spaces with completeness, embedding and compactness results; tensor-valued Hilbert–Sobolev towers; Moser-type tame product estimates; and Gagliardo–Nirenberg interpolation down to fibre-norm level.
- [**Parabolic & heat equations**](DifferentialGeometry/Analysis/Parabolic) — heat semigroups, Duhamel solutions, Schauder and maximal regularity, quasilinear local existence, strong maximum and Hopf principles, Harnack inequalities, and joint space-time smoothing.
- [**ODE flows**](DifferentialGeometry/Analysis/ODE) — $C^\infty$ dependence of flows on their initial data, and time-dependent flows on closed manifolds jointly smooth up to the initial time (via Seeley-type time extension of the vector field).

The classical De Giorgi–Nash–Moser regularity machinery is vendored under [`External/`](DifferentialGeometry/External) from [scottnarmstrong/DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi) (Scott Armstrong and Julia Kempe, Apache-2.0).

## Topology Infrastructure

The topology library supplies the constructions used by Moise smoothing, surgery, and the Poincaré endpoint:

- [**PL topology, triangulation & smoothing**](DifferentialGeometry/Topology/PiecewiseLinear) — simplicial complexes, links and stars, subdivisions, PL balls and spheres, local charts, finite gluing, approximation and isotopy. [Compact PL triangulations](DifferentialGeometry/Topology/PiecewiseLinear/TriangulationExistence.lean#L57) and [smooth structures on compact topological three-manifolds](DifferentialGeometry/Topology/PiecewiseLinear/Moise352Producer.lean#L33) connect the combinatorial and smooth developments.
- [**Fundamental groups, homotopy & coverings**](DifferentialGeometry/Topology/Covering) — path and homotopy lifting, covering transformations, deck groups, and based/free sphere-map constructions. The [van Kampen development](DifferentialGeometry/Topology/VanKampen) includes [fundamental groups of finite connected sums](DifferentialGeometry/Topology/VanKampen/FiniteConnectedSumFreeProduct.lean#L277).
- [**Homology, cohomology & orientation**](DifferentialGeometry/Topology/Homology) — singular chains, relative and local homology, excision, [Mayer–Vietoris exactness](DifferentialGeometry/Topology/Homology/MayerVietorisExactness.lean#L125), compactly supported cohomology, cap products, low-degree Hurewicz maps, local orientation classes and fundamental classes. These developments build on the [vendored canonical-topology core](DifferentialGeometry/External/CanonicalTopology/Topology/Homology).
- [**Morse theory & handles**](DifferentialGeometry/Topology/Morse) — Morse normal forms, regular-level transport, critical-point attachment, sublevel topology and smooth handle attachment, supported by [handle and collar constructions](DifferentialGeometry/Topology/Handle).
- [**Three-manifold topology & surgery**](DifferentialGeometry/Topology/ThreeManifold) — sphere separation, connected sums, cutting and capping, reconstruction and orientation transport. [Cut-and-cap reconstruction](DifferentialGeometry/Topology/ThreeManifold/CutCapConnectedSumTopology.lean#L29) identifies the original manifold as a connected sum of capped components and sphere-product factors; [simple connectivity is preserved by capping](DifferentialGeometry/Topology/ThreeManifold/CutCapConnectedSumTopology.lean#L53).
- [**Separation, embeddings & gluing**](DifferentialGeometry/Topology/PlanarJordan) — planar Jordan and Schoenflies tools, [sphere separation](DifferentialGeometry/Topology/SphereSeparation), [smooth embedding and extension APIs](DifferentialGeometry/Topology/Embedding), [collars](DifferentialGeometry/Topology/Collar), and [adjunction spaces](DifferentialGeometry/Topology/Attachment), with [homeomorphism](DifferentialGeometry/Topology/Homeomorph) and [diffeomorphism](DifferentialGeometry/Topology/Diffeomorph) transport and gluing.

Third-party foundations are preserved under [CanonicalTopology](DifferentialGeometry/External/CanonicalTopology/README.md), [ClassificationOfSurfaces](DifferentialGeometry/External/ClassificationOfSurfaces/VENDOR.md), [Schoenflies](DifferentialGeometry/External/Schoenflies/UPSTREAM_README.md), and [selected Tau Ceti modules](DifferentialGeometry/External/TauCeti/README.md), together with their source, license and modification records. Native extensions and theorem assembly remain in the mathematical topic directories.

## AI Disclaimer

Generative AI (ChatGPT, Claude, Deepseek, Gemini, GLM, etc.) was used in the development of this codebase. The high-level architecture is human-designed; AI agents assisted with formalizing individual proofs and writing boilerplate. All definitions and core theorem statements were human-verified for correctness. Since all proofs are verified by Lean's type checker, AI-generated and human-written code are held to the same standard of correctness.

> **Note:** This library is under active development. Breaking changes to public APIs and file paths should be expected.
