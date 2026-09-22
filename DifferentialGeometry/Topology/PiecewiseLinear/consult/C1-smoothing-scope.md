# C1 scope: `PLSmoothingModel 3`, refreshed against the tree of 2026-09-21

Baseline `codex/moise-integration` @ `1a7a78a2c`. Refreshes `PHASE2_SMOOTHING_AUDIT.md`
(2026-09-12); its §1 tables stay valid unless contradicted here. Every declaration cited was
opened. Paths omit `DifferentialGeometry/`; `PL/` = `Topology/PiecewiseLinear/`.

## 0. What changed since the audit (verified)

- **H1 (PL handle decomposition) is CLOSED.** `PL/DerivedNeighborhoodHandleFiltration.lean:20`
  `exists_pl_three_handle_filtration`: for finite `K` with `IsCombinatorialManifold 3 K`, a
  monotone-by-index enumeration of `K.faces`, derived neighbourhoods `N i` of the face prefixes,
  `(N 0).space = ∅`, `(N m).space = K.space`, each `IsCombinatorialManifoldWithBoundary 3 (N i)`,
  each step an `IsPLThreeHandleAttachment (k i)` (`PL/CellAttachment.lean:55`) with models `Δ³`;
  `Δ² × [0,1]` on `Δ² × {0,1}`; `Δ² × [0,1]` on `stdSimplexBoundary 2 × [0,1]`; `Δ³` on
  `stdSimplexBoundary 3`. Each step carries a PL homeomorphism of the model onto the cell, an
  attaching closed embedding into `(boundaryComplex 3 (N i)).space`, and a homeomorphism
  `AdjunctionSpace … ≃ₜ (N (i+1)).space` fixing the lower space (`PL/CellAttachment.lean:19`).
- **Triangulation bridge CLOSED**: `PL/Combinatorial.lean:268 plManifoldTriangulation` (from
  `:257`), for compact T2 `Nonempty` PL `n`-manifolds; not a free input any more. **PL Schoenflies
  dim 3 unconditional**: `PL/PLSchoenflies.lean:6,10`, on the proved
  `PL/SchoenfliesFoundations.lean:7 schoenflies_input`. **PL boundary-sphere extension proved**:
  `PL/BallReplacement.lean:23`, `PL/ThreeCellExtension.lean:7`.
- **Topological cone extension exists** (audit §2.8, then missing):
  `Topology/Homeomorph/SphereExtension.lean:45 sphereRadialHomeomorph`, `:71
  closedBallHomeomorphExtension`; plus `Topology/Attachment/CellExtension.lean:41` and
  `Topology/Attachment/Homeomorph.lean:40 adjunctionHomeomorph` (two attaching squares induce a
  homeomorphism of adjunction spaces). **Topological Jordan–Schoenflies in the plane is vendored
  and sorry-free**: `External/Schoenflies/{JordanSchoenflies.lean:47,54,61, JordanClosed.lean:68}`.
- **Local 2-dimensional smoothing exists**: `Topology/Manifold/SurfaceChartSmoothing.lean:17
  exists_isotopy_smoothing_surface_chart` — for any topological chart into a smooth surface, a
  compactly supported ambient isotopy and a reparametrisation making the corrected chart lie in
  the maximal smooth atlas on a small ball. Companions `Topology/Homeomorph/
  {PlanarExtension.lean:93, JordanDiskMove.lean:19,82, JordanAnnulus.lean:47,142,
  Alexander.lean:113, CircleIsotopy.lean:15}`. **Corner/collar bricks (local only)**:
  `Topology/Manifold/{CornerRounding.lean, FramedCornerSmoothing.lean:18,
  CollaredCornerSmoothing.lean:15, ChartCornerSmoothing.lean:16, RoundedStrip.lean:223,
  Collar/Attachment.lean:11, BoundaryCollar/{SmoothAttachment.lean:12, Diffeomorph.lean:76}}`.
  **Boundaryless conversion CLOSED** (audit §2.9): `Topology/Manifold/InteriorAtlas.lean:17,33`
  under `[BoundarylessManifold I M]`.
- **`sorry` inventory, smooth side** (never build on these): `Topology/ThreeManifold/
  {ConnectedSum/Construction.lean:92,95,102,133, ConnectedSum/Finite.lean:34,40,46,53,64,70,
  StandardFactors.lean:86, SmoothSchoenflies.lean:14}`; `Topology/Manifold/{Components.lean:115,
  ProductOrientation.lean:39, SphereOrientation.lean:28, ULift.lean:96}`;
  `Topology/Homology/HurewiczLowDegrees.lean:32,44`. `Topology/{Handle,Morse,Diffeomorph,
  SphereSeparation,Collar,Double}` clean; all 23 `sorry`s under `PL/` are in `PL/Skeleton/`.
  `sphereDiffeomorphDegree_eq_one_iff_isotopy` (`…/SphereDiffeomorphDegree.lean:83`) is
  source-clean but shares a subtree with `SphereOrientation.lean:28`: `#print axioms` before use.

## 1. Audit §2 gap table, status today

| Gap (audit §) | Status |
|---|---|
| H1 PL handle decomposition (2.1) | **CLOSED**, `PL/DerivedNeighborhoodHandleFiltration.lean:20` |
| H2 smooth handle attachment along an arbitrary smooth attaching embedding (2.2) | **OPEN**. Only the Morse-specific version (`Morse/Attachment/SublevelTransport.lean:1033`, model `MorseHalfSpace`, universe 0); corner bricks are local; no `𝓡∂ 3` assembly |
| (i) PL circle/annulus in a smooth surface isotopic to smooth (2.3) | **PARTLY**: plane-level inputs now present; no statement about a curve or annulus *in a surface* exists |
| (i-b) framing (2.4) | **DISAPPEARS**: the PL attaching region is already an annulus, so the framing is carried, not reconstructed |
| (i-c) isotopic attaching maps give homeomorphic gluings (2.5) | **PARTLY**: `Topology/Attachment/Homeomorph.lean:40` gives the quotient comparison; the collar extension of a boundary isotopy is unwritten but its input is `BoundaryCollar/Diffeomorph.lean:76` |
| (ii) smooth closed surface homeomorphic to `S²` is diffeomorphic to `S²` (2.6) | **OPEN, unchanged**. `Morse/{CompactCriticalValues.lean:174,218, CubicCancellation.lean:179, LocalizedCubicCancellation.lean:35, SaddleMinimumStrip.lean:21}` are genuine partial inputs |
| (ii′) PL homeomorphism of a closed surface isotopic to a diffeomorphism (2.7) | **OPEN**, no producer, no partial input; Heegaard route only |
| Alexander cone extension (2.8) | **CLOSED**, `Topology/Homeomorph/SphereExtension.lean:45,71` |
| assembly / universe / boundaryless (2.9) | **PARTLY**: boundaryless closed; compact interface and `ULift` still to write |

No `HandleDecomposition`, `Heegaard`, `handlebody`, `genus` or surface-classification declaration
exists; the external `classification_of_surfaces` vendor is recorded as not recommended
(`HANDOFF_CODEX_H.md` §H.4b).

## 2. Goal-driven restriction

`Smoothing.lean:63` already assumes `[T2Space M] [CompactSpace M]`; the honest restriction is
compactness only:

```lean
def PLSmoothingModelCompact (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      IsManifold (𝓡 n) ∞ N ∧ Nonempty (X ≃ₜ N)
```

Endpoint changes: add `[CompactSpace X]` to `PLSmoothing` as `PLSmoothingCompact`; restate
`plSmoothing_of_plSmoothingModel` for the compact pair (proof unchanged — `pullbackChartedSpace`
ignores compactness); let `exists_isManifold_of_plApproximation_of_plSmoothing`
(`Smoothing.lean:37`) consume it, which moves no call site since its `X` already has
`[CompactSpace X]`. Empty `X` needs a separate line, because `plManifoldTriangulation` requires
`[Nonempty X]`. Removed by the restriction: non-compact exhaustion, locally finite assembly, any
infinite induction. **Orientability buys nothing** — the route never chooses a framing, so neither
`IsOrientable` (`PL/Orientation.lean:434`) nor connectedness should enter the statement.
**Compatible smoothing is already not asked for**: `B′` wants a homeomorphic smooth model, which
is what makes the route below possible.

(a) 3-handles by the topological Alexander trick: **partly, not fully.** It removes the *matching*
obligation (no isotopy of an `S² ≃ₜ S²`, hence no Smale / `sphereDiffeomorphDegree` input at the
cap: `sphereRadialHomeomorph` absorbs it). It does **not** remove (ii): to attach a *smooth*
3-handle at all, the boundary component of `N₂` must be diffeomorphic to `S²`, and that boundary
is produced by the construction, not chosen. Every route ends in one capping, so (ii) survives.

(b) Heegaard: **worse.** A PL handlebody must first be recognised (no handlebody notion exists),
and the gluing map isotoped to a diffeomorphism — gap (ii′), strictly stronger than (ii), with no
partial input here. Building `N` handle-by-handle with smooth attaching maps only topologically
conjugate to the PL ones is the recommended route and avoids (ii′). The unavoidable 2-dimensional
content is taming a disk and an annulus in a smooth surface, plus (ii); surface classification is
not needed, so do not take the external vendor.

(c) Simple connectivity: **no further shortcut.** Any use of `π₁ X = 1` that shortened the
smoothing would be a form of the PL Poincaré theorem in dimension 3 — the statement this chain
exists to prove. It must not appear in C1.

## 3. D1 interface

`POINCARE_PLAN.md` does **not** exist in `E:\differential-geometry-dev` (branch
`codex/post-merge-review`, `d4b09024d`), which has no Poincaré endpoint. The endpoints live in the
gitignored worktree `E:\…\.codex-scratch\pc-sorry-free-build` (detached at `7658c8fa8`), file
`…/Geometry/Flow/RicciFlow/Surgery/Poincare.lean`:

- `:30 def smoothPoincareConjecture : Prop` — `∀ (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M], Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯
  standardThreeSphereLift.{u}.Carrier)`. A `Prop` definition, **not proved**: every producer
  (`:36`, up to `Extinction/Width/InitialWidthDataFrontier.lean:65`) is conditional on
  `Prop`-interface hypotheses. No metric or orientation hypothesis — both are built internally
  (`Geometry/Metric/CompactExistence.lean:11`; `Topology/Manifold/Orientation.lean:436`, scratch
  worktree only — the main checkout has the weaker `:173`).
- `:56 topologicalPoincareConjecture_of_smoothStructureInput` is already written against our
  shape: `hsm : ∀ M … [ChartedSpace ℝ³ M], ∃ inst : ChartedSpace ℝ³ M, letI := inst;
  Nonempty (IsManifold (𝓡 3) ∞ M)`, with `ℝ³ = EuclideanSpace ℝ (Fin 3)`.

Mismatches versus `exists_isManifold_three_of_plApproximation_of_plSmoothing`: (1)
`Nonempty (IsManifold …)` versus `IsManifold …` — a one-line bridge, `IsManifold` is a `Prop`
class; (2) `hsm` also carries `[ConnectedSpace M] [SimplyConnectedSpace M]`, harmless and unused
by the smoothing side; (3) nothing else — model space, `𝓡 3`, smoothness `∞` (never `ω`), universe
`u`, `T2Space`, `CompactSpace` match exactly, `SecondCountableTopology` is required by neither.
Residual risks: the target is `ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)`, so an
un-lifted form needs `standardThreeSphereLiftDiffeomorph`; and `standardThreeSphere` is downstream
of `SphereOrientation.lean:28` in **both** checkouts, so the axiom audit belongs on the scratch
chain.

## 4. Proposed skeleton `PL/Skeleton/PLSmoothingClosed.lean` (route R-DN)

Triangulate `X`; take the proved PL handle filtration; build a parallel smooth filtration `Nᵢ`
(model `EuclideanHalfSpace 3`) with `hᵢ : (N i).space ≃ₜ Nᵢ` carrying the intrinsic PL boundary
onto `∂Nᵢ`, correcting each attaching map by an ambient homeomorphism of the boundary surface; cap
with `closedBallHomeomorphExtension`; convert to the boundaryless model and `ULift`. Build the
model in `Type 0`, so the universe-0 restriction of `Morse/*` and `Double/` is harmless.

| Leaf | Statement sketch (tree vocabulary) | Supplier | Size |
|---|---|---|---|
| **L0** carrier bridge | `(T : PLTriangulation 3 X) → [CompactSpace X] [T2Space X] → T.complex.space ≃ₜ X`, from `T.bijOn`, `T.continuousOn`, compactness of a finite complex's space | Mathlib `Continuous.homeoOfEquivCompactToT2` | S |
| **L1** smooth handle attachment | for `N` compact T2 with `[ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold (𝓡∂ 3) ∞ N]`, `k : Fin 4`, and a smooth embedding `ψ` of the standard attaching region into `∂N`: a `ChartedSpace (EuclideanHalfSpace 3)` on `AdjunctionSpace … ψ` with `IsManifold (𝓡∂ 3) ∞`, `T2Space`, `CompactSpace`, and `ContMDiff` `lower`/`cell` | `BoundaryCollar/SmoothAttachment.lean:12`, `Collar/Attachment.lean:11`, `Handle/Gluing.lean`, corner bricks | **L** |
| **L2** step transport | from `h : (N i).space ≃ₜ Nᵢ` and a commuting attaching square, `(N (i+1)).space ≃ₜ Nᵢ₊₁` | `Topology/Attachment/Homeomorph.lean:40` plus `IsPLCellAttachment`'s own `e` | S |
| **L3** disk taming (`k = 1`) | for the two closed disks `g '' (stdSimplex ℝ (Fin 3) ×ˢ {0,1})` of the step, transported into the smooth closed surface `∂Nᵢ`: an ambient homeomorphism of `∂Nᵢ` carrying them onto two disjoint smooth embedded disks, with the reparametrisation | `External/Schoenflies/JordanSchoenflies.lean:47`, `Manifold/SurfaceChartSmoothing.lean:17`, `Homeomorph/JordanDiskMove.lean` | M |
| **L4** annulus taming (`k = 2`) | the same for `g '' (stdSimplexBoundary 2 ×ˢ Icc 0 1)`: an ambient homeomorphism of `∂Nᵢ` onto a smooth embedded annulus | `Homeomorph/JordanAnnulus.lean:47,142`, `PL/ArcChainCover.lean`, L3 | **L** |
| **L5** boundary-to-interior extension | a homeomorphism of `∂N` isotopic to the identity extends to `N`, identity off a collar | `BoundaryCollar/Diffeomorph.lean:76`, `Homeomorph/ConjugateFamily.lean` | S |
| **L6** two-sphere recognition | a smooth closed surface `Σ` with `Σ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` is diffeomorphic to it | none; partial: `Morse/CompactCriticalValues.lean:218`, `CubicCancellation.lean:179`, `SaddleMinimumStrip.lean:21` | **L** |
| **L7** cap | `k = 3`: glue a smooth `ClosedCell 3` along the L6 diffeomorphism, transport the homeomorphism through the cone extension | `Homeomorph/SphereExtension.lean:71`, `Attachment/CellExtension.lean:41`, `Handle/Manifold.lean` | S |
| **L8** closing off | `(𝓡∂ 3).boundary N = ∅ → BoundarylessManifold (𝓡∂ 3) N →` a `ChartedSpace (EuclideanSpace ℝ (Fin 3)) N` with `IsManifold (𝓡 3) ∞ N`; then `ULift` to `Type u` | `Manifold/InteriorAtlas.lean:17,33`; `Manifold/ULift.lean` (audit: its orientation half is sorried) | S |
| **L9** assembly | induction over `exists_pl_three_handle_filtration`, base `(N 0).space = ∅`, concluding `PLSmoothingModelCompact 3` | L0–L8 | M |

Vacuity notes applied: L3/L4 are stated on the actual cell image `g '' …` produced by
`IsPLCellAttachment`, never on an arbitrary family of subsets that could be taken empty; the
intrinsic boundary of a handle cell is `g '' stdSimplexBoundary d`, never the ambient `frontier`;
**Correction after the first skeleton review (2026-09-21, digest AN):** L3/L4 smooth only the *image* of the attaching region, not `ψ`; parameter matching is the attachment leaves' duty, and L7's cone extension settles topological matching only, not the smooth collar cap. L1's hypothesis (a smooth embedding into `∂N`) is what L3/L4 supply up to that reparametrisation, so nothing unsuppliable is
introduced; L6 speaks of an actual surface, not a `Prop` interface.

## 5. Estimate

Restricted (compact) C1: **10 leaves, total size class L**, the cost concentrated in
`L1 + L4 + L6` (L1 ≈ 1500–3500 lines of corner/collar work, L4 ≈ 2000–4000, L6 ≈ 3000–6000);
L0/L2/L5/L7/L8 ≈ 200–500 lines each. Unrestricted `PLSmoothingModel 3` adds a locally finite
exhaustion and a non-compact filtration — roughly one further L-sized leaf — and is off the goal
path. **Most uncertain leaf: L6**, smooth two-sphere recognition: the only leaf with no statement
in the tree and no clearly cheapest proof (the Morse route needs 2-dimensional critical-point
cancellation driven by `χ = 2`, and the partial inputs are local). L4 is second: no taming
statement for a curve *in a surface* exists, and the chart-to-chart induction is unwritten.

Against the other ledger sides: **A** has 18 open leaves, but narrow ones, eleven already reviewed
and frozen — wide and shallow. **B** has 8, of which `Section34CellDiagram` alone is comparable to
all of C1. C1 is **narrow and deep**: 10 leaves, three of them L, the cost in 2-dimensional
differential topology no other lane needs. It parallelises badly and is best started once A or B
frees a lane.
