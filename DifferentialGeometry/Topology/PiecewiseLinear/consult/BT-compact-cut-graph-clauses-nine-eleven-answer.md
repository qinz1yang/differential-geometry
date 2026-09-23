# BT — compact graph-frame clauses 9 and 11

**Review base:** `liao9yuan/differential-geometry-dev`, `moise-integration@d7cb053e8f08d51db90cab5f362db65f4d33c76a`, including the actual Batch 8 report and the owner-approved `Moise331OnTube` interface. Supporting definitions were also inspected at its ancestor `c4cad9c6`. Paths below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/` unless prefixed `Topology/`.

**Scope:** source-level mathematical review, not a Lean compilation or an axiom audit. Proposed declarations below are uncompiled interfaces, not additional assumptions for the frozen statement. Verdicts are evidence for the lead to verify.

## 1. Ordinary mathematical statements

Write `Cᵥ` for the source vertex cells, `Vᵥ = f₁ '' Cᵥ`, `Jₛ = h '' rim(s)`, and `Tₛ = section34CompactFaceTorus V s`. Clause 9 asks for an **actual core-marked toroidal sandwich**: `S₁ ⊆ Int Tₛ`, `Tₛ ⊆ Int S₂`, a product shell between `S₁` and `S₂`, and `Jₛ` a product core of `S₁`.

Clause 11 asks every nonincident vertex image to belong to an **unbounded component** of the complement of

\[
O_t=\bigcup_{v\text{ incident to }t}V_v\;\cup\!
     \bigcup_{s\text{ a face of }t}h([s]).
\]

This is neither a carrier-relative statement nor simply connectedness of `ℝ³ \ h([t])`. Also, the face-torus union runs over **all incident subdivision vertices**, not necessarily three; it is three in the worker's choice `K' = K`.

## 2. Truth and shortcut tests

| Item | Evidence-based verdict |
|---|---|
| Bicollared image-cell complement | **OK:** the lead's proposed topological route applies; no general cell-complement theorem is needed. |
| Entire clause 11 | **FIX the proof plan, not the signature:** additionally control the whole obstacle, including protruding vertex balls. |
| Clause 9 | **OPEN, expected dischargeable:** the tree supplies unmarked torus recognition, but the controlled, marked-core producer still needs proof. |

No counterexample satisfying the frozen leaf's complete hypotheses was established. In particular, a winding-two curve or a contractible circle inside an arbitrary solid torus refutes only the shortcut “circle inside torus ⇒ spine”; it is **not** a counterexample to this jointly chosen dual-cell construction. Empty cells and lower-dimensional tetrahedra are excluded by the ball and simplex hypotheses; `ε > 0` permits arbitrarily fine choices. Do not use ambient `frontier` as the intrinsic boundary of a lower-dimensional cut cell.

## 3. One shared, nonvacuous fixture

Use a polyhedral 3-ball consisting of two tetrahedra sharing a face, an open ball `V` containing it, and the nonidentity affine embedding `h(x₁,x₂,x₃)=(x₁+x₂/5+1,x₂,x₃)`. Fix, for example, `ε=10⁻³`; take a sufficiently fine compatible collar triangulation and its graph dual cells. Set `f₁=h`, so approximation is exact, while outer cells and nonincident vertex/tetrahedron pairs remain nonvacuous. The named `h331` input has its intended conditional supplier `moise331OnTube h323 h324 h264`. This is a common geometric test fixture, **not a checked Lean inhabitant of the complete output package**; the marked-core and cut-incidence certificates remain the obligations identified below.

## 4. Dischargeability and exact existing interfaces

### Clause 11: the correct theorem is already available

The relevant namespace is `DifferentialGeometry.Topology`, and the direct theorem is in **`Topology/ClosedBallImage.lean`**, not the smooth `SphereSeparation` assembly:

```lean
isConnected_compl_of_homeomorphClosedBall_of_isBicollared
    [NoncompactSpace E]
    (hrank : 1 < Module.rank ℝ E)
    (φ : B ≃ₜ Metric.closedBall (0 : E) 1)
    (hbi : IsBicollared (frontier B)) : IsConnected Bᶜ
```

Here the ambient section requires a finite-dimensional real inner-product space. Take `E = EuclideanSpace ℝ (Fin 3)` and `B = h '' convexHull ℝ (t.1 : Set E)`. The simplex is compact, convex and full-dimensional. Its cell homeomorphism transports through `hh` restricted to it; `IsTopologicalCell.image_of_continuousOn_injOn` in `Section34CompactFaceEnvelopes.lean` supplies exactly that image-cell step. For the rank argument, the existing `bicollared_cell_complement_connected` in `TameNestedCells.lean` uses:

```lean
exact isConnected_compl_of_homeomorphClosedBall_of_isBicollared
  (by rw [← Module.finrank_eq_rank']; norm_num) φ hbi
```

The lower-level `Topology/BicollaredComplement.lean` theorem `isConnected_compl_of_isBicollared_frontier` requires: a Hausdorff, connected, locally path-connected ambient space; `IsClosed B`; compact, connected `frontier B`; nonempty `interior B`; nonempty `Bᶜ`; and its bicollar. The closed-ball theorem supplies all the set conditions. `NoncompactSpace E` rules out a compact ball-image equalling the ambient space. Neither theorem requires smoothness or a global extension of `h`.

**Transport is substantially already written.** `Topology/OpenEmbeddingFrontier.lean` proves

```lean
frontier_image_eq_image_frontier hV hcont hinj hPV hP
-- frontier (h '' P) = h '' frontier P
```

with `hP : IsCompact P`, `P ⊆ V`, and continuity/injectivity on open `V`. Invariance of domain, via `isOpen_range_of_isOpen_subtype`, upgrades `hh` to an open embedding. Crucially, `Topology/BicollarNeighborhood.lean` already proves

```lean
ThreeManifold.TwoSidedCollar.isBicollared_image
  (c : ThreeManifold.TwoSidedCollar e)
  (hU : Set.range c.toFun ⊆ U)
  (hf : IsOpenEmbedding (fun x : U => f x)) :
  IsBicollared (f '' Set.range e)
```

Thus the missing **small wrapper**, rather than missing collar-image theory, is:

```lean
-- Proposed wrapper; not compiled here.
isBicollared_frontier_image_of_isEmbedding
    (hV : IsOpen V) (hh : IsEmbedding (V.domRestrict h))
    (hP : IsCompact P) (hPV : P ⊆ V)
    (hbi : IsBicollared (frontier P)) :
    IsBicollared (frontier (h '' P))
```

Shrink the source collar into `V` using compactness before composing. The actual `IsBicollared` uses `(frontier P) × ℝ`, not `S² × (-1,1)`. `exists_twoSidedCollar_of_closedInterval` and `TwoSidedCollar.ofOpenInterval` already handle that conversion.

For a tetrahedron, `Bicollar.lean`'s `IsCombinatorialManifoldWithBoundary.exists_bicollar_of_isConnected` supplies the closed PL collar: use the **larger ambient collar triangulation `M`**, and the simplex-boundary sphere `L`, not the tetrahedron as ambient manifold. Finiteness, the sphere's connectedness, and disjointness from `∂M` follow from `t ⊆ C ⊆ Int |M|`; two-sidedness follows from `Topology.isTwoSided_frontier` and its `preimage_of_isInducing` transport. Promote the relative neighborhood to an ambient one since `L ⊆ Int |M|`, then apply the closed-interval converter.

**What still separates this from clause 11:** `O_t ⊆ h([t])` is false as a proposed inclusion in general; entire incident vertex balls may protrude. A precise sufficient, source-only additional brick is a PL ball `B_t ⊆ V` with

\[
[t]\cup\bigcup_{v\in t}C_v\subset\operatorname{Int}B_t,
\qquad B_t\cap(K.\mathrm{vertices}\setminus t)=\varnothing
\]

for the worker's `K'=K`. More precisely, with the same `M, K, hM, hK, hKM, hKint` inputs as the rim-buffer signature below, the proposed `exists_compactTetraExteriorBuffer` takes `t : Section34CompactSimplexIndex K 4` and returns:

```lean
let L := restrict K (section34CompactGraphSkeleton K)
∃ B : Set E3, IsPLBall 3 B ∧ B ⊆ interior M.space ∧
  (convexHull ℝ (t.1 : Set E3) ∪
    ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space) ⊆ interior B ∧
  Disjoint B (K.vertices \ (t.1 : Set E3))
```

Prove this for the **actual dual-cell construction**, using its flag/collar geometry; do not infer it from separation alone. Choose every prescribed `W v` additionally inside `Int(h '' B_t)` for all incident `t`, then invoke `Moise331OnTube`. Consequently `O_t ⊆ h '' B_t`, and each relevant `y` lies outside that image. The bicollar theorem applies to this buffered ball too. Its complement is connected and unbounded, and

\[
(h(B_t))^c\subset\operatorname{connectedComponentIn}(O_t^c,y)
\]

finishes clause 11. None of the six reported Batch 8 interfaces supplies this source buffer. An independently constructed finite escape-path certificate is an alternative; the existing `exists_pos_forall_not_isBounded_connectedComponentIn_of_finite` preserves such certificates under thickening but does not create them. `TopologicalCellComplementConnected` and Alexander-duality certificates remain unnecessary on this route.

### Clause 9: existing recognition versus missing marking

The source rim is PL; its image under a merely topological `h` need not be PL in the target coordinates. Construct the marked neighborhood in the source and transport its homeomorphism through `h`, rather than applying a PL-circle theorem directly to `h  rim(s)`.

`IsPLSphere.exists_solid_torus_neighborhood` in `CircleSolidTorus.lean` gives a finite combinatorial manifold neighborhood containing a prescribed polygonal circle, a topological solid torus, and an untwisted cylindrical diagram. Its exported conclusion gives **neither prescribed-neighborhood control nor `IsSpine`**. `exists_parametrized_solid_torus_complex_subset_open` in `SolidTorusOpenNeighborhood.lean` puts **some** torus in a nonempty open set; it does not surround the prescribed circle.

`isTopologicalSolidTorus_derivedNeighborhood_circle` in `SolidTorusProduct.lean` gives an unmarked product for a connected combinatorial circle in an orientable ambient 3-manifold. `isTube_graphDualCell` in `TubeOfGraphDualCells.lean` supplies the actual graph tube and splitting disks, not a marked circle product. `Section34FaceTorusCycle` supplies the finite cyclic-incidence argument; for the compact case extract its argument and apply `isCombinatorialSolidTorus_iUnion_of_cycle` in `CyclicBallUnion.lean` to PL vertex balls, consecutive disk intersections, disjoint nonconsecutive balls and empty triple intersections. Do **not** instantiate the boundaryless frame or require the complete graph frame while constructing it.

The exact missing geometric brick is a **core-marked buffer for this source cyclic union, including its arms**, not unrestricted regular-neighborhood uniqueness. A sufficient interface for the worker's construction is:

```lean
-- Proposed signature; E2/E3 are EuclideanSpace ℝ (Fin 2/3).
-- D2 := Metric.closedBall (0 : E2) 1; S1 := Metric.sphere (0 : E2) 1.
exists_compactRimCoreBuffer
    {M K : Geometry.SimplicialComplex ℝ E3} [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hKM : K.faces ⊆ M.faces) (hKint : K.space ⊆ interior M.space)
    (s : Section34CompactSimplexIndex K 3) :
    let L := restrict K (section34CompactGraphSkeleton K)
    let Ns := ⋃ v ∈ (s.1 : Set E3), (graphDualCell M L v).space
    ∃ P : Set E3, P ⊆ interior M.space ∧ Ns ⊆ interior P ∧
      ∃ Φ : (D2 × S1) ≃ₜ P,
        section34CompactSimplexRim s.1 =
          Subtype.val '' (Φ '' {q | (q.1 : E2) = 0})
```

This zero-marking deliberately preserves what the existing abstract product conclusions forget. Establish it from the dual-cell cone/edge models and a compatible outer collar. Mere abstract torus recognition is insufficient.

Choose such `Pₛ` **before `f₁`**. Intersect the finitely many allowed `W v` with `Int(h '' Pₛ)` for incident faces. After approximation, set `S₂=h '' Pₛ`; clause 8 puts its marked core inside `Int Tₛ`. Shrink the disk coordinate in that *same marked product* to obtain `S₁ ⊆ Int Tₛ`, retaining the core and the radial toroidal shell. This is a separate scale choice, not automatic from `Tₛ` being a torus.

`IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior` in `InnerSolidTorusToroidalShell.lean` instead takes compact `Q ⊆ Int Y` and produces an inner torus **containing `Q`**. It neither marks `Q` as core nor constructs an outer torus around a prescribed inner one. Reuse its radial proof with the fixed, zero-marked product; do not apply its existential conclusion as though it retained that marking.

## 5. Right size and remaining cut obligations

The frozen existential leaf can retain its signature. Separate source geometry, finite neighborhood choice and transport; do not add their conclusions as permanent hypotheses or use the generator exporter to obtain its own sandwich input.

**Cut 7.** Start with the flag APIs of `DerivedNeighborhoodCells` and `DerivedNeighborhoodRestriction`.
Identify `C_w ∩ [σ]` and `D_e ∩ [t]` in the face complexes.
Use `Section34CompactResidualCells` for face disks and residual balls.
For outer kinds, use the collar triangulation, `ManifoldComplement` and relative boundary restrictions.
Still prove the intrinsic-boundary identifications; PL-ball recognition alone is insufficient.

**Cut 8–11.** Prove the common flag-cell decomposition first.
Its facet descriptions give clause 8 and common subfaces give clause 9.
Distinct labels and strictly smaller face dimension give clause 10.
The residual descriptions plus the vertex-cell union give exactly `C ∪ N` in clause 11.
Do not invoke `compactSourceFace_iff_cutLe` to manufacture its own `hcut` input.

**Cut 26.** Expand the splitting disk as the intersection of its two end cells.
Use `graphDualCell_space_inter_of_mem` from the graph-dual-cell machinery.
Exclude a third vertex cell through the flag description of triple intersections.
Translate endpoint equality into `w.1 ⊆ e.1`.
The nonincident-simplex separation theorem alone does not state this intersection result.

**Cut 28.** Use the two `closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_*` descriptions.
A face disk is its face-derived cell.
A tetrahedron residual is the union of its own derived cell and its facet-derived cells.
Transport the incident face's derived cell through restriction and include it in that union.
No new separation or annulus theorem is involved.

## 6. Five-step proof route and final sub-leaves

1. Build the compatible ambient collar triangulation and complete the source flag-cell incidence package.
2. Produce marked rim buffers and tetrahedron exterior buffers, then choose all finite `W v` constraints together with the existing carrier/separation margins.
3. Apply the actual `Moise331OnTube` input once, preserving the chosen source tube.
4. Recognize each target cyclic union; shrink inside the same marked outer product to obtain clause 9.
5. Transport the buffered-ball bicollars, apply the existing complement theorem and component monotonicity to obtain clause 11.

The likely expensive step is **marking the source cyclic union with arms**, followed by the filled-tetrahedron buffer; not Jordan–Brouwer. The shared fixture remains uncompiled. No complete-hypothesis counterexample or justification for changing a frozen statement was found.

| Proposed sub-leaf / work item | Size |
|---|---|
| `isBicollared_frontier_image_of_isEmbedding` — package existing collar-image and frontier transport, with shrinking | **SMALL** |
| `isConnected_compl_image_of_bicollaredCell` — closed-ball theorem specialization | **SMALL** |
| `isCombinatorialSolidTorus_compactFaceTorus_of_cycle` — compact adapter without a complete-frame premise | **SMALL** |
| `exists_compactRimCoreBuffer` — actual dual-cell cyclic union, arms included, zero-marked product and outer room | **MEDIUM** |
| `exists_innerToroidalShell_of_zeroMarkedProduct` — retain the core while reusing the radial shell construction | **SMALL** |
| `exists_compactTetraExteriorBuffer` — source PL-ball buffer containing the whole incident-cell obstacle and excluding foreign vertices | **MEDIUM** |
| `compactExterior_of_ballBuffers` — finite neighborhood choice, complement theorem, unbounded-component inclusion | **SMALL** |
| `compactDualCutFlagIncidence` — patches, arcs, points, outer collar and boundary/intersection formulas | **MEDIUM** |
| `compactDualCutCover`, `compactVertexSplitIncidence`, `compactFaceDisk_subset_residualBall` | **SMALL** |
| Unrestricted marked regular-neighborhood uniqueness / a general annulus theorem, if pursued instead | **NEW_THEORY — avoid for BT** |
