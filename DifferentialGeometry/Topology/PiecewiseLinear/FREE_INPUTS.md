# FREE INPUTS — the single progress ledger for the Moise route

**This page is the only yardstick of progress.** Progress is *not* the number of files, lines,
proved lemmas or conditional assemblies. Progress is this list getting shorter.

**Goal.** A closed simply connected topological 3-manifold is homeomorphic to `S³`, from the
smooth Poincaré theorem (main repository) through triangulation and smoothing. Only the
orientable case is needed (simply connected ⇒ orientable); only existence of structures is needed.

## Rules

1. An item is **OPEN** unless the tree contains a theorem whose conclusion is that item and whose
   hypotheses are only instance binders. "Proved conditionally" is OPEN, with its conditions
   listed underneath as further items.
2. A `def … : Prop` naming an obligation is OPEN until such a theorem exists. A structure or
   predicate with no inhabitant theorem on a non-degenerate object is **UNTESTED**, and nothing
   may be built on it.
3. Whoever commits a change to the hypothesis list of any endpoint named here updates this page
   **in the same commit**. An audit that disagrees with this page must point to the declaration
   (file:line) that proves the item, or the page stands.
4. Last verified against source: **2026-09-21, commit of `consult/H-section34-celldiagram-review-digest.md`**.

## How to audit (no compiler needed)

```
# theorems whose conclusion is a named obligation (must print a line for an item to be CLOSED)
grep -rnE "^theorem [A-Za-z0-9_']+ *: *(Moise352Open|GeneralPositionInDoubleBufferedStatement|DescentStepOrientableStatement|PLSmoothingModel|Moise351|Moise341|Moise331)(\.\{u\})?( [0-9]+)? *:=" DifferentialGeometry
# a line `theorem foo : Item → …` CONSUMES the item and is excluded by the pattern; the pattern
# does catch proved items (try it with Moise308Nested in place of the list)
# hypotheses of the endpoints
grep -n -A4 "^theorem moise304_of_generalPositionBuffered_of_descentStepOrientable" DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CoverReductionOrientableProducer.lean
grep -n -A3 "^theorem plApproximationManifold_three_of_open" DifferentialGeometry/Topology/PiecewiseLinear/Moise352OfOpen.lean
grep -n -A8 "^theorem exists_isManifold_three_of_plApproximation_of_plSmoothing" DifferentialGeometry/Topology/PiecewiseLinear/Smoothing.lean
```

## The tree of inputs

### Level 0 — the top endpoint in this checkout
`exists_isManifold_three_of_plApproximation_of_plSmoothing` (`Smoothing.lean:63`): a compact
Hausdorff topological 3-manifold has a smooth structure, **from** `PLApproximation 3` **and**
`PLSmoothing 3`.

| Input | Reduced to (proved) | Status |
|---|---|---|
| `PLApproximation 3` | `PLApproximationManifold 3` (`ApproximationManifold.lean:76`) ⇐ `Moise352 3` (`Endgame.lean:9`) ⇐ **`Moise352Open 3`** (`Moise352OfOpen.lean:40,45`, inward push proved) | OPEN → **B** |
| `PLSmoothing 3` | **`PLSmoothingModel 3`** (`Smoothing.lean:27`) | OPEN → **C** |
| smooth Poincaré | main repository, not this checkout | external → **D** |

### A — loop-theorem side (orientable): delivers 30.4 and tame 30.5, which §34 consumes
Endpoint: `moise304_of_generalPositionBuffered_of_descentStepOrientable`
(`LoopTheorem/CoverReductionOrientableProducer.lean:278`), and `moise305_tame_of_moise304`.
**Two hypotheses, both OPEN.** Everything else on this side is proved: entry, complexity
induction, return leg, Stallings tower with orientability in the motive, covers of orientable
complexes orientable, `Moise252 → Moise304 → Moise305Tame`.

| ID | Item | Status |
|---|---|---|
| **A1** | `GeneralPositionInDoubleBufferedStatement` (`LoopTheorem/LemmaTwoBuffered.lean:167`) | **OPEN**; leaves = the `sorry`s of `Skeleton/GeneralPositionInDouble.lean` (external review pending) |
| A1.1 | adapted half-space charts of the double, arbitrarily small (leaf `exists_adaptedHalfSpaceChart_in_double`) | open (lane H); reviewed **OK, frozen** |
| A1.2 | finite adapted cover of the whole compact double, `⋃ j, W j = univ` | **PROVED** in the skeleton (`exists_finiteAdaptedCover_of_compactSpace`), replacing the false cover of the double point set |
| A1.3 | cut-out piece of a source disk **with boundary**, frozen outer collar (leaf `SingularTwoCell.exists_cutOutPiece_of_closure_subset`) | open (lane H); reviewed **OK, frozen** |
| A1.4 | controlled preparation (`[MetricSpace M] [CompactSpace M]`, `hfiber`): whole-source control complex `T`, `κ`, an **ambient** scale `δ` with `∀ g, (∀ x, dist (g x) (D x) < δ) → StarInj T g → UniformInjectivityScale … κ ∧ fibres ≤ 2`, then a **chart** scale `ε` with the conversion `dist z (ec (D x)) < ε → z ∈ ec '' V ∧ dist (ec.symm z) (D x) < δ` (leaf `exists_normalizationPreparation_on_prescribedRegion`) | open (lane H); fourth review **OK, frozen** (the multiplicity supplier still needs its `[MetricSpace]` generalisation) |
| A1.5a | **protected subdivision** (was the pairing seed): consuming the stable blocks over `Z ∩ P_k` in the chart `ec_k` and the preparation certificate (`κ, δ, ε, hcert, hconv`), `∃ R τ K` such that EVERY `τ`-admissible vertex map is controlled, keeps normality over `Z ∩ K` at fibres meeting a frozen-vertex simplex, and keeps the stable blocks with margin `η/2` (leaf `exists_protectedSubdivision_in_adaptedChart`). No pairing, no open family, no seed centre | open (lane H); seventh review 2026-09-21: **OK, frozen** (`consult/V-generalposition-seventh-review-digest.md`) |
| A1.5b | **relative multi-chart generic production**: for the fixed `R` and every `τ > 0`, an admissible vertex map with the guard and the wall conditions against the affine pieces of the chart transitions on the fixed overlap blocks (leaf `exists_genericVertexMap_in_adaptedChart`); the transition subdivision itself is a separate leaf `exists_transitionSubdivisionOnOverlap` | open (lane H); transition subdivision leaf **frozen**; generic production leaf, eighth iteration 2026-09-21: free germs now require `R.space` to be a source neighbourhood of every fibre point (`FreeSourceGerm`; sanity lemma proved), wall clauses on free interior germs, new `hboundaryAffine` output for free boundary germs (the transition is affine on a physical half-neighbourhood); **unreviewed** |
| A1.5c | stable ⇒ normal: a margin-stable crossing block has PL normal double crossings (leaf `hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock`) | open; seventh review: **OK, frozen**; auxiliary |
| A1.6 | literal PL gluing (leaf `exists_gluedCell_of_vertexMap_in_adaptedChart`) | open (lane H); reviewed **OK, frozen** (byte-identical); bridge `eq_regionGluedMap_of_eqOn` proved |
| A1.7 | global invariants of the glued cell (leaf `exists_globalInvariants_of_gluedCell`) | open (lane H); third review **OK, frozen** (only the allowed rename `ε → δ` in its closeness hypotheses) |
| A1.8 | crossing leaf, eighth iteration: (a) normality over `Z ∪ closure W`; (b) later-chart blocks only over `(Z ∪ closure W) ∩ P_m ∩ K⁺`, assembled from four strata — its own content on free interior germs, `hboundaryAffine` on free boundary germs, the mixed-layer leaf on non-free germs, and **off `K` a PROVED chain** in the assembly (compact localisation → fibre-based retention → union of block families) (leaf `exists_normalCrossings_of_gluedCell`) | open (lane H); **unreviewed** |
| A1.8a | compact localisation of stable blocks: `HasStableCrossingBlocks … Q η` + injectivity scale + `Q' ⊆ Q` compact `⊆ N` open ⇒ `HasStableCrossingBlocksIn … Q' N η` (leaf `hasStableCrossingBlocksIn_of_isCompact_subset`) | open; new, **unreviewed**; expected true, > 250 lines (recentring blocks; needs restriction / translation API for `IsPLHomeomorphOn`) |
| A1.8b | later-chart margin blocks at **non-free (mixed) germs** over `Z ∩ P_m ∩ K⁺` (leaf `exists_laterMarginBlocks_of_mixedGerms`) | **NEEDS_PROOF — mathematically unverified**, consult `consult/U-mixed-later-margin.md` open; PROVED around it: every double point of the new map over `closure W` is a free source germ (`freeSourceGerm_of_mem_closure`), so the mixed layer never meets the new region; the open case is a *new* double point over `Z` with one moved and one frozen or unmoved preimage |
| A1.9 | induction with the new invariant — (a) normality over `Z_k`, (b) `HasStableCrossingBlocks` in `ec_m` over `Z_k ∩ closure (V_m \ closure W_m)` for all `m ≥ k` —, base case, endpoint extraction, boundary loop, compactness of the double, strengthened finite cover (`closure (V j) ⊆ ec.source`), retention of blocks on untouched data, flat-sheet inhabitant of the block predicate | **PROVED modulo the leaves above**: `Skeleton/GeneralPositionInDouble.lean` compiles with exactly 12 `sorry` leaves and none in the assembly (checked 2026-09-21) |
| **A2** | `DescentStepOrientableStatement` (`LoopTheorem/LemmaTwoOrientable.lean:61`) | **OPEN**; leaves = the `sorry`s of `Skeleton/DescentStepOrientable.lean` (reviewed: `consult/G-descent-skeleton-review-digest.md`) |
| A2.1 | closed branch, two circles, nested | **PROVED** `exists_descendingSurgery_of_nested_innermost_cleanDisk` (`LoopTheorem/ClosedBranchNestedDescent.lean:245`) |
| A2.2a | closed branch, two circles, disjoint — geometric cap producer: for every open `V` with `D(Q) ⊆ V ⊆ interior (C \ BdM)`, a larger source disk `E'` and a PL embedded cap `Δ' ⊆ V` (leaf `exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk`) | open, not started; reviewed (false over a bare `ChartedSpace`), repaired with `[HasGroupoid M (plGroupoid 3)]`, **frozen** |
| A2.2b | the same — surgery consumer: cut-and-paste along the cap, branch retention, the three invariants (leaf `exists_descendingSurgery_of_adaptedCleanCap`); the disjoint analogue of `IsNestedDiskReplacementCell` does not exist yet | open, not started; reviewed **OK, frozen** |
| A2.3 | closed branch, one circle: impossible in an orientable manifold (leaf `not_branchPreimage_eq_of_isOrientable`, **frozen**; surviving name `NormalSingularCellData.not_branchPreimage_eq_of_isOrientable`). Own skeleton `Skeleton/ClosedBranchCaseOne.lean`, repaired after review I: **1 open leaf** (A2.3.b) | open |
| A2.3.a | marked crossing chart at a source point of the branch | **PROVED** `NormalSingularCellData.exists_isMarkedCrossingChartAt` (`LoopTheorem/ClosedBranchCaseOneMarkedChart.lean`), the frozen statement verbatim; audited 2026-09-21 |
| A2.3.b | orientation-free **source-tracked** branch tube: derived neighbourhood of a complex in a subdivision of `L`, end map permuting four marked rays in cyclic order, the rays realised on the actual collar `φ(rᵢ,t) = ι(D(ρ(aᵢ t, sᵢ t)))` with alternating pairing (leaf `exists_isSourceTrackedBranchTube`). Weakened 2026-09-21: the clauses `trace` and `branchInterior`, consumed by no proof, were dropped (lead verified by grep; conclusion strictly weaker than the reviewed one). Scoped (`consult/C-or1-sign-vs-tube-scope.md`): the marked **sign argument is not cheaper** — the tree has no bridge from `IsOrientable` (a coherent simplicial orientation) to any chart-level or link-level orientation; the only bridge is the Möbius chain behind `not_closedBranchCase1`. Tube route ≈ 2000–3500 lines; sub-bricks: marked link normalisation at each face of the branch (the uncertain one: `hsep`, `hsep'` at a vertex), marked cone-pair extension, cyclic splice, four source arcs, bookkeeping | open (W-B); statement frozen (weakened form); not started |
| A2.3.c | source-ray transport, circuit lifts in a connected double cover end at the other fibre point, `u²` fixes the rays, sheet exchange, tube orientability, assembly | transport, circuit lift, `square_fixes_rays`, `isSheetExchange` and the two predicates are **PROVED and committed** in `LoopTheorem/ClosedBranchCaseOneTransport.lean` (audited); the assembly stays in the skeleton, proved modulo A2.3.a–b (2 `sorry`s, checked 2026-09-21) |
| A2.4a | boundary branch: PL tube with side containment, boundary equality, end-disk buffer (leaf `isPLBoundaryTubeProducer_double`; `IsPLBoundarySide` now carries `IsClosed BdM`, `BoundaryAdaptation.lean:56`) | open (lane S); statement **frozen** |
| A2.4a′ | realisation of the boundary neighbourhood in the double (leaf `NormalSystem.exists_boundaryNeighborhood_realization`) | open (lane S); **frozen** |
| A2.4a″ | the quarter-turned tube chart is again a PL seam tube chart (leaf `nonempty_plSeamTubeChart_comp_crossQuarterTurn`) | open (lane S); reviewed **OK, frozen**; small |
| A2.4b | boundary branch: both boundary word witnesses from **one** cut | **PROVED** `NormalSingularCellData.exists_boundaryWordWitnesses_of_cut` (`LoopTheorem/BoundaryCaseOfCut.lean`; frozen statement minus an unused instance; lane F, audited by the lead 2026-09-21) |
| A2.4b′ | the PL reading, for the tube chart **or** its quarter turn, given the tube's boundary equality (leaf `exists_plCrossSeamReading_of_isCrossRegluedCell`) | open (lanes F/S); **frozen** after repair |
| A2.4c | boundary branch: assemblies conclude side + buffer | **PROVED** `…exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing`, `…_preserving` (`LoopTheorem/BoundaryCaseFromTube.lean`; frozen statements verbatim; lane F, audited 2026-09-21) |
| A2.4d | joint non-degenerate fixture: branch + both candidates + tube + reading + both witnesses on one tuple | open (F11), **partial 2026-09-21**: on one tuple — a genuine normal disk of complexity exactly 2 (first non-degenerate inhabitant of `NormalSingularCellData`), two boundary branches, the actual tube with side containment and boundary equality, the explicit cross candidate and its PL reading; the retained cap's boundary is not injective (`crossingProductCell_exists_crossReading`, `LoopTheorem/CrossRegluedSourceProductCut.lean`; lead audit clean). Still owed: the direct candidate with both word witnesses on the same tuple, a regular neighbourhood with buffer (`IsPLBoundarySide` not yet produced: corner half-space charts), the reversing model; until then A2.4 stays UNTESTED as a whole |
| A2.5 | wiring into the statement | **PROVED modulo the leaves above**: `descentStepOrientableStatement` in `Skeleton/DescentStepOrientable.lean` compiles with exactly 7 `sorry` leaves and none in the assembly (checked 2026-09-21) |

### B — §34–35 side
| ID | Item | Status |
|---|---|---|
| **B1** | `Moise352Open 3` (`OpenSourceReduction.lean:297`) | **OPEN**; reduced (proved, `moise352Open_of_section34CellDiagram`, `Section34Endpoint.lean`) to the single obligation **`Section34CellDiagram`** = B1.b |
| B1.a | terminal labelled PL-cell assembly + corrected endpoint | **PROVED** `exists_isPLHomeomorphInto_of_labelledCells` (`LabelledCellAssembly.lean`), manifold-level locally finite PL pasting with inverse (`LocallyFinitePLPastingManifold.lean`). **Tested** on a non-degenerate tuple: the 23-label bent double tetrahedron, no free hypotheses, two 3-cells meeting in a common triangle, no affine map realises the matching (`exists_isPLHomeomorphInto_bentTetrahedra`, `exists_bentTetrahedra_top_cells_inter_eq`, `not_exists_affineMap_image_eq_bentTetrahedraTargetCell`, `LabelledCellAssemblyFixture.lean`). A fixture of the *assembly*, not progress on B1.b |
| B1.b | `Section34CellDiagram` (the final-diagram producer = P0–P8): controlled frame, joint graph selection, generator transfer, face balls, protected compression, bigon slide, normalization, exterior face disks, tetrahedron and vertex recognition | open, not started; statement externally reviewed **OK** (`consult/H-section34-celldiagram-review-digest.md`); proved ingredients: `moise308Nested`, link connectivity, marked-circle sectors, locally finite PL gluing, labelled normalization, tolerance control, chart-local 34.1 **from** `Moise341` |
| B1.b.T | **terminal skeleton** `Skeleton/Section34Terminal.lean` (P6–P8 + exporters → `Section34CellDiagram`), second repair 2026-09-21 on the shared real module `Section34Frame.lean` (audited; realisation ambient now a parameter / existential `ℝ^N`; carriers are closed PL balls; `IsCombinatorialManifold 3 𝒦`, `IsSubdivision 𝒦' 𝒦`, equal realisation maps in the cut frame). 5 `sorry` leaves, none in the assembly. All `Section34*` predicates still **UNTESTED** (no inhabitant theorem) | unreviewed in this form |
| B1.b.T1 | P0–P5 composite: `∃ N 𝒦 𝒦' data, Section34NormalPlus …` (leaf `exists_section34NormalFamily`); the endpoint of the next skeleton; **not** produced by the controlled-35.1 skeleton, which gives P1 only | open; third review 2026-09-21: **OK** — statement frozen pending the lead's due-diligence pass (`consult/P-section34-third-review-digest.md`) |
| B1.b.T2 | P6: `NormalPlus → ∃ disks, Section34FaceDiskFamily` (leaf `exists_section34FaceDisks`) | open; third review 2026-09-21: **OK** — statement frozen pending the lead's due-diligence pass (`consult/P-section34-third-review-digest.md`); the worker's foreign-arc objection is answered by a **derived lemma** (owed: `section34_faceArc_subset_faceDisk_iff` ; the **`IsPLCellOn` API is now PROVED** (2026-09-21, `PLCellOnBoundary.lean`, `PLCellOnInterior.lean`, lead audit clean): `IsPLCellOn.boundary_eq`, `.dim_eq` (all dimensions), `.boundary_eq_frontier`, `.sdiff_boundary_eq_interior`, `.image`, `.image_boundary_interior`, and the relative nowhere-density `IsPLCellOn.inter_eq_empty_of_subset_iUnion` (a finite union of ≤1-cells has no relative interior in a 2-cell) — the fact the owed P6 lemma was missing; missing fact named by the worker: a compact polyhedron of dimension ≤ 1 has empty interior *relative to a PL 2-cell* — the tree only has ambient-interior versions), no new hypothesis |
| B1.b.T3 | P7: `… → ∃ residuals, Section34ResidualPlus` (leaf `exists_section34ResidualBalls`), carriers now closed PL balls | open; third review 2026-09-21: **OK** — statement frozen pending the lead's due-diligence pass (`consult/P-section34-third-review-digest.md`) |
| B1.b.T4 | source face bridge `src m ⊆ src l ↔ m ≤_cut l` (leaf `section34SourceFace_iff_cutLe`, new) and P8 target recognition consuming it (leaf `section34TargetRecognition`) | open; third review 2026-09-21: **OK** — statement frozen pending the lead's due-diligence pass (`consult/P-section34-third-review-digest.md`) |
| B1.b.1 | controlled source triangulation: a compatible locally finite triangulation of an arbitrary open subset of an atlas-defined PL 3-manifold, subordinate to P0's control supports (true classically; **not formalised here**) | open, not started |
| B1.b.2 | target recognition: PL-ball presentations, intrinsic boundaries and exact intersections of `V_v, E_e, Δ_σ, X''_{tv}, R_t, a'', I'', p''` (P1, P6–P8, marked-sector condition) | open, not started |
| B1.b.3 | target local finiteness `hLFt` from `T_λ ⊆ H_λ ⊆ h(U)` with `(H_λ)` locally finite in `h(U)`, without the assembled homeomorphism | **PROVED** as an exporter in `Skeleton/Section34Terminal.lean` (`exists_nhds_finite_of_subset_carrier`); what remains is producing the carriers inside `h '' U`, part of B1.b.T1 |
| B1.b.4 | parent-carrier exporter: top-cell carriers inherited by lower cells along a chosen incident top label | **PROVED** as an exporter in `Skeleton/Section34Terminal.lean` (`carrier_subset_and_dist_lt_of_parent`) |
| B1.b.5 | P0 fixes control data only; the neighbourhood `N`, the cut diagram and `f₁` are chosen jointly in P1 | design constraint on B1.b, not a theorem |
| B1.c | 35.1 in **controlled** form, as P1 needs it. Skeleton `Skeleton/ControlledGraphNeighborhood.lean`, second repair 2026-09-21: endpoint `ControlledGraphNeighborhoodStatement` over an arbitrary realisation ambient `Ea`; from `Moise341` and 6 `sorry` leaves, none in the assembly. PROVED: the dual-cell paste, L1(2), L1(3), the `ψ`-estimate, target local finiteness, and the **generator clause** (Lemma 2) from the nested-torus certificate via the unconditional `moise308Nested` and a homeomorphism-of-pairs transport. `Moise351` as stated is consumed nowhere on the live route | unreviewed in this form |
| B1.c.1 | source side: subdivision, typed cut frame, `N ⊆ W`, fine carriers (leaf `exists_section34CutFrame`) | open; **changed after review S** (one added output `Q w ⊆ H s` for incident triangles; carriers now lie in charts), unreviewed in this form; the rest byte-identical to the version judged OK and confirmed by the due-diligence pass |
| B1.c.2 | vertex preparation, third form: pierced cells `C'_v ⊆` approximation domains `C''_v`, piercing circles, tubes `T_e ⊆ Int S_e` (solid tori, regular neighbourhoods), annuli `A_e = ∂C'_v ∩ T_e`, `B_e ⊆ ∂C'_w` with named end circles, Lemma 1's input through `CarriesFundamentalGroupOnto`, `ε_v` with margins against both `∂C'_v` and `∂C''_v`, **explicit target charts** (leaf `exists_section34VertexPreparation`, 24 fields). The vertex approximation is now a **PROVED theorem** from `Moise341` through that chart | open; fourth repair 2026-09-21: preparation with 35 fields — common triangle chart from produced data (`hQchart`, proved one-liner), outer torus `(ct s, Sd s)` with the exact `moise308Nested` spine predicate and buffer, pairwise disjoint tubes, source-side marking, component certificates, sum margins; `C_v ⊆ C'_v` dropped (the book does not assert it); unreviewed |
| B1.c.3 | piercing package with conditions (2)–(8), (8) carrying the local crossing model `HasPLCrossingAt` (leaf `exists_section34PiercingPackage`); protected circle removal: a single step with fixed supports (leaf `exists_section34ProtectedCircleRemovalStep`), finite descent at one label **PROVED**, simultaneous version for all labels (leaf `exists_section34ProtectedCircleRemoval` — the worker doubts it: local finiteness of the supports is stated in `⋃ Sp e`, not in `h '' U`) | open; fourth repair: package consumes the completed preparation; PROVED for every `ε`-close family: condition (2), the disjointness halves of (5), (6), disjoint supports (`section34MarginConditions`); the interior-containment halves of (3)–(7) stay in the package leaf (they need the missing `IsPLCellOn` invariance-of-domain API); single step with isolated supports; one-label descent re-proved keeping all support clauses; simultaneous removal with local finiteness in `h '' U` and compact envelopes `K_v = H (car v)` — still a leaf (a real proof needs a well-ordering of labels and an eventual-value limit, > 300 lines); unreviewed |
| B1.c.4 | joint producer: ball recognition, exact meets, PL matching; outputs the marker clause, rim containment and the nested-torus certificate; now receives `hQsep`, `hQlf` (leaf `exists_section34EdgeMatching`) | open; fourth repair: joint producer consumes the pre-selected outer torus and outputs the inner torus with `Φ_σ` the restriction of the same chart; unreviewed |
| B1.d | `Moise341` (faithful, p. 239; one consumer, the proved chart-local form), `Moise331` (faithful, p. 230; no consumer yet) and what they rest on: §33.1 (L), §32 pseudo-cells and tubes (L, no goal-driven cut; **32.1 the most uncertain item**), §31 canonical configurations (M) ⇐ `Moise306` (faithful, UNTESTED), `Moise307` (**wrong statement**: concludes `HasCylindricalDiagram`, must conclude `IsCombinatorialSolidTorus`), `Moise308Nested` (PROVED) ⇐ a confined orientable variant of `Moise264` (plausibly from `Moise252` by cutting). Surface classification: §33 cites 22.9 once (Lemma 11), deletable; the capping route needs only `isPLSphere_two_of_faceEulerChar_eq_two` (proved). **Do not vendor** the external classification. Definitions missing: pseudo-cell, tube, handle decomposition of a tube, canonical configuration, source cut diagram | OPEN, not started; scoped 2026-09-21; proposed skeletons `Section33Approximation`, `CanonicalConfiguration`, `PseudoCellCapping`; none for 32.1–32.3 until their definitions exist |
| B1.e | how A's output (tame 30.5, the loop theorem) enters P3/P4 | **not yet stated in Lean** — the two sides meet only in the book so far |

### C — smoothing
| **C1** | `PLSmoothingModel 3` (`Smoothing.lean:27`) | **OPEN**; scoped 2026-09-21 (`consult/C1-smoothing-scope.md`): the goal needs only the **compact** case `PLSmoothingModelCompact 3` (homeomorphism type only; no orientability, no framing). Route: proved triangulation + proved PL handle filtration of derived neighbourhoods, a parallel smooth filtration handle by handle, cone cap. Closed since the Phase 2 audit: PL handle decomposition, triangulation bridge, Alexander cone extension, boundaryless conversion. Ten leaves sketched, not yet a skeleton; the three large ones: smooth handle attachment, taming a PL annulus in a smooth surface, recognition of a smooth surface homeomorphic to `S²` (most uncertain). Surface classification is **not** needed |

### D — external
| **D1** | smooth Poincaré theorem and its use on the smooth manifold produced above | main repository. As read on 2026-09-21: `smoothPoincareConjecture` is a `Prop` definition (unproved, producers conditional) in a gitignored worktree of the main checkout, `…/Surgery/Poincare.lean:30`; hypotheses `ChartedSpace (EuclideanSpace ℝ (Fin 3))`, `IsManifold (𝓡 3) ∞`, T2, compact, connected, simply connected; `topologicalPoincareConjecture_of_smoothStructureInput` (`:56`) is already stated against our output shape. Interface mismatches are one-liners (`Nonempty (IsManifold …)`, `ULift` of the target) |

**Due-diligence pass on the frozen leaves (2026-09-21, `consult/M-frozen-leaves-due-diligence.md`):**
an independent read-only audit unfolded every definition of the 15 frozen leaves: 13 confirmed,
2 suspect, 0 defect; the lead checked both suspects against the source and fixed them —
the 2b cap leaf had a vacuous binder `W` (its side hypothesis was really `Disjoint V BdM`; now
stated so), and the A1 crossing leaf did not receive the local injectivity of the glued cell that
its only proved supplier needs (now passed; the assembly had it). The three hypotheses added on the
reviewer's FALSE verdicts (`IsClosed BdM`, `HasGroupoid`, `MetricSpace`/`CompactSpace`) were found
justified, suppliable and essentially minimal.

**Due-diligence pass on the §34 terminal leaves (2026-09-21, `consult/Q-section34-terminal-due-diligence.md`):**
independent read-only audit of the six leaves the reviewer judged OK: 3 confirmed
(`exists_section34NormalFamily`, `exists_section34ResidualBalls`, `exists_section34CutFrame`),
3 suspect, 0 defect; the assembly wiring is correct in both directions. The three suspects share
one cause: **`IsPLCellOn` has no API** — missing are uniqueness of a PL cell's intrinsic boundary,
boundary = frontier in codimension 0, and "a set is not both a PL 1-cell and a PL 2-cell"; without
them `∂V_w = ⋃E ∪ ⋃X`, `∂E_e = ⋃I` are inputs nowhere. `section34SourceFace_iff_cutLe` silently
needs "every triangle carrying a face arc is a face of a tetrahedron" (one free `CutFrame` clause).
P6's OK is true but hollow: of the four cyclic-seam ingredients only "single crossing" is a field;
the innermost-disk step sits as an assumption in the composite leaf. Inhabitant advice: `∂Δ⁴ ≅ S³`
in `ℝ⁴` with `h = f₁ = id` (size L), with a `U = ∅` control first (S).

## Deliberately NOT on the goal path (may stay open forever)
Unrestricted `Moise251`; the non-orientable loop theorem and the one-circle closed case in a
non-orientable manifold; `Moise305` (non-tame); `TopologicalCellComplementConnected`; the
Hauptvermutung; boundary-relative approximation; cross-caps and the full classification 22.8–22.10.

**Correction 2026-09-21 (lead, checked against the book pp. 217 and 221).** `Moise264`, `Moise306`
and `Moise307` were listed here by mistake: 31.1 is "repeated applications of 30.7" and 31.2 of
30.8 (p. 221); the proof of 30.7 starts from 30.6 and takes a polyhedral compressing 2-cell from a
non-trivial `π₁` kernel (p. 217), which is the loop theorem for an interior two-sided surface. The
earlier ruling came from a citation census of §§33–35 only. They are now under B1.d.

## Count (the number an audit should quote)
Top-level OPEN items: **A1, A2, B1, C1** (+ D1 external). Expanded leaves currently open:
**A: 12 + 7 = 19** = the `sorry` leaves of the three skeletons (A1: 12 in `Skeleton/GeneralPositionInDouble.lean` after the redesign of the induction following consults L and O and the stratification of review V; A2: 7 in `Skeleton/DescentStepOrientable.lean`, one of which is the endpoint of `Skeleton/ClosedBranchCaseOne.lean` with 1 open leaf, so 6 + 1). The number rose because reviews G, I, J cut false or oversized leaves into honest ones — not new work; **frozen (externally reviewed OK) so far: 8 of A1's 12 (one of the other four, A1.8b, is a truth question under consult), 7 of A2's 7** (every open A2 leaf is frozen), **B: 2 + 6 + 5 + 1 = 14** (B1.d, B1.e; the 6 `sorry` leaves of `Skeleton/ControlledGraphNeighborhood.lean`; the 5 of `Skeleton/Section34Terminal.lean`; B1.b.1 inside its composite leaf until the next skeleton cuts it; B1.a closed, B1.b.3–4 proved as exporters 2026-09-21), **C: 1**. Foundations proved on 2026-09-21 that unblock B-side leaves without closing one: the `IsPLCellOn` API. Leaves closed since this page was created: 5 (B1.a, its UNTESTED flag cleared 2026-09-21; A2.3.a; A2.4b; A2.4c ×2 — the last four are frozen skeleton leaves proved on 2026-09-21).
