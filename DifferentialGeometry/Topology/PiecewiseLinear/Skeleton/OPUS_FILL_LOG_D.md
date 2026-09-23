# Opus fill log, lease d (token `claude-agent-d-20260919`), 2026-09-22

The coordinator stopped the lane before the first compile (lease d was in use by the Gemini
batch). No Lean module, `.wip` file or scratch probe was created. There were 0 compiles, so
nothing was verified and there is no axiom audit. Every leaf is STUCK at "design only". The
routes below come from reading `Skeleton/Section32PseudoCell.lean`, `PseudoCell.lean` and the
digests AK/AM/AD. None of them has been checked in Lean.

## exists_compact_connected_to_freeFace — STUCK (not started in Lean)
- File: none. Import line: none. New public names: none. Compiles: 0.
- Route: `Bv := h '' (f '' [q, s])`, where `f` is the `IsPLBall 3` model of `C v`,
  `q = f⁻¹ v` and `s = f⁻¹ p` for a point `p` of the free face `F_v` (non-empty by
  `freeFaceConnected`). `F_v ∩ D e = ∅` follows from `splitProper`. The half-open segment
  maps into `interior (C v)`, and `D e ∩ interior (C v) = ∅`.
- Needed: `f` (relative interior) = `interior (C v)` by invariance of domain, and "a splitting
  disk has empty interior in ℝ³" (or `D e ⊆ frontier (C v)`). Neither was searched for yet.

## exists_twoComponents_of_pseudoCell — STUCK (not started in Lean)
- File: none. Compiles: 0.
- Route: `U_i := connectedComponentIn ((h''C u ∪ h''C v) \ Ec) (h u / h v)`. "All or none" on
  `Eint \ {P'}` uses `hcell` and needs `DQ ⊆ closure (Q₁ \ DQ)`. A third component is excluded
  because `Y \ (Ebd ∪ {P'})` is connected. It lies between the connected `interior (C·)` and
  its closure.
- Two gaps were found that the frozen hypotheses do not obviously close:
  - (a) Disjointness of `U₁` and `U₂` needs the separation `hsep` inside
    `I = interior Y` to extend to frontier points of `Y`. That needs `Y` to be locally
    collared at `frontier Y \ Ec`, a model-side property of `C u ∪ C v`.
  - (b) Clause (6) at the rim circles `h '' Dbd f`, `f ∋ u`, needs
    `Dbd f ⊆ closure F_u`. The proof reduces to "a PL disk does not locally separate ℝ³ at
    its boundary points".
- Neither gap is a counterexample. Both are genuine regularity lemmas.

## exists_edgeCollarFamily — STUCK (not started in Lean)
- File: none. Compiles: 0.
- Route: build `W e := h '' (radial collar in the `f_u` model ∪ radial collar in the `f_v`
  model)` over `f⁻¹ (D e)`. The collar thickness is a continuous function tapering to 0 at
  `f⁻¹ (midpoint)`, bounded by the distance to `f⁻¹ K`, to the other disks, and to the `V`
  margins.
- `C v \ W e` is star-shaped in the model, so it is connected.
- Needed: uniqueness of the radial representation in the standard simplex (relative
  interior, not ambient), `∂C = f (∂Δ)`, and invariance of domain to transport interiors and
  frontiers through `h`.

## isHandleDecomposition_of_edgeCollars — STUCK (not started in Lean)
- File: none. Compiles: 0.
- Route: partition `G = N' \ ⋃ Ec` into `P_w` by owner (the side of `W e`, else the unique
  cell). Each `P_w` is clopen in `G`. (7), (10a) and (10b) then follow set-theoretically,
  with `closure U₁ ∩ closure U₂ ⊆ Ec e` because components are closed.
- Remaining gap: `P_w ⊆ closure (connectedComponentIn G (h w))`. This reduces to
  `h''C w \ ⋃_{e ∋ w} W e` being connected. The reduction from `Q_w ∪ R_e` is a clopen
  argument, done on paper.
- `IsEdgeCollarFamily` gives connectivity only per single edge. Deriving it for the union
  needs unicoherence of the ball `h''C w`. That means `separates_or_separates_of_union`
  (`Connected/PhragmenBrouwer.lean`, `[SimplyConnectedSpace X] [LocallyConnectedSpace X]`)
  applied to the subspace `h''C w`.
- Not refuted: a circle-type counterexample needs a non-unicoherent `h''C w`, and the tube's
  cells are balls.

# Batch 2 (lease d)

Worker: Claude (lease d, token `claude-agent-d-20260919`), 2026-09-22, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`.

## isEmbedding_derivedNeighborhoodRay — CLOSED
## range_derivedNeighborhoodRay — CLOSED

- File (both leaves): `DifferentialGeometry/Topology/PiecewiseLinear/DerivedNeighborhoodRayInterior.lean`
  (43 lines, SHA-256 `bc4a8618fc18df4661d416c784adcb930aa1477ba6296f42bbe2e331ca8e1e50`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayInterior`
  (the module imports only `DerivedNeighborhoodRayEmbedding`).
- New public names: the two leaves only (grepped tree-wide; the only other occurrences are the
  skeleton's `sorry` copies). Statements byte-identical to
  `Skeleton/DerivedNeighborhoodComplement.lean:66-79` (checked by script, text up to `:=`), with
  the same `local notation "E3"` and the same `private noncomputable local instance
  euclideanDecidableEq`; the instance in the `range` statement is definitionally the classical
  one of `range_derivedNeighborhoodRay_of_subset_interior`, `exact`-term accepted.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedNeighborhoodRayInterior.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 15:41 local, -07:00).
- Axiom audit: `AuditOpusD1.lean` (lease d output root, `-Audit`) — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\AuditOpusD1.lean with no diagnostics;
  shared outputs unchanged.` (15:42): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: each leaf is `…_of_subset_interior A K hKA` (lease b,
  `DerivedNeighborhoodRayEmbedding.lean`) applied to
  `derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA hKint`.
  Every frozen hypothesis is used (`hA` only for `N ⊆ interior |A|`); no gap.
- Lead option: the skeleton could instead call the two lease-b theorems directly; the leaves
  are kept because their statements are frozen.
- Compiles: 1 module check (≈11 s) + 1 audit (≈46 s).

## exists_bicollar_complement_with_boundary_collars — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/BicollarComplementCollars.lean`
  (594 lines, SHA-256 `b7507266916a78a85ad02af61f2c08cc2595586529723f43ad0f915d6b39a076`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.BicollarComplementCollars`
- New public names (grepped tree-wide, unused before): `IsPLHomeomorphOn.image_mem_nhdsWithin`
  (a PL homeomorphism carries relative neighbourhoods to relative neighbourhoods),
  `exists_rescaled_bicollar_of_mem_nhdsSetWithin` (rescale a bicollar so that
  `ρ (L × (-1, 1))` is relatively open in `K`), `image_inter_closure_sdiff_of_rescaled_bicollar`
  (then `W ∩ cl (K - W) = ρ (L × {±1})`), `isCombinatorialManifoldWithBoundary_of_space_eq_image_prod`
  (any triangulation of a PL image of `L × [a, b]`, `L` a combinatorial surface, is a
  combinatorial 3-manifold with boundary), `exists_half_collar_of_eq_image_connectedComponentIn`
  (the half collar and component retraction of an end copy `ρ (Lα × {e})`), and the leaf itself
  (statement and `variable` line byte-identical to `Skeleton/ExtendedLoopTheoremOrientable.lean`,
  checked by script).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\BicollarComplementCollars.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 16:06 local, -07:00).
- Axiom audit: `AuditOpusD2.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\AuditOpusD2.lean with no diagnostics;
  shared outputs unchanged.` (16:07): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: `IsCombinatorialManifoldWithBoundary.exists_bicollar` (`Bicollar.lean`, already
  componentwise) gives `ρ₀ : L × [-1, 1] ≅ W₀`, `W₀ ∈ 𝓝ˢ[K] L`. With `O ∩ K ⊆ W₀` and the
  tube lemma, `ρ (y, t) = ρ₀ (y, ε t)` for small `ε` has `G ∩ K = ρ (L × (-1, 1))` (`G` open, via
  continuity of `ρ₀⁻¹` on `W₀`); so no invariance of domain is needed. `W = ρ (L × [-1, 1])` is
  triangulated as `restrict K' W` in a subdivision `K'`; it is a combinatorial manifold by
  `isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods` (closed-star disk × interval,
  `isPLBall_three_prod`). `R = subcomplexGeneratedBy K' A.facesᶜ` is a manifold by
  `IsCombinatorialManifoldWithBoundary.complement` (the trace on `Bd K` is empty);
  `boundaryComplex_space_of_closure_sdiff` and
  `inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary` give `Bd K ⊆ Bd R` and
  `ρ (L × {±1}) = Bd A ⊆ Bd R`. A component `B ⊆ W` of `Bd R` is `ρ (Lα × {e})`: first
  coordinates of `ρ⁻¹ (B)` stay in one component of `L`, second coordinates are an order-connected
  subset of `{-1, 1}`. `σ (y, s) = ρ (π y, e - e s)`; the retraction is `x ↦ ρ (x, e)` on the
  clopen component `Lα` and constant elsewhere (`Continuous.if`, empty frontier).
- Gemini G053 blocker claim ("missing bicollar neighborhood theorem") was FALSE:
  `IsCombinatorialManifoldWithBoundary.exists_bicollar` exists; the missing parts were the
  rescaling, the manifold property of the complement and the component bookkeeping.
- Compiles: 2 module checks (≈14 s each) + 1 audit (≈47 s).

## exists_nontrivial_boundary_loop_of_bicollar_complement — STUCK (statement believed TRUE)

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExtendedLoopKernelTransfer.lean.wip`
  (462 lines, SHA-256 `044377cac8539c06d4298903cc9a0f03fc41e10dfd22ab0f124c9dfe12c8a3c4`). It does
  NOT contain the leaf; it holds the verified toolkit below. Before the rename, this exact content
  passed as module `DifferentialGeometry.Topology.PiecewiseLinear.ExtendedLoopKernelTransfer`:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExtendedLoopKernelTransfer.lean with no diagnostics; shared outputs unchanged.`
  (≈16:32), and `AuditOpusD3.lean` passed (16:34; foundational axioms only, thirteen linters).
  Renaming it back to `.lean` gives a registrable module (imports `BicollarComplementCollars`).
- Toolkit (new names, grepped unused; hypotheses are exactly the leaf's own `hK hL hR hρ hW
  hRspace`, so the digest's "derived boundary interface" obligation is DONE for the GIVEN collar,
  not a rescaled one):
  `isCombinatorialManifoldWithBoundary_of_space_eq_prod_Icc`, `boundaryComplex_space_of_space_eq_prod_Icc`
  (any triangulation of `L × [a,b]` has boundary `L × {a,b}`; via `boundaryComplex_space_prism`
  on closed-star disks), `IsPLHomeomorphOn.mem_nhdsWithin_of_mem_prod_Ioo` (PL invariance of
  domain: `W ∈ 𝓝[|K|] ρ z` for `z ∈ L × (-1,1)`, via
  `image_mem_nhdsWithin_of_notMem_boundaryComplex`),
  `IsPLHomeomorphOn.inter_closure_sdiff_eq_image_prod_pair` (`W ∩ cl (K - W) = ρ (L × {±1})`),
  `boundaryComplex_space_of_closure_sdiff_bicollar` (`Bd R = Bd K ∪ ρ (L × {±1})`),
  `exists_connectedComponentComplex_boundaryComplex_eq_image_of_bicollar` (each `ρ (Lα × {e})` is a
  whole component of `Bd R`), `IsPLHomeomorphOn.exists_isOpen_inter_eq_image_prod_Ioo` (the bands
  `ρ (L × (-s, s))` are open in `|K|`), `IsPLHomeomorphOn.exists_continuousOn_push_to_ends` (a map
  `Φ : |K| → |K|`, identity off `W`, `ρ (y,t) ↦ ρ (y, clamp (t/s))`; sends `ρ (L × {±s})` to the
  ends, `|K| - ρ (L × (-s,s))` into `R`, the band into `W`, fixes `L`),
  `IsPLHomeomorphOn.exists_continuousOn_retraction_image_connectedComponentIn` (`W → ρ (Lα × {e})`).
- Remaining obligation (the innermost-circle core of 26.4), in the contrapositive form that the
  toolkit makes uniform: assume every free loop of every end component that is nullhomotopic in
  `R` is nullhomotopic in the end component; show the original loop is nullhomotopic in `L`.
  (a) PL singular disk: `exists_isPiecewiseAffineOn_fill_of_nullhomotopic` (`LoopTheorem/MoiseChainPL`)
  with `L` as a subcomplex of a subdivision of `K`, plus the `g`/free-loop conversion
  (`conjugacyClassMeets_bot_iff_nullhomotopic`, `pathToCircle_nullhomotopic_iff`).
  (b) Transversality: for `φ = (ρ⁻¹ ∘ f).2` (PL on `P ∩ f⁻¹ W`, a polyhedron by
  `isPolyhedron_inter_preimage_of_isPolyhedron`), a level `±s` avoiding vertex values has
  `f⁻¹ ρ (L × {±s})` = a finite disjoint family of PL circles in `int P`. NOT in the tree: needs the
  local arc structure at edge points (two cofaces of an interior edge), then
  `exists_finite_isPLSphere_or_isPLBall_decomposition` and exclusion of arc components.
  (c) Planar innermost argument: nested Jordan disks (`isPLBall_closure_inside_of_isPLSphere_one`),
  induction on nesting depth, connectedness of "disk minus disjoint subdisks" (NOT in the tree
  outside the active `PlanarJordan/` lane), pasting extensions over child disks into the end
  components, `Φ` for the sides, the retraction for the W-side case, and the root case (all
  circles inessential ⇒ nullhomotopy in `W` ⇒ in `L`, the digest's zero-intersection exclusion).
  Estimate for (a)–(c) plus assembly: 1300–1600 lines. Gemini G054's claim ("missing loop
  lifting") is not the real gap; the gap is (b) + (c).
- Compiles for this leaf: 3 module checks of the toolkit (≈14–24 s) + 2 audits (≈48 s).

## exists_product_coordinates_for_disjoint_essential_polygons — STUCK (statement believed TRUE)

- File: none (no `.wip`; no Lean written for this leaf). Compiles: 0.
- Route checked against the tree: `IsCombinatorialSolidTorus.isPLTorus_frontier` (lease c) makes
  `∂S` a PL torus; `IsPLTorus.exists_combinatorial_triangulation`, `isOrientable_euclidean_three`,
  `IsPLTorus.bettiOne_le_two` give an orientable triangulation with `χ ≥ 0` (`χ = 0` still needs
  `β₁ ≠ 0`, e.g. via the essential circle). NEW since my first grep: the untracked, in-flux files
  `SeparatingPolygonDisk.lean` / `OrientableSurfaceEulerParity.lean` (created 16:31–16:33 by another
  lane, not accepted, not imported by me) prove Moise 28.9
  (`IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff`, whose conclusion is
  literally the negation of `hess i`), so every `G i` is nonseparating. Then
  `IsCombinatorialManifold.exists_connected_annulus_complement` (bicollar of `G 0` inside
  `T - ⋃_{i≠0} G i`) and `exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero` make the complement
  an annulus containing the other circles.
- Missing (not in the tree): (i) in an annulus, each further `G i` separates it into two annuli
  (Euler/parity count with `odd_eulerChar_of_isOrientable`, capping, `hess` excludes the disk
  piece), iterated into a cyclic chain of annuli ordered along the core; (ii) gluing the
  annulus product charts along the chain into ONE PL chart `J × Q → ∂S` with `Q` a PL circle in
  `E3`: matching end parametrizations and killing the monodromy PL-ly (the existing torus
  recognition `exists_homeomorph_prod_circle_of_eq_ends` is only topological). Estimate ≥ 1500
  lines. Gemini G024's claim is right about the missing simultaneous straightening, wrong about
  "classification of surfaces" (the Euler-parity route above avoids it).

# Batch 3 (lease d)

Worker: Claude (lease d, token `claude-agent-d-20260919`), 2026-09-22, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`.

## exists_nontrivial_boundary_loop_of_bicollar_complement — CLOSED

- Files (three new real modules, no `.wip`, nothing else edited):
  - (c) `DifferentialGeometry/Topology/PiecewiseLinear/JordanDiskPasting.lean` (464 lines,
    SHA-256 `72a690483a04d39ae810ebfc9621dfabf424be88c7f8cd44e07e700e6f29a0d6`);
  - (b) `DifferentialGeometry/Topology/PiecewiseLinear/PLLevelCircles.lean` (747 lines,
    SHA-256 `dcb0edba64ed05d42f921c167f588c23528e481923a04814821ca4370f0b11d3`);
  - leaf `DifferentialGeometry/Topology/PiecewiseLinear/BicollarBoundaryLoop.lean` (591 lines,
    SHA-256 `570e139942aa770dcf4b9ac7781dbac5bb0f27ba32b841a05fc35e7bb4ad4e13`).
- Import lines to register (the leaf module imports the other two and `BicollarBands`):
  `import DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting`
  `import DifferentialGeometry.Topology.PiecewiseLinear.PLLevelCircles`
  `import DifferentialGeometry.Topology.PiecewiseLinear.BicollarBoundaryLoop`
  All imports are tracked modules except these three; nothing under `PlanarJordan/` that is
  untracked is imported (`AmbientExtension`, `CompactRegion`, `Transport` are tracked).
- New public names (all grepped tree-wide first, previously unused):
  - `JordanDiskPasting`: `exists_homeomorph_image_closure_inside_eq_closedBall`,
    `isConnected_setOf_one_lt_norm_lt`, `exists_isOpen_isConnected_sdiff_closure_inside`
    (arbitrarily thin connected outer collars of a Jordan disk),
    `exists_continuousOn_mapsTo_closure_inside_of_nullhomotopic`,
    `IsPLBall.nullhomotopic_of_continuousOn`, `closure_inside_subset_interior_of_subset_interior`,
    `exists_continuousOn_mapsTo_of_jordan_disk_pasting` (the innermost-circle induction).
  - `PLLevelCircles`: `exists_ne_zero_linearMap_apply_eq_zero_of_finrank_eq_two`,
    `exists_eq_smul_of_linearMap_apply_eq_zero_of_finrank_eq_two`, `affineMap_apply_eq_add_linear`,
    `exists_affineMap_linear_ne_zero_apply_eq_zero_of_finrank_eq_two`,
    `exists_linearMap_apply_eq_zero_pos_of_apply_ne_zero`,
    `exists_ball_subset_forall_mem_convexHull_of_mem_openSimplex`,
    `card_le_three_of_mem_faces_of_finrank_eq_two`,
    `exists_arc_of_mem_level_of_ball_subset_convexHull`,
    `exists_coface_pos_of_ball_subset`, `exists_cofaces_cover_of_ball_subset`,
    `exists_arc_of_two_rays`, `exists_eq_add_smul_of_mem_level_of_nonneg`,
    `exists_arc_of_mem_level_of_edge`, `exists_arc_of_mem_level_of_affineOn_faces`,
    `isCombinatorialManifold_one_of_forall_arc`,
    `IsPiecewiseAffineOn.exists_finite_levels_isPLSphere_decomposition` (transversality: all but
    finitely many levels of a PL function on a planar polyhedron, if interior, are finite
    disjoint unions of PL circles).
  - `BicollarBoundaryLoop`: `exists_continuousOn_mapsTo_closure_inside_of_forall_isNullHomotopic`,
    `IsPLHomeomorphOn.exists_mem_connectedComponentIn_of_isPreconnected`,
    `IsPLHomeomorphOn.exists_finite_isPLSphere_levels_of_bicollar`,
    `IsPLHomeomorphOn.exists_continuousOn_push_to_ends_mapsTo`,
    `IsPLHomeomorphOn.exists_isOpen_pair_of_bicollar_levels`,
    `IsPLHomeomorphOn.exists_continuousOn_mapsTo_space_of_bicollar_disk`, and the leaf (statement,
    `open Set Topology`, namespace and `variable` line byte-identical with
    `Skeleton/ExtendedLoopTheoremOrientable.lean:71-94`, checked by script).
- Checker (each exactly `Verified … with no diagnostics; shared outputs unchanged.`):
  `JordanDiskPasting.lean` 16:56, `PLLevelCircles.lean` 17:14, `BicollarBoundaryLoop.lean` 17:40
  (local, -07:00; the JSON records `diagnosticLines 0` for the SHAs above).
- Axiom audit: `AuditOpusD4.lean` (all three modules, `-Audit`) — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\AuditOpusD4.lean with no diagnostics;
  shared outputs unchanged.` (17:42): every declaration of the three modules has closure within
  `propext`, `Classical.choice`, `Quot.sound`; the thirteen environment linters pass.
- Route (Moise 26.4, prove-first). By contradiction, every loop in a component of `Bd R` inside
  `W` that dies in `R` dies in the component. The kernel element gives a non-nullhomotopic free
  loop of `L` nullhomotopic in `K`; `exists_isPiecewiseAffineOn_fill_of_nullhomotopic` (with `L`
  a subcomplex of a subdivision of `K`) gives a PL disk map `f : P → K`, `f (Bd P) ⊆ L`.
  `φ = (ρ⁻¹ ∘ f).2` is PL on the polyhedron `P ∩ f⁻¹ W`; a level `s ∈ (0, 1)` with `±s` generic
  gives disjoint PL circles `C±` in `Int P` (interiority from `G₁ ∩ K = ρ (L × (-1, 1))` and
  `f (Bd P) ⊆ L = ρ (L × {0})`). After the push `Φ` of `BicollarBands`, `U = f⁻¹ ρ (L × (-s, s))`
  goes into `W`, `V = f⁻¹ (K - ρ (L × [-s, s]))` into `R`, and each circle into an end copy
  `ρ (Lα × {±1})`, which is a component of `Bd R`. The pasting theorem absorbs innermost disks:
  on the `W` side by the end retraction, on the `R` side by the contradiction hypothesis and the
  Jordan-disk extension of a nullhomotopic map. The result `G : P → W` agrees with `f` on `Bd P`
  (`Φ` fixes `L`), so `(ρ⁻¹ ∘ G).1` extends `f | Bd P` into `L` and the loop dies in `L`.
  The digest's zero-intersection case is exactly this final projection.
- Duplication report: the Jordan–Schönflies disk transport in `JordanDiskPasting`
  (`exists_homeomorph_image_closure_inside_eq_closedBall`) re-proves locally the pattern of the
  untracked `PlanarJordan/ConsecutiveCellUnion.lean` (`nonempty_homeomorph_closure_inside`), from
  tracked `PlanarJordan` files only. "PL disk minus disjoint interior subdisks is connected" was
  not needed: the induction uses connected thin outer collars instead.
- Compiles for this leaf: `JordanDiskPasting` ≈3 checks, `PLLevelCircles` ≈4 checks,
  `BicollarBoundaryLoop` 2 checks (≈14 s each), 1 audit (≈53 s).

## exists_product_coordinates_for_disjoint_essential_polygons — NOT STARTED (deferred)

- No file, no compile. Returned after the leaf above so that it can be accepted first; the
  worker can be resumed on this leaf.
- Route with the accepted 28.9 modules: `IsCombinatorialSolidTorus.isPLTorus_frontier` and
  `IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff` make every `G i`
  nonseparating (its conclusion negates `hess i`);
  `IsCombinatorialManifold.exists_connected_annulus_complement` and
  `exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero` chart the torus cut along `G 0` by
  `∂Δ² × [0, 1]`. The other circles pull back into the open lateral annulus and are essential
  there (a lateral disk maps to a disk in `frontier S`);
  `IsPLSphere.exists_disk_or_annulus_of_subset_prism_lateral` (`NonseparatingPolygonCarrier`)
  then gives the sub-annulus below each circle, and the flipped
  application the one above.
- Still missing in the tree: the induction on `n` ordering the circles by height; matching the end
  parametrizations of consecutive annuli (orientation-preserving by orientability, then the
  circle pseudo-isotopies of `CircleAnnulusIsotopy` in a collar); killing the monodromy when the
  chain closes up at `G 0` (only the interval-fiber version
  `IsCylindricalDiagram.exists_endMap_id_of_isOrientable_interval` exists); `J := G 0` and `Q` a
  triangle in `E3` with `n` marked points. Estimate 1500–2500 lines.

# Batch 4 (Section 28 product coordinates)

Worker: Claude (lease d, token `claude-agent-d-20260919`), 2026-09-22, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`. Target:
`exists_product_coordinates_for_disjoint_essential_polygons` (`Skeleton/Section28Annuli.lean`).
Planned bricks: (1) the two sides of an essential circle in the prism lateral annulus;
(2) slab gluing and simultaneous straightening of finitely many essential circles to levels;
(3) the leaf (torus cut along `G 0`, cylindrical diagram, twist removal in a top slab by
`isPLCirclePositive_of_isOrientable_cylindricalDiagram`, product chart in `E3`).

## Brick 1 `PrismLateralCircleSides` — VERIFIED, AUDITED

- `DifferentialGeometry/Topology/PiecewiseLinear/PrismLateralCircleSides.lean` (308 lines), import
  `NonseparatingPolygonCarrier`. Checker 18:00 local: `Verified ... with no diagnostics; shared
  outputs unchanged.`
- `isPLSphere_stdSimplex_prism_boundary` (public re-proof of the private
  `isPLSphere_prism_frontier` of `NonseparatingPolygonCarrier`, 25 lines; duplication reported),
  `exists_isPLHomeomorphOn_lateral_side_of_disk_decomposition`,
  `IsPLSphere.exists_lateral_sides_of_subset_prism_lateral`: an essential PL circle in
  `∂Δ² × (0, 1)` splits `A = ∂Δ² × [0, 1]` into two PL annulus charts meeting exactly in `K`,
  one fixing the bottom and one fixing the top pointwise.

## Brick 2 `LateralAnnulusLevels` — VERIFIED, AUDITED

- `DifferentialGeometry/Topology/PiecewiseLinear/LateralAnnulusLevels.lean` (522 lines), import
  `PrismLateralCircleSides`. Checker 18:14 local: `Verified ... with no diagnostics; shared
  outputs unchanged.`
- `isPLHomeomorphOn_mul_add_Icc`, `eqOn_piecewise_of_eqOn_inter`,
  `exists_Ioo_subset_of_isPreconnected_of_finite`, `IsPLHomeomorphOn.exists_eqOn_eqOn_union`
  (piecewise gluing without exposing the classical decidability instance of
  `IsPLHomeomorphOn.piecewise`), `IsPolyhedron.exists_isPLHomeomorphOn_prod_Icc_of_slab`
  (squeeze a PL homeomorphism of `P × [0, 1]` into a slab),
  `IsPLSphere.exists_isPLHomeomorphOn_prism_lateral_level`,
  `exists_isPLHomeomorphOn_prism_lateral_levels_insert`,
  `exists_isPLHomeomorphOn_prism_lateral_levels` (finitely many disjoint essential circles are
  distinct levels of one PL homeomorphism of `A` preserving both boundary circles).
- Pitfall: `IsPLHomeomorphOn.piecewise` fixes `Classical.propDecidable`; a written
  `(P ×ˢ Icc a b).piecewise f g` elaborates with `decidableMemProd` and does not match. Use the
  existential wrapper.

## exists_product_coordinates_for_disjoint_essential_polygons — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/EssentialPolygonProductCoordinates.lean`
  (481 lines, SHA-256 `ed5dc0057fc6409662a4e3e0fb407d552d9d5e00341aadbc7aa47a13cb7ef02b`).
  Brick SHAs: `PrismLateralCircleSides`
  `7e803541ac5f8f4478f9817038ab8f8336b014574ecafe23c32bb429f049882e`, `LateralAnnulusLevels`
  `f4177c940080e4c7f2a22d9042d3009a61fe57ec0d1a65f49c95b0b526d1b988`.
- Import lines to register (the leaf module imports the two bricks):
  `import DifferentialGeometry.Topology.PiecewiseLinear.PrismLateralCircleSides`
  `import DifferentialGeometry.Topology.PiecewiseLinear.LateralAnnulusLevels`
  `import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates`
  Other imports are tracked: `CarriesGeneratorOrIsPLCellOfDisjointCarrier`,
  `CirclePrismComparison`, `CylinderEndMap`, `MobiusEmbedding`, `MoiseChain`.
- New public names (grepped first, unused): `isPLHomeomorphOn_mul_add_Icc_of_neg`,
  `exists_isCylindricalDiagram_eqOn_eqOn` (instance-safe wrapper of
  `isCylindricalDiagram_piecewise`), `IsCylindricalDiagram.exists_prod_chart_of_eq_ends` (an
  untwisted diagram over `∂Δ²` is a PL product chart `J × Q` in `E3`, levels to fibres),
  `IsCylindricalDiagram.exists_eq_ends_of_isOrientable` (twist removal in a top slab `[c, 1]`,
  levels in `[0, c]` untouched), `IsPLHomeomorphOn.exists_prism_levels_of_essential` (annulus
  chart with finitely many essential circles as levels),
  `exists_isCylindricalDiagram_of_annulus_bicollar` (annulus chart plus bicollar), and the leaf.
  Statement, `open Set Topology`, namespace and `local notation "E3"` byte-identical with
  `Skeleton/Section28Annuli.lean:80-90` (checked by script).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\EssentialPolygonProductCoordinates.lean with no diagnostics; shared outputs unchanged.`
  (18:26 local, -07:00).
- Axiom audit: `AuditOpusD5.lean` (all three Batch 4 modules) — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\AuditOpusD5.lean with no diagnostics;
  shared outputs unchanged.` (18:28): closure within `propext`, `Classical.choice`, `Quot.sound`;
  the thirteen environment linters pass.
- Route. `Bd S` is a PL torus; its orientable triangulation `L` has `χ ≥ 0`. 28.9
  (`IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff`) and `hess` make `G 0`
  nonseparating. `exists_connected_annulus_complement`, with the neighbourhood avoiding the
  other `G i`, gives a bicollar `W` and a connected complement `R` with two boundary circles;
  `χ(R) = 0` and `exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero` chart `R` by
  `∂Δ² × [0, 1]`. The other circles lie in the open annulus, bound no disk (a disk in `R` is one
  in `Bd S`), and brick 2 makes them levels. Annulus chart then bicollar give a cylindrical
  diagram over `∂Δ²` with `G 0` at level `3/4`. Its end map is circle-positive by
  `isPLCirclePositive_of_isOrientable_cylindricalDiagram` (no Möbius band in `Bd S`), hence
  pseudo-isotopic to the identity; the pseudo-isotopy is squeezed into `[3/4, 1]`, which removes
  the twist without moving the levels. `exists_isPLHomeomorphOn_of_eq_endMap` against the model
  `(x, t) ↦ (e x, e (stdTriangleLoop t))` gives `f : J × Q → Bd S` with `J = Q` a triangle in
  `E3`; `q i` is the loop point at the level of `G i`, injective because the `G i` are.
- The twist removal needed no new interval-fibre extension: the circle-fibre orientation theorem
  already exists (`MobiusEmbedding.isPLCirclePositive_of_isOrientable_cylindricalDiagram`); the
  new work is keeping the levels fixed (slab squeeze).
- Compiles for Batch 4: `PrismLateralCircleSides` 2, `LateralAnnulusLevels` 4,
  `EssentialPolygonProductCoordinates` 3 (≈14–70 s each), 1 audit (≈57 s).

# Batch 5 (controlled graph neighbourhood)

Worker: Claude (lease d, token `claude-agent-d-20260919`), 2026-09-22, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`. Target: the seven frozen leaves of
`Skeleton/ControlledGraphNeighborhood.lean`. Read first: the skeleton docstring, `Section34Frame`
(`Section34CutFrame`, `Section34OuterTorus`, `Section34VertexPreparation`,
`Section34PiercingConditions`), `Section34Statements`, `Section34Control`,
`Section34FaceBallVocabulary`, `ChartTameNestedCells`, `CurveCrossingGeneralPosition`,
`PLCellOnStability`, the `DualCellPiercing*` modules, `TrivalentDualCellSolidTorusNeighborhoods`,
`LocallyFiniteSplittingDisks`, `SubdivisionSubordinateToCover`, `SurfaceSplitBallPair`,
`BallCyclePair`, `InnerSolidTorusToroidalShell`.

## exists_section34CutFrame — STUCK (not started in Lean; whole statement open)

- Remaining goal: the entire conclusion. Sub-obligations and what the tree has:
  (1) the fine subdivision `𝒦'` with `𝒦'.map = 𝒦.map`, combinatorial, fine for `ψ` and the
  carriers `H`: available (`exists_isSubdivision_section34CarrierSupport_subset`).
  (2) the eight-label cut: vertex balls and splitting disks exist only as graph dual cells and
  splitting disks of finite complexes (`isPLBall_graphDualCell`, `LocallyFiniteSplittingDisks`);
  NOT in the tree: the complementary cells (`tetraBall t = cl(|t| \ N)`, face disks, patches,
  face arcs, edge arcs, marked points), their `IsPLCellOn` certificates in `M₁` (the complex
  lives in `Ea`, so each cell needs a PL transport of a 3-dimensional polyhedron of `Ea` into
  `ℝ³`), the exact boundary and intersection formulas, face nesting and local finiteness.
  (3) `IsLocallyFiniteRegularNeighborhoodOf N Γ U`: needs the increasing exhaustion by finite
  subcomplexes with combinatorial derived neighbourhoods; only the one-piece version
  `PLPiece.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood` exists.
  (4) carriers: `Q w` = a small closed thickening of `h '' C_w` meets every carrier clause by
  compactness and local finiteness (not written).
  (5) outer torus: chart from `exists_chart_iUnion_carrier_subset_source`; `Sd s` must be
  `ct s '' h '' N_s` for a solid torus `N_s ⊆ U` with the rim as core, obtained by moving the
  closed star of `s` (a PL 3-ball) into `ℝ³` and using `IsPLSphere.exists_solid_torus_neighborhood`;
  the buffer then needs `C_w ⊆ int N_s` for every rim vertex `w` (fineness of `𝒦'`); the
  no-disk clause follows from the buffer and the spine clause (a spine generates `π₁` of the
  solid torus), not written.
- Estimate: the largest leaf; (2) and (3) alone are several thousand lines.

## exists_section34VertexPreparation — STUCK (not started in Lean)

- Remaining goal: the 44 clauses of `Section34VertexPreparation`. The geometric core exists
  only for finite complexes of a vector space: `exists_piercings_with_pairwise_disjoint_nested_common_neighborhoods`
  (piercing circles, nested common annular neighbourhoods = `Tn ⊆ Sn`),
  `exists_graphDualCell_piercing_with_nested_boundary_bicollars` (annuli `A_e`, `B_e`, `B_e⁰`),
  `exists_perturbation_radius_of_pairwise_disjoint_nested_common_neighborhoods`. Missing: their
  transport through `𝒦'.map` into `M₁` for the locally finite family, the enlarged cells
  `C''_v` inside the given chart preimage, the source-side component certificates, the choice
  of the two-sided tolerances `ε` with all metric margins and the whole-overlap certificate (by
  compactness and local finiteness, after localising each lens near its own disk), and the
  stability field from `exists_dist_lt_image_interior_stable_of_isPLCellOn`.

## exists_section34PiercingPackage — STUCK (not started in Lean)

- Remaining goal: the whole conclusion. Missing: auxiliary scales `δ_w ≤ ε_w` for the tube and
  side containments, `Moise341` approximation via the proved
  `Moise341.exists_section34VertexApproximation` pattern, then a relative general-position move
  of the image annuli inside each tube making every intersection point an `HasPLCrossingAt`
  crossing in a chart (the finite-complex brick is `exists_small_homeomorph_transverse_relative`
  / `hasPLCrossingAt_of_transverse_faces`; not transported to charts of `M₂`), the decomposition
  of the crossing set into `cnt e` disjoint polyhedral circles `Pg e i`, the component
  certificates of (7) for the image, and the derived fields via `section34MarginConditions`,
  `section34OverlapConditions`, `section34MarkerConditions`.

## exists_section34ProtectedCircleRemovalStep — STUCK (not started in Lean)

- Remaining goal: the whole conclusion. Missing: the Moise page 249-250 surgery inside the
  tube `Int S'_{e₀}` (an innermost intersection circle on the image annulus, a disk swap
  supported in the tube realised by a PL self-map of `C''_w`), and the preservation of all 21
  fields of `Section34PiercingConditions`, of which only the marker and boundary equalities are
  proved (`section34Step_eqOn_marker_and_boundary`).
- Interface note: the step gives `EqOn` off the support but not that the modified points stay
  in the support (`G' w '' {x | G w x ∈ interior (Sp e₀)} ⊆ interior (Sp e₀)`). The reduction of
  the next leaf below does not need it.

## exists_section34ProtectedCircleRemoval — REDUCED to the removal step (proved from leaf 4)

- File: `DifferentialGeometry/Topology/PiecewiseLinear/Section34CircleRemovalDescent.lean`
  (524 lines, SHA-256 `3dd046c4177d216ad1c5c008095d7ef767d5fa104ddf164d0c6de9ad90883866`),
  import `Section34Frame` only. Import line:
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section34CircleRemovalDescent`
- Main theorem `exists_section34ProtectedCircleRemoval_of_step`: exactly the conclusion of the
  frozen leaf, with the frozen hypotheses `hprep hpack K hK` and one more, `hstep`, which is the
  conclusion of `exists_section34ProtectedCircleRemovalStep` for the same preparation,
  universally quantified over `G cnt Pg`. Wiring for the skeleton (not compiled here: the
  skeleton olean cannot be built in the private root because of its `sorry` warnings):
  `exists_section34ProtectedCircleRemoval_of_step (fun _ _ _ hp e₀ hlt =>
    exists_section34ProtectedCircleRemovalStep hprep hp e₀ hlt) hprep hpack K hK`.
- New public names (grepped first): `IsPLHomeomorphInto.congr_of_eqOn`,
  `Section34RemovalGood`, `Section34RemovalLe` (two abbreviations for the Zorn order),
  `section34RemovalLe_trans`, `section34PiercingConditions_congr_of_eqOn` (the piercing
  conditions only see the vertex maps on `Cc w`), `exists_section34PiercingConditions_count_le_one_of_step`
  (the skeleton's induction, re-proved from `hstep` under a new name because a module cannot
  import the skeleton), `exists_section34RemovalGood_upperBound`,
  `exists_section34RemovalGood_insert`, `exists_section34ProtectedCircleRemoval_of_step`.
- Route: Zorn (`exists_maximal_of_chains_bounded`) on partial results `(S, G', cnt', Pg')`
  satisfying the piercing conditions with `cnt' = 1` on the finished set `S`, `cnt' = cnt` off
  it and both `EqOn` clauses, ordered by `S ⊆ S'` and equality of `G' w` whenever no edge of
  `S' \ S` has its tube meeting `K w`. `K w` compact in `h '' U` and the local finiteness of
  the tubes make that set of edges finite, so along a chain each `G' w` stabilises; each of
  the 22 piercing conditions involves at most four vertex maps and one edge, and is read off one
  member of the chain. A maximal element with an unfinished edge is extended by iterating the
  step at that edge; vertices whose envelope misses the tube keep their map (image in
  `Q w ⊆ K w`), the others are patched off `Cc w` so that the order holds with equality. No
  countability of the edges is used, and the step's missing support-image property is not needed.
- Checker: `Verified ...\Section34CircleRemovalDescent.lean with no diagnostics; shared outputs
  unchanged.` (18:51 local). Audit `AuditOpusD6.lean`: `Verified ... with no diagnostics; shared
  outputs unchanged.` (axioms within `propext`, `Classical.choice`, `Quot.sound`; thirteen
  linters pass).
- Compiles: 3 module checks, 1 audit, 3 failed wiring attempts (audit and scratch module cannot
  see the skeleton olean; the scratch file was deleted).

## exists_section34DeletedBalls — CLOSED

- Files (both new; imports ≤ 100 characters):
  - `DifferentialGeometry/Topology/PiecewiseLinear/Section34CapDeletion.lean`: 527 lines,
    SHA-256 `7957c3d09e06d0a619cb526e2865197a8a86ad1236c657c3b0015bf5adcfc0f6`. Imports
    `BallInterior`, `LabelledCellAssembly`, `PieceMap`, `PLCellOnBoundary`, `SphereDisk` and
    `SurfaceSplitBallPair`.
  - `DifferentialGeometry/Topology/PiecewiseLinear/Section34DeletedBalls.lean`: 168 lines,
    SHA-256 `730fe0a38896791be6fcf1dd8dcc3b16fd7fa9471c908c4175fee1cef9c81cac`. Imports
    `Section34CapDeletion` and `Section34Frame`.
- The leaf is restated byte-identically. The skeleton lines 239–258 (`section Leaves` and the
  variable block) and 521–544 (the statement) are copied verbatim, under `open Set Topology`,
  the same namespace and `universe u`.
- Wiring: import `Section34DeletedBalls` and delete the skeleton leaf. The call at skeleton line
  647 is unchanged.
- No frozen hypothesis was dropped. The following are unused and consumed by `let _`:
  - the hypotheses `hU`, `hh`, `hN` and `hQlf`;
  - the instances `[T2Space M₁]`, `[SecondCountableTopology M₁]`, `[SecondCountableTopology M₂]`
    and `[HasGroupoid M₁ (plGroupoid 3)]`;
  - the section instance `[FiniteDimensional ℝ Ea]`.
- New public names (all grepped first):
  - `IsPLCellOn.subset_closure_interior`;
  - `IsPLHomeomorphInto.isPLSphere_invFunOn_image`, which pulls a polyhedral sphere back
    through a PL embedding of a model polyhedron;
  - `IsPLCellOn.sdiff_interior_of_frontier_inter`, the single cap;
  - `IsPLCellOn.sdiff_biUnion_interior`, the finite iteration;
  - `isPLCellOn_sdiff_iUnion_interior_of_caps`, the whole family over abstract index types.
- Route:
  - Single cap. Take cells `X`, `Y` with `Bd X ∩ Bd Y = C` a polyhedral circle, a point of
    `Bd Y` in `Int X`, and `Bd Y ⊄ X`.
    - Pull `C` back to a PL circle on the model sphere `Bd P_Y`, and split that sphere into two
      disks (`exists_disk_decomposition_of_isPLSphere_one_subset_two`).
    - Each open disk is connected and misses `Bd X`, so it lies in `Int X` or misses `X`. The
      two witness points choose the inner disk, and `Bd Y ∩ X` is that disk. This is already the
      2-cell with rim `C`.
    - Transport the disk into the model of `X` through `invFunOn uX PX ∘ uY` and split the ball
      (`IsPLBall.exists_pair_union_eq_inter_eq_of_boundary_trace`).
    - The interiors of the two halves are connected and miss `Bd Y`. Exactly one half lies in
      `Y`: if both did, `Int X ⊆ Int Y` against the inner witness; if neither did, `X` would miss
      `Int Y` near the inner witness. `X \ Int Y` is the other half.
  - Iteration. The overlaps `B_{e.1} ∩ B_w` of the incoming edges are pairwise disjoint (piercing
    clause 21), so each earlier deletion leaves the next circle, both witnesses and the
    frontier trace unchanged. Finset induction on the incoming edges, which are finite by
    `finite_splitDisk_of_section34CutFrame`.
  - Leaf data: `Dd e = Bd B_{e.1} ∩ B_{e.2}`, `DdBd e = Pg e 0`, `DvBd w = frontier (Dv w)`.
    - `Bd ∩ Bd = Pg e 0` comes from piercing clauses 7, 17 and 18 with `hone`, and from
      preparation clauses 15 and 16.
    - The witnesses come from clause 8 and a point of each boundary circle of the annulus
      `A_e`.
    - Markers come from `hcore`, `body ⊆ Kcore` and clause 22.
    - The neighbourhood: every `B_w` is covered by the deleted balls (clause 21), and `hcore`
      with `Γ ⊆ ⋃ Kcore` puts `h '' Γ` inside `⋃ Int B_w`.
- Checker: both modules `Verified ... with no diagnostics; shared outputs unchanged.` Audit
  `AuditOpusD7.lean` (both modules): `Verified ... with no diagnostics; shared outputs
  unchanged.` Axioms are within `propext`, `Classical.choice` and `Quot.sound`; all thirteen
  linters pass.
- Compiles: 4 module checks (2 failures: one `image_id'` argument and a `mem_toFinset`
  elaboration) and 1 audit.

## exists_section34EdgeMatching — STUCK (not started in Lean; whole statement open)

- Remaining goal: the entire conclusion (`G'` with clauses (a)–(f) below).
- Needed for (a)–(d), the PL homeomorphisms `G' w : C_w = src (.vertexBall w) → Dv w` that agree
  on the splitting disks:
  1. Disk maps `φ_e : src (.splitDisk e) → Dd e` sending rim to rim. Cheap: both are PL
     2-cells (cut frame and `hDd`), so compose the parametrisations.
  2. Sphere maps `Bd C_w → Bd Dv w` extending the `φ_e` of the incident edges. The complement of
     the disks is a `k`-holed sphere on both sides (`hDdBd`, `hDddisj`, and the cut frame's
     boundary formulas). NOT in the tree: a PL homeomorphism of `k`-holed spheres with
     prescribed boundary maps. That extension exists only when the prescribed maps are
     orientation-compatible, and the tree has no PL orientation of disks and spheres.
  3. Ball extension: `exists_isPLHomeomorphOn_extension_marked` (Alexander trick in the model),
     transported through the `IsPLCellOn` charts of `C_w` in `M₁` and of `Dv w` in `M₂`.
  4. The matching clauses then follow from the cut frame's formula `C_w ∩ C_w' = splitDisk`
     together with `hDmeet` and `hDadj`.
- Mathematical obstruction to step 2. Around a cycle of the graph the orientation choices must
  close up, so the chain of the `C_w` along a cycle and the chain of the `Dv w` must have the same
  orientation character. This does not come from the local data: when `U` is non-orientable a
  cycle can have a solid Klein bottle neighbourhood. It has to come from `h` (a topological
  embedding), or from the `ε`-closeness of the `G w` to `h` (a map close to the identity on a ball
  has local degree `1`). The `LocalDegree/` and `Homology/Local/` modules are the likely inputs,
  but no bridge to PL disk orientations exists. This is the main missing foundation.
- Needed for (e) and (f), the face tori. (e) looks cheap: `hDnbhd`, `hDvQ` and `hQsep` with the
  local finiteness `hQlf`, plus the arc-index bookkeeping of `section34FaceTorus`. (f) needs:
  - a cyclic chain of PL balls in the chart `ct s`, consecutive ones meeting in one disk and the
    rest disjoint, to be an `IsCombinatorialSolidTorus` (`BallCyclePair` gives the ball-pair
    cover; `isCombinatorialSolidTorus_of_hasCylindricalDiagram` would need a cylindrical
    diagram);
  - an inner solid torus `S₁` with the toroidal shell
    (`IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior`);
  - the spine clause for `ct s '' h '' rim`;
  - the transport `Φ` of the face torus by `ct s`.
- Estimate: several thousand lines. Steps 2 and (f) are each a project-scale brick.

# Batch 6 (PL smoothing, compact case)

Worker: Claude (lease d, token `claude-agent-d-20260919`), 2026-09-22, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`. Target: the six frozen leaves of
`Skeleton/PLSmoothingCompact.lean`. Read first:
- the skeleton docstring and the assembly `isSmoothHandleStage_step`;
- the template `IsSmoothHandleStageAdjunctionZero.lean` (a disjoint union, no gluing);
- `Handle/SmoothStage.lean`, `Handle/Gluing.lean` (only pull-back along a homeomorphism);
- `Manifold/OpenCoverAtlas.lean` (a boundaryless atlas from open patches);
- `Double/*` (the smooth double along the whole boundary);
- `Manifold/Boundary/DefiningCollar.lean` (defining function with a smooth closed collar);
- `Manifold/Attachment/Radial*` (the model cap `Cap ∪ S² × [0, B) ≅` open ball);
- `Collar/Attachment.lean` (an outer collar is absorbed);
- `Homeomorph/CircleIsotopy.lean`, `Attachment/CellExtension.lean`, `Homeomorph/JordanDiskMove.lean`
  and `Manifold/SurfaceChartSmoothing.lean`.

The tree has no general smooth gluing of two manifolds along open subsets or boundary components
for the half-space model. Every attachment leaf needs one (a capping chart, or corners rounded
along the attaching region); `Handle/Gluing.adjunctionChartedSpace` only pulls a structure back
along a homeomorphism the caller already has.

## exists_homeomorph_smooth_disks_of_isClosedEmbedding — STUCK (not started in Lean)

- Remaining goal: the entire conclusion.
- Sub-obligations:
  1. Tameness in a surface: each of the two embedded closed disks `ψ (Δ² × {j})` in the closed
     surface `∂M` lies inside a coordinate disk, i.e. an open set of `∂M` homeomorphic to the
     plane. This needs Schoenflies for a circle in a surface. Only planar Schoenflies is in the
     tree (`External/Schoenflies`, `Homeomorph/JordanDiskMove.exists_image_closed_region_eqOn_compl`).
  2. A compactly supported ambient homeomorphism of `∂M`, isotopic to the identity, moving
     both disks at once onto round disks of two disjoint smooth charts `f j : ℝ² → ∂M`. The
     planar moves exist; the surface chart smoothing is
     `exists_isotopy_smoothing_surface_chart`; the simultaneous, disjoint version is not
     written.
  3. Extension of that isotopy through a boundary collar to `θ : M ≃ₜ M` with
     `θ '' ∂M = ∂M` (the collar is `exists_boundary_collar_homeomorph`; the extension
     `θ (c (b, s)) = c (J_{1 - s/δ} b, s)` is not written).
  4. `f j` as a smooth embedding into `M` (`𝓡 2 → 𝓡∂ 3`) with range in `∂M`. This needs
     composition with the boundary inclusion of `BoundaryManifold`, whose charts are in
     `Manifold/Boundary/SmoothMap.lean`.

## isSmoothHandleStage_adjunction_one — STUCK (not started in Lean)

- Remaining goal: the entire conclusion.
- Finding (orientation alignment). The hypotheses fix only `range ψ = ⋃ j, f j '' closedBall`.
  A homeomorphism of `Δ² × [0,1]` that restricts to prescribed homeomorphisms
  `φ_j = f_j⁻¹ ∘ ψ(·, j)` on the two ends exists only when `φ₀` and `φ₁` have the same
  orientation character: the boundary sphere map restricts on the two ends with opposite
  induced orientations. So the proof must first replace `f 1` by `f 1 ∘ reflection` when the
  characters differ; the leaf stays true because the reflected chart has the same image.
  - The tree has the dichotomy for circle homeomorphisms (`HasIncreasingCircleLift`) and the
    cylinder extension `exists_homeomorph_cylinder_of_same_orientation`.
  - Missing: transferring a disk homeomorphism's character to its boundary circle, plus the
    radial extension over `Δ² × [0,1]` (via the sphere `∂(Δ² × [0,1])` and
    `closedCellHomeomorphExtension`).
- Main missing brick: a smooth compact 3-manifold homeomorphic to `M ∪_{f₀ ⊔ f₁} D² × [0,1]`.
  This needs smooth gluing along the two boundary disks with corners rounded (see the note
  above). There are corner-rounding bricks (`CornerRounding`, `CollaredCornerSmoothing`,
  `FramedCornerSmoothing`), but no gluing.
- The boundary formula of the stage then follows from boundary points being read off in charts.

## exists_homeomorph_smooth_annulus_of_isClosedEmbedding — STUCK (not started in Lean)

- Remaining goal: the entire conclusion.
- The same missing inputs as the disk leaf, for a closed annulus in `∂M`:
  - an annular coordinate neighbourhood in the surface (both boundary circles tame);
  - an ambient move onto `S¹ × [0,1]` inside a smooth open annulus `S¹ × ℝ → ∂M`
    (`Homeomorph/JordanAnnulus.exists_homeomorph_jordan_annulus` is planar);
  - the collar extension to `θ`.

## isSmoothHandleStage_adjunction_two — STUCK (not started in Lean)

- Remaining goal: the entire conclusion.
- No orientation obstruction here. The free part `Δ² × {0,1}` of `∂(Δ² × [0,1])` consists of
  two disks, so any annulus homeomorphism (ends possibly swapped, circle possibly reflected)
  extends radially over the two end disks, and then over the ball.
- Main missing brick: the same smooth gluing, along the annulus `f (S¹ × [0,1])`, with rounded
  corners.

## exists_isSmoothEmbedding_sphere_of_isClosedEmbedding — STUCK (not started in Lean)

- Remaining goal: the entire conclusion. This is the leaf the skeleton calls the one deep
  independent producer.
- Sub-obligations:
  1. `range ψ` is open and closed in `∂M` (invariance of domain in the 2-manifold
     `BoundaryManifold`; `InvarianceOfDomainManifold.lean` has the real-model statements).
  2. It is therefore a closed smooth surface homeomorphic to `S²`.
  3. Uniqueness of the smooth structure on `S²`: such a surface is diffeomorphic to the round
     sphere. The route through Morse theory needs a Morse function with exactly two critical
     points, via cancellation on a simply connected surface, and then Reeb's theorem. The
     partial inputs named in the skeleton (`CompactCriticalValues`, `CubicCancellation`,
     `SaddleMinimumStrip`) do not assemble into it.
- Estimate: the largest leaf of the file.

## isSmoothHandleStage_adjunction_three — CLOSED

- Files (all new; imports ≤ 100 characters):
  - `DifferentialGeometry/Topology/PiecewiseLinear/SmoothBoundarySphereCollar.lean`: 242 lines,
    SHA-256 `abd589e9a6b4a3d231be4aeb01aecddc6a059b7867a5ff6c3646af85f392e758`.
  - `DifferentialGeometry/Topology/PiecewiseLinear/SmoothCapAttachment.lean`: 636 lines, SHA-256
    `475a6e1289c9d8b9a2ed35d6244e9499d686f15a8c15e3d2e34052c97a5f1475`.
  - `DifferentialGeometry/Topology/PiecewiseLinear/IsSmoothHandleStageAdjunctionThree.lean`: 126
    lines, SHA-256 `1f1e2dbf1a8c0ec4b0498e1b443c1748e6a4b98f4737f6ca102ddadb3257da30`.
- The leaf is restated byte-identically. It uses the skeleton's opens, namespace, `universe u` and
  the `variable {E F …}` line, which the statement does not mention. A script compared the
  statement against the skeleton text: identical.
- Wiring: import `IsSmoothHandleStageAdjunctionThree` and delete the skeleton leaf. The call at
  skeleton line 505 is unchanged. No frozen hypothesis was dropped, and none is unused.
- New public names (all grepped first):
  - `exists_radialCollar_of_isSmoothEmbedding_sphere`;
  - `halfSpaceShiftFun`, `halfSpaceShiftFun_val`, `halfSpaceShift`, `halfSpaceShift_val`,
    `halfSpaceShift_contMDiffOn`, `halfSpaceShift_symm_contMDiff`: a chart of `ℝ³` into the
    interior of `EuclideanHalfSpace 3`;
  - `exists_isManifold_of_isOpenEmbedding_of_ballChart`;
  - `exists_capChart_of_radialCollar`;
  - `isSmoothHandleStage_adjunction_of_radialCollar`;
  - `exists_closedCell_homeomorph_of_range_eq`.
- Route:
  1. Radial collar. As a map into `BoundaryManifold`, `d` is a smooth injective immersion between
     surfaces (mfderiv chain rule through `boundaryInclusion`). By
     `exists_diffeomorph_onto_range_of_injective_immersion` it is a diffeomorphism onto an open
     subset of `∂M`. Pushing that set along the defining-function collar
     (`exists_definingFunction_sublevel_collar`) gives an open `V ⊇ range d`, with smooth
     `θ : V → {1 ≤ ‖v‖ < 1 + a}` and inverse `Θ`, where `Θ` restricted to the unit sphere is `d`.
  2. Generic gluing (`exists_isManifold_of_isOpenEmbedding_of_ballChart`). Take an open part `U`
     of a smooth `M` embedded openly in `X`, plus one chart of `X` onto a ball, with smooth
     transitions in both directions. The atlas made of `M`'s charts lifted by
     `lift_openEmbedding` and the ball chart shifted into the open half space gives an
     `IsManifold (𝓡∂ 3) ∞` structure. The boundary is exactly the image of `U ∩ ∂M`, by
     `isBoundaryPoint_iff_any_chart_real`.
  3. Cap chart. `κ` is the quotient lift of `Ext` on the cell and `θ` on `M`. Its inverse is
     piecewise (the cell inside the unit ball, `Θ` outside), and `ContinuousOn.if` matches the
     two pieces on the unit sphere.
  4. Cone step. `Ext` is the radial extension (`closedCellHomeomorphExtension`) of the sphere
     homeomorphism `d⁻¹ ∘ ψ`, so the parametrisation of `ψ` never needs to be smooth.
- The proof is split into five lemmas to keep each declaration within the default heartbeats.
  No `set_option` is used.
- Checker: all three modules `Verified ... with no diagnostics; shared outputs unchanged.` Audit
  `AuditOpusD8.lean` (all three modules): `Verified ... with no diagnostics; shared outputs
  unchanged.` Axioms are within `propext`, `Classical.choice` and `Quot.sound`; all thirteen
  linters pass.
- Compiles: 3 checks for the collar module (2 failed), 7 for the gluing module (1 heartbeat
  failure before the split; 4 other failures and 1 run with a `sorry` placeholder), 3 for the
  leaf module (2 failed), and 1 audit.
- Reuse: the gluing lemma and the half-space shift chart are also inputs for the one-handle and
  two-handle leaves. Those still need corner charts (angle rescaling in collar coordinates) and,
  for `k = 1`, the orientation alignment recorded above.

# Batch 7 (corner charts, one- and two-handles)

## Corner charts and the smooth attachment with rounded corners — VERIFIED, AUDITED

- New modules (all new files; no existing file edited):
  - `ConcaveCornerMap.lean` (311 lines): the corner map `K z = (e^{-iπ/4} z)^{2/3}`, which sends
    the closed three-quarter plane `re ≥ 0 ∨ im ≥ 0` onto the half plane `re ≥ 0`. It has the
    inverse `e^{iπ/4} w^{3/2}`. Both maps are continuous, and smooth away from `0`. The boundary
    rays go to the imaginary axis.
  - `ConcaveCornerChart.lean` (273 lines): the corner chart `(a, b, u) ↦ (re K, (2 + im K) u)` in
    cylindrical coordinates. It has an explicit inverse, is smooth with a smooth inverse off the
    rim, and its first coordinate vanishes exactly on the two boundary rays.
  - `SmoothChartFamilyGluing.lean` (164 lines): `exists_isManifold_of_isOpenEmbedding_of_charts`.
    It glues an open part of `M` with a family of charts and keeps boundary status on the part.
  - `SmoothHandleModelAttachment.lean` (540 lines): the reusable attachment theorem
    `isSmoothHandleStage_adjunction_of_modelCharts`. The handle sits in a normed space `Z` as
    `range Ext`, and a smooth collar `(V, θ, Θ)` meets it in `Ext '' range i`. A family of model
    charts `(D j, Tg j, ζ j, ζinv j)` must be smooth off a singular set `Rim ⊆ range Ext` on which
    no two charts overlap. The conclusion is a stage with boundary
    `lower '' (∂M \ range ψ) ∪ cell '' Fr`, where `Fr` is read off the first coordinate.
    Also: `adjunctionLower_boundary_sdiff_union_eq`, which converts to the leaf boundary form.
  - `HandleModelCharts.lean` (352 lines): slab charts `(w, s) ↦ (σ s + c, w)` and corner charts
    `cornerModelVec L`. The latter use an arbitrary affine change `L` from `(‖w‖, s)` to corner
    coordinates, so the same lemmas give both rims of both handles, rescaled as needed.
  - `TwoHandleModelAttachment.lean` (527 lines): the two-handle model. The handle is the closed
    unit ball of `ℝ² × ℝ` with the product norm, `‖w‖ ≤ 1, |s| ≤ 1`, so that
    `sphereRadialHomeomorph` cones over its boundary. The collar is
    `1 ≤ ‖w‖ < 1 + a, |s| < 3/2`, with `a ≤ 1/2`. There are five charts (interior, two faces, two
    rims), and the result is `isSmoothHandleStage_adjunction_of_twoHandleCollar`.
- All six modules: `Verified ... with no diagnostics; shared outputs unchanged.` Audit
  `AuditOpusD9.lean` (all six modules): `Verified ... with no diagnostics`. Axioms are within
  `propext`, `Classical.choice` and `Quot.sound`; all thirteen linters pass.
- Route and design notes:
  - Only the handle needs model charts: points of `M \ range ψ` keep the charts of `M`.
  - A transition between two different charts never meets the rim, so the non-smoothness of the
    corner chart at the rim only enters through identity transitions.
  - Plan for the one-handle model: use the same corner lemma with
    `L (r, s) = ((-1 - s)/2, (1 - r)/2)`. With this rescaling the two corner charts cover the
    whole free side, so three charts should suffice.

## isSmoothHandleStage_adjunction_two — CLOSED

- Leaf module `IsSmoothHandleStageAdjunctionTwo.lean`. The statement is byte-identical to the
  skeleton, checked by a script diff of the theorem header, with the same
  `open`/namespace/`universe u`/variable context. No frozen hypothesis was dropped, and none is
  unused.
- New modules:
  - `SmoothAnnulusCollar.lean` (`exists_twoHandleCollar_of_isSmoothEmbedding`): the cylindrical
    collar `V ≅ {1 ≤ ‖w‖ < 1 + a, |s| < 3/2}` of `f (S¹ × (-1/4, 5/4))`, with `a ≤ 1/2`, and
    `Θ (u, s) = f (u, (s + 1)/2)` on the side. The route is the same as the sphere collar: an
    injective immersion into `∂M`, then the defining-function collar.
  - `CylinderSideExtension.lean` (`exists_homeomorph_extension_of_cylinderSide`): every
    homeomorphism of the side `‖w‖ = 1, |s| ≤ 1` extends to a norm-preserving homeomorphism of
    `ℝ² × ℝ` (sup norm). Steps:
    - The rim circles are preserved. For the interior this is invariance of domain in the planar
      annulus `1 ≤ ‖x‖ ≤ 3`.
    - The rim signs come from connectedness of `S¹`.
    - The rim circle maps become homeomorphisms, and their radial extensions fill the caps.
    - The result is a compact-to-T2 bijection of the unit sphere, extended by
      `sphereRadialHomeomorph`.
  - `TwoHandleAlignment.lean` (`exists_twoHandle_alignment`): builds `Ext` from
    `prismBallHomeomorph` (heights rescaled to `[-1, 1]`) followed by the extension of the side
    map `f⁻¹ ∘ ψ`. `Ext` is a closed embedding onto the cylinder with side ↔ `∂Δ² × I` and
    `|s| = 1` ↔ ends, and `Ext z = ((g z).1, 2 (g z).2 - 1)` with `f ∘ g = ψ`.
- The leaf applies `isSmoothHandleStage_adjunction_of_twoHandleCollar` and then rewrites the
  boundary with `adjunctionLower_boundary_sdiff_union_eq`, since the points of `ψ '' (∂Δ² × {0,1})`
  are `cell` points of the end faces.
- Checker: all four modules `Verified ... with no diagnostics; shared outputs unchanged.` Audit
  `AuditOpusD10.lean` covers the ten Batch 7 modules and passes (`Verified ... with no
  diagnostics`). An earlier audit run flagged an unused `[T2Space M]` in
  `exists_twoHandle_alignment`; it was removed and the module rechecked.

## isSmoothHandleStage_adjunction_one — CLOSED

- Leaf module `IsSmoothHandleStageAdjunctionOne.lean`. The statement is byte-identical to the
  skeleton, checked by a script diff, with the same context. No frozen hypothesis was dropped, and
  none is unused.
- New modules:
  - `OneHandleModelAttachment.lean` (`isSmoothHandleStage_adjunction_of_oneHandleCollar`): the
    one-handle model is the cylinder `‖w‖ ≤ 1, |s| ≤ 1`, attached along its ends, with collar
    `‖w‖ < 3/2, -1 - a < s ≤ -1 or 1 ≤ s < 1 + a`. It uses three charts: the interior slab, and
    two corner charts in the rescaled coordinates `L (r, s) = ((∓1 - s)/2 or (s - 1)/2, (1 - r)/2)`,
    which between them cover the whole free side.
  - `SmoothDiskPairCollar.lean` (`exists_oneHandleCollar_of_isSmoothEmbedding`): the product
    collar of two disjoint smooth boundary disks, with `Θ (w, -1) = F 0 w` and
    `Θ (w, 1) = F 1 w`.
  - `CylinderEndExtension.lean` (`exists_homeomorph_extension_of_ends`):
    - A disk homeomorphism preserves the rim; this is invariance of domain.
    - `hasIncreasingCircleLift_reflect_iff`: composing with the planar reflection flips the
      orientation character.
    - Two end-disk homeomorphisms whose rim maps have the same orientation extend to a
      norm-preserving homeomorphism of `ℝ² × ℝ`. The side comes from
      `exists_homeomorph_cylinder_of_same_orientation`, and the whole is assembled on the unit
      sphere with `sphereRadialHomeomorph`.
  - `OneHandleAlignment.lean`:
    - `exists_oneHandle_end_assignment`: each end is connected, so it goes onto exactly one of the
      two disks, and the two ends go onto different disks.
    - `exists_endDisk_homeomorph` and `exists_oneHandle_alignment`: if the orientations differ,
      the top disk is reparametrised by `planarReflection`, with `L = id ∨ L = planarReflection`.
      The frozen leaf is unchanged because `f j ∘ L` has the same image and is still a smooth
      embedding (`IsSmoothEmbedding.comp_diffeomorph` with `planarReflectionDiffeomorph`).
- Checker: all five modules `Verified ... with no diagnostics; shared outputs unchanged.` Audit
  `AuditOpusD11.lean` covers all fifteen Batch 7 modules and passes (`Verified ... with no
  diagnostics`). Axioms are within `propext`, `Classical.choice` and `Quot.sound`; all thirteen
  linters pass.
