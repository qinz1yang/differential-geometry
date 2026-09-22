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
