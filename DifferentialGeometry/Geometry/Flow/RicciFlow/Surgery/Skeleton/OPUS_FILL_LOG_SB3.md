# SB3 — bricks B3a/B3b (and B4 if it fits): coarse presentation on spatial witnesses (2026-09-26)

## Progress
- 10:50 UTC start. Read AGENTS, NAMING §2–6, Skeleton/README, DESIGN_S_FACTORY, SpatialCanonicalWitness,
  CanonicalNeighborhoodInduction (SpatiallyCanonicalBefore, DerivativeBoundBefore, EventSlabsSpatiallyCanonical).
- Traced the A1 chain (TerminalCorePresentationExistence:431) down to its witness-reading leaves:
  A1:431 → Contract/TerminalCutoffScale:111 → TerminalSphericalRegionExterior:162 → :14 →
  {TerminalSphericalRegion:23 → TerminalBarrierComponents:54 → TerminalSphericalBarrierFamily:79 →
   TerminalSphericalBarrierCover:18 → TerminalSphericalBarrier:449 ;  TerminalCapCore:287}.
  Leaves reading witness fields: TerminalCanonicalAlternatives:18/33/59, TerminalSphericalBarrier:21/41/67/133,
  TerminalCapBarrier (scalar bounds, midpoint region), TerminalCapNormalization:17/39/82, TerminalCapCapture:23,
  TerminalNeckNormalization:74/304/409/434/498, TerminalCapCore:23/146/182, CapTruncation (LocalCap topology),
  CapCollarDepth:20.
- Finding: no site in the A1 chain reads `time_derivative` of the HYPOTHESISED witnesses. Every time-derivative
  bound used there (S1: compact capture of scalar sublevels, `exists_compact_subset_terminalRegularRegion_...`)
  is taken from the slab's own qualitative constants `G.exists_all_point_canonical_neighborhoods`
  (IncomingModelCoverage:169). So the spatial A1 needs NO derivative clause; adding one would be an unused
  hypothesis. Hypothesised witnesses are read only for: `alternative` (neck at τ, cap core/tube, cap tube neck
  chart), `scalar_bounds`, `domain`, `inside_ball`/`radius_upper` (not in A1 chain), `one_le_comparison_constant`.
- 11:35 UTC. File 1 `Surgery/Topology/TerminalSpatialCanonicalAlternatives.lean` (~900 lines so far) compiles
  clean (`LEAN_NUM_THREADS=2 lake env lean`): SpatialLocalCap topology (tubeMap_mem_core_iff, truncation),
  `SpatialCanonicalWitness.alternative_eq_neck_or_cap_of_mul_scalar_lt`, terminal normalization of moving
  spatial necks (copy of TerminalNeckNormalization:74/304/409/434/21/41 on `SpatialNeck (g(τ n))`),
  spatial neck-or-cap sequence (TerminalCanonicalAlternatives:18/33/59), spatial cap capture/normalization
  (TerminalCapNormalization:17/39/82 + TerminalCapCapture:23 inlined), scalar bounds (TerminalCapBarrier:18).
  One olean-missing interruption (acceptance build), resolved on retry.
- 12:40 UTC. DONE for B3a + B3b. B4 NOT attempted (see below).

## Outcome
B3a + B3b PROVED, sorry-free; B4 not started.
- File 1 `Surgery/Topology/TerminalSpatialCanonicalAlternatives.lean` (1444 lines, B3a leaves).
- File 2 `Surgery/Contract/TerminalCorePresentationOfSpatiallyCanonical.lean` (1118 lines, B3b chain + A1).
- No original file edited. Not registered in the root aggregate. No git writes, no lake build.

## A1: original vs new (TerminalCorePresentationExistence:431 and :654)
Original :431 (`..._with_scale_bound_and_base_necks_of_canonical_neighborhoods`), hypothesis:
  `(∀ x t, t ∈ Ioo D.startTime D.endTime → q < D.slab.flow.scalar t x →
     ∃ W : CanonicalWitness D.slab.flow εcan C1 C2 x t, W.capTubeHasNeckChart εcan) →`
  head: `∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧ ∀ C1 C2 : ℝ, 1 ≤ C2 → ∃ C Λ ...`
New `OneStepIncoming.exists_neckRadius_terminalCorePresentation_with_base_necks_of_spatiallyCanonical`:
  `∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧ 104000 * εcan ≤ ε ∧ ∀ C1 C2 : ℝ, 1 ≤ C2 → ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
   ∀ q : ℝ, 0 < q → ∀ D : OneStepIncoming.{u}, D.slab.SpatiallyCanonicalBefore εcan C1 C2 q D.endTime →
   ∀ q' : ℝ, q ≤ q' → ∃ ρ hρ, ...` (conclusion verbatim from :431).
New `OneStepIncoming.exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_spatiallyCanonical`:
  :654 verbatim with the same hypothesis swap and the extra `104000 * εcan ≤ ε`.
`εcan = δreg/4`, `δreg = min η₁ (min η₂ (min (ε/26000) (1/156000)))` exactly as the original (design's ε̄ ≤ δreg/4).
NO derivative clause: none of S1–S3 reads `time_derivative` of the hypothesised witnesses; the S1 compact-capture
bounds use the slab's own `exists_all_point_canonical_neighborhoods`. `DerivativeBoundBefore` would be unused.

## Intermediate siblings (file 2; hypothesis `G.SpatiallyCanonicalBefore (δ / 4) C1 C2 q s` or pointwise)
- `TerminalLimitMetric.exists_spherical_barrier_at_level_of_spatiallyCanonical` ← TerminalSphericalBarrier:449
- `TerminalLimitMetric.spatial_neck_or_cap_core_of_spatiallyCanonical_of_not_isCompact` ← TerminalCapCore:287
- `TerminalLimitMetric.exists_finite_spherical_barrier_cover_of_spatiallyCanonical` ← TerminalSphericalBarrierCover:18
- `TerminalLimitMetric.exists_finite_recorded_spherical_barriers_of_spatiallyCanonical` ← TerminalSphericalBarrierFamily:79
- `TerminalLimitMetric.exists_recorded_barriers_with_compact_closures_of_spatiallyCanonical` ← TerminalBarrierComponents:54
- `exists_uniform_disjoint_spherical_region_of_spatiallyCanonical` ← TerminalSphericalRegion:23
- `exists_uniform_disjoint_spherical_region_with_exterior_alternatives_of_spatiallyCanonical` ← Exterior:14
- `exists_uniform_component_spherical_region_of_spatiallyCanonical` ← Exterior:162
- `OneStepIncoming.exists_neckRadius_spherical_region_with_scale_bound_of_spatiallyCanonical` ← TerminalCutoffScale:111
(names shortened where the literal `_of_spatiallyCanonical` suffix would exceed 100 columns.)

## B3a leaves (file 1), all spatial copies with each `CanonicalWitness` read replaced by the spatial field
- `SpatialLocalCap.{tubeMap_mem_core_iff, mem_truncated_core_on_tube, nonempty_capCore_truncated_core,
  exists_truncated_compactDomain}` ← CapCollarDepth:20, CapTruncation:28/44/94 (purely topological).
- `SpatialCanonicalWitness.alternative_eq_neck_or_cap_of_mul_scalar_lt` ← CanonicalStrictBounds:29 (whole-branch
  exclusion by `scalar_bounds`; positive/round excluded exactly as the original).
- `SpatialNeck.exists_terminal_neckBuffer_pullback_bound` ← TerminalNeckNormalization:74 (uses
  `SpatialNeck.exists_neckBuffer_pullback_bound`).
- `TerminalLimitMetric.eventually_normalizedNeck_of_moving_spatialNecks` ← :304;
  `.eventually_normalizedNeck_of_spatialNecks` ← :409+:434+:498 (intrinsic derivative bound);
  `.eventually_spatialNeck_of_incoming_spatialNecks` ← TerminalSphericalBarrier:41;
  `.exists_neck_spherical_barrier_of_incoming_spatialNecks` ← :67.
- `.eventually_spatial_neck_or_cap`, `.eventually_spatial_neck_or_cap_of_not_isCompact`,
  `exists_spatial_neck_or_cap_sequence_of_eventually` ← TerminalCanonicalAlternatives:18/33/59.
- `.eventually_spatial_cap_neck_compact_capture` ← TerminalCapNormalization:39 + TerminalCapCapture:23;
  `.eventually_scalar_range_on_spatial_domains` ← :17; `.eventually_normalizedNeck_of_spatial_caps` ← :82.
- `.eventually_scalar_bounds_on_spatial_domains`, `.exists_cap_midpoint_region_of_normalizedNeck_of_spatialCap`,
  `.eventually_spatial_cap_midpoint_region` ← TerminalCapBarrier (the last drops one unused conjunct).
- `.eventually_spatial_cap_spherical_barrier` ← TerminalSphericalBarrier:133 (no respectTransparency option needed).
- `.eventually_spatial_neck_slab_subset_spatial_cap_core`, `.eventually_spatial_cap_core`,
  `.spatial_neck_or_cap_core_of_spatial_sequence` ← TerminalCapCore:23/146/182.

## Verification
- File 1: `LEAN_NUM_THREADS=2 lake env lean -Dweak.linter.mathlibStandardSet=true <file1>`: no output.
- File 2 needs file 1's olean (absent: no lake build). Checked by concatenating both files into one scratch file
  outside the repo: `lake env lean -Dweak.linter.mathlibStandardSet=true`: no diagnostics; `#lint`: 0 errors in
  36 declarations, 14 linters. Axioms of both A1 siblings, of the :449 and :287 siblings: propext,
  Classical.choice, Quot.sound. Scratch removed. Lines ≤ 100 (open-private lines wrapped). Public names unique.
- Only option: `set_option autoImplicit false`. No sorry/nolint/heartbeat overrides.

## B4 not done
File budget (two new files, ≤ 1500 lines each) is used (1444 + 1118); A2's chain (DiscardedComponentClassification,
DiscardedCanonicalCoverage, StoppedCapCuttingSide, TerminalComponentClassification) is ~700–1100 more lines.
Also: the B2 lane is editing those A2 files IN PLACE right now (worktree diff adds `Ctime`/`hbound` to
DiscardedComponentClassification, DiscardedCanonicalCoverage, TerminalComponentClassification,
TerminalCanonicalCapture), so a B4 sibling should be written after that lands.
