# SB10 — brick B10, horn central-sphere separation for B11's clause (c) (2026-09-26)

- start: read AGENTS, NAMING, Skeleton README, DESIGN_S_FACTORY, SB9, SB11, B3, B11 file, horn objects.
- finding: slice-level global separation (B11's `z ∉ connectedComponentIn Σᶜ y` in the compact carrier) is
  NOT derivable and false in general; writing a ball-local B11 variant + terminal horn separation.

## Outcome: DONE with one precisely stated gap (the slice transfer). File `Surgery/Topology/HornCentralSphereSeparation.lean` (584 lines), sorry-free.

### (1) at slice level, as B11 states it: NOT derivable, false in general
- B11 (`SeparatingSphereAxialArms`) wants `z ∉ connectedComponentIn Σᶜ y` in the WHOLE compact carrier at time t < s.
- Counterexample: a neckpinch on S²×S¹. Terminal regular open = S²×(0,1), one component, two horns; the neck
  sphere Σ = S²×{θ} separates the terminal component but not the carrier. `OrientedThreeStage` records no
  simple connectivity / H₁(M;Z/2)=0, so no global carrier separation is available from horn data.
- Also B11 needs `RiemannianMetricComplete`; the terminal metric is incomplete, so B11 cannot be fed at time s either.
  B11's theorem is therefore NOT imported (it would be an unused import).
- Replacement delivered: a ball-local B11 (separation only inside `B(x, r)`, compact closed ball instead of
  completeness), and its slab form. Local separation is what the horn really gives.

### Public statements
- `FiniteHorn.SpatialNeck.exists_minimizingArms_of_locally_separating_centralSphere`: any g (no completeness),
  `nk : SpatialNeck g eps x`, `28 ≤ D`, `3·(D/√R) < r`, `IsCompact (closedBall x r)`, `U V` open disjoint with
  `ball(x,r) \ Σ ⊆ U ∪ V`, `y ∈ U`, `z ∈ V`, `ofReal(D/√R) ≤ edist x y < ofReal r` (same for z)
  ⇒ B11's conclusion (arms, `√R·ell ∈ [D,2D]`, angle ≥ π/2).
- `IncomingSlab.exists_strongNeck_threshold_of_locally_separating_centralSphere`: H's binders verbatim, then
  `nk` (slice t), `eps ≤ 1/252`, `U V` open disjoint, `ball_t(x, 4D/√R) \ Σ ⊆ U ∪ V`, `y ∈ U`, `z ∈ V`,
  `ofReal(D/√R) ≤ edist_t x y < ofReal(4D/√R)` (same z) ⇒ `Nonempty (StrongNeck G.flow delta x t)`.
  Small D (9D < eps⁻¹): axial arms as in B11.
- (1) terminal: `TerminalCorePresentation.exists_deep_horn_centralSphere_sides`: ∃ eta>0, ∀ P, ε ≤ eta, c ∈ component,
  e, ∃ Q>0, ∀ NormalizedNeck N (δ ≤ ε, ⌊ε⁻¹⌋₊+1 ≤ k, centre in `hornHalfRange P c e`, Q < scale),
  ∃ U V open disjoint, `U ∪ V = (N.chart '' {z | z.val.2 = 0})ᶜ`, `P.core c ⊆ U`,
  `∃ u₀, ∀ y u, u₀ < u → P.horn c e (y,u) ∈ V`, `∀ w ∈ U, ∀ z ∈ V, z ∉ connectedComponentIn Σᶜ w`.
  (Global in the terminal regular open.) Helper `closure_positiveHornMap_image_subset` (horn_proper ⇒ closed map).
- (3) terminal: `TerminalCorePresentation.isCompact_riemannianClosedBallOf_of_scalar_le`: `c ∈ component`,
  `mk x = c`, `0 < r`, `r' < r`, `∀ z ∈ ball_L(x,r), R_L(z) ≤ K` ⇒ `IsCompact (closedBall_L x r')`
  (ball ⊆ core ∪ ⋃ horns up to the divergence depth of K; finite horn index).
- Corollary `TerminalCorePresentation.exists_minimizingArms_of_horn_point`: ∃ eta, … same N-prefix …,
  `28 ≤ A`, (2) `∀ w ∈ frontier (P.core c), ofReal(2A/√R_L(x)) < edist_L x w`,
  (3) `∀ z ∈ ball_L(x, 5A/√R_L(x)), R_L(z) ≤ Cb·R_L(x)` ⇒ arms in `D.terminal.metric` with `√R·ell ∈ [A,2A]`,
  angle ≥ π/2. The far points are the tree's `exists_horn_side_points_at_distance` (HornEndpointRadius:102).

### Horn objects used
Contract/Terminal.lean:58 (`horn_proper`, `horn_injOn`, `horn_covers_component`, `horn_scalar_diverges`,
`horn_base_covers_boundary`, `horn_pos_notMem_core`); HornNeckEssentiality.lean:280
(`exists_deep_horn_neck_end_separation_tolerance`: ComplementPair of the neck sphere in horn coordinates);
HornNeckCoordinates.lean:110–137 (`positiveHornDomain`, `positiveHornMap(_local)`);
HornEndpointRadius.lean:102; NeckSpatialBridge.lean:56 (`NormalizedNeck.exists_spatialNeck`);
CompactMinimizer.lean:332; NeckRegionBall.lean:214. The (2) "+C / separating-slices chain" is unnecessary:
the frontier-distance hypothesis feeds `hbase` directly.

### Hypothesis shapes
- (3) is B3b's shape (`OPUS_FILL_LOG_B3.md`: "∀ z ∈ B_t(y, A/√R(y,t)), R(z,t) ≤ Q·R(y,t)") written for the
  terminal metric with A := 5A_arm. B3b produces it on slices t < s; the terminal form is its τ → s limit
  (not proved here).

### Missing brick (B10-proper, slice transfer), stated precisely
From the terminal data above to the slab theorem at τ → s: (i) slice neck `nk_τ` at x with the SAME map as the
terminal neck (then Σ_τ = val '' Σ); (ii) `ball_τ(x, 4D/√R(x,τ)) ⊆ Ω` (compactly), so that
U_τ := val '' U, V_τ := val '' V are open in the carrier, disjoint, and cover `ball_τ \ Σ_τ`;
(iii) points y ∈ U, z ∈ V with `D/√R(x,τ) ≤ d_τ(x,·) < 4D/√R(x,τ)` (from the terminal side points at
normalized distance 2D via metric convergence on the compact ball). Then
`exists_strongNeck_threshold_of_locally_separating_centralSphere` applies.

## Checks
- `LEAN_NUM_THREADS=2 lake env lean <file>` (waited ~10 min for another lane's rebuild of Diagonal* oleans):
  no output; also clean with `-Dweak.linter.mathlibStandardSet=true`.
- Scratch copy outside the repo: all six public theorems depend on [propext, Classical.choice, Quot.sound];
  `#lint`: 0 errors in 12 declarations, 14 linters. Lines ≤ 100 chars. No git writes, no lake build, not registered.
