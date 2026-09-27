# SB11 — brick B11, arms from one separating central sphere (2026-09-26)

Outcome: DONE, sorry-free. File `Surgery/Topology/SeparatingSphereAxialArms.lean` (259 lines).

## Consumer data matched (HornNeckImprovement:249, `exists_strongNeck_threshold_of_minimizing_arms`)
`arms : Fin 2 → MinimizingArm (G.flow.base.metric t) x`, `ell : Fin 2 → ℝ`,
`∀ j, ell j ∈ Ioc 0 (arms j).length`, `∀ j, √(G.flow.scalar t x) * ell j ∈ Icc D (2*D)`,
`angle ≤ comparisonAngle (ell 0) (ell 1) (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1)))`,
used with `angle = π/2`. The new slab theorem feeds `hthr` with exactly these.

## Public statements
- `FiniteHorn.SpatialNeck.exists_minimizingArms_of_separating_centralSphere`
  (hg complete, nk : SpatialNeck g eps x, eps ≤ 1/252, 0 < D, far points y z with
  `D ≤ √R(x)·d(x,y)`, `D ≤ √R(x)·d(x,z)`, `z ∉ connectedComponentIn Σᶜ y`, Σ = nk.map '' (univ ×ˢ {0}))
  → arms with ell ≡ D/√R(x) (or the axial ones), angle ≥ π/2.
- `IncomingSlab.exists_strongNeck_threshold_of_separating_centralSphere`: H's binders verbatim, then
  `∀ {eps} (nk : SpatialNeck (G.flow.base.metric t) eps x), eps ≤ 1/252 → ∀ y z, (two far points) →
  (separation) → Nonempty (StrongNeck G.flow delta x t)`.

## Form of (c) and why (a), (b) are absent
- (c) taken as a hypothesis: two points at normalized distance ≥ D (not 2D) with `z ∉ connectedComponentIn Σᶜ y`.
  Not derivable from neck + ball: separation by a neck sphere is global (S²×S¹ neck sphere does not separate).
- (a) compact containment and (b) `R ≤ Cb R(x)` are NOT used: at t < s the slice lives on the compact carrier,
  complete (`RiemannianMetricComplete.of_compact`), so minimizers exist globally. Adding them would be
  unused arguments (AGENTS). Their role is upstream: supplying the far points / separation of (c) (B9/B10).
- Proof: D ≥ 28: arm from x to each far point; the point at parameter D/√R stays off Σ (Σ ⊆ closedBall(x,7/√R),
  `central_sphere_subset_closedBall`), so it is in the far point's Σᶜ-component; then
  `metricDistance_ge_of_separating_slices` (NeckChainAxialArms:131) with chain p, x, q gives
  d(p,q) ≥ 2ℓ − 14/√R ≥ 3ℓ/2, cos ≤ 0. D < 28 ≤ eps⁻¹/9: axial arms (`SpatialNeck.exists_axial_minimizingArms`,
  NeckRegionAxialArms:149). `open private exists_minimizingArm_of_edist_ne_top` (NeckRegionAxialArms:28).

## Checks
- `LEAN_NUM_THREADS=2 lake env lean <file>` (also with `-Dweak.linter.mathlibStandardSet=true`): no output.
- Scratch copy (outside repo): axioms of both public theorems = [propext, Classical.choice, Quot.sound];
  `#lint`: 0 errors, 14 linters. Lines ≤ 100. No git writes, no lake build, not registered in the root aggregate.
