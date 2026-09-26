# OPUS_FILL_LOG_SW2 — young spatial canonical witnesses of the standard solution (2026-09-26)

- Start: read SW log, StandardSpatialCanonical (young clause), EndNeckPerturbation, LocalInitialSpatialCap,
  metric/curvature control. Finding: young region `t·R < τmin` is NOT inside the initial layer for the
  `τmin` the old-point theorem produces (`τmin ≥ 1`; far points at `t < 1/2` have `t·R ≈ t/(1-t) < 1`).
  Plan: prove the initial layer `t ∈ [0, τ(eps)]` fully; isolate the positive-time bounded band.
- New file `Perelman/StandardSolution/StandardInitialSpatialCanonical.lean` (not wired).
- PROVED (file 1, `StandardInitialSpatialCanonical.lean`, 715 lines): initial layer
  `StandardSolution.exists_initial_spatialCanonicalWitness_with_cap_neck_charts`:
  `∀ eps ∈ (0,1/11), ∃ τ C, 0<τ ∧ 1≤C ∧ ∀ S x t, t ∈ Icc 0 τ → ∃ W : SpatialCanonicalWitness … eps C C x,
  W.capTubeHasNeckChart eps`. Route: static theorem `StandardCap.exists_uniform_spatialCanonicalWitness_of_metric_close`
  (any metric on ℝ³ with 1 ≤ R ≤ B, |Rm| ≤ K, |∇R| ≤ G, C^⌈1/eps⌉-close to the initial cap metric):
  far points (‖x‖ > (r+1)/10) = rotated end neck (`EndNeckPerturbation` + `pointedInitialRotation` +
  `SpatialNeck.exists_image_of_local_isometry`) + generic `exists_uniform_spatialNeck_canonicalWitness`
  (ball sandwich 9/√Q from NeckRegionBall, volume from BallVolume); tip points = explicit `SpatialLocalCap`
  on closedBall 0 (r+1) (core closedBall r, tube = one-neck annulus, r ≥ 20000 gives depth ≥ 10000),
  ball sandwich from 11/10 distance comparison. Inputs: one_le_scalar, initial curvature control,
  uniform ∇Rm bound on [0,1/2], `standard_uniform_fixed_cap_metric_bounds` (C^N rate L·t).
  Uses `open private exists_compactDomain_of_cylinder_slab` (precedent in NeckCapCompactDomains).
- PROVED (file 2, `StandardYoungSpatialCanonical.lean`): `exists_youngSpatiallyCanonical_of_le_initial_time`
  (`YoungSpatiallyCanonical Θ eps C τmin` for Θ<1, τmin ≤ τ); reduction
  `youngSpatiallyCanonical_of_bounded_curvature` and the consumer form
  `exists_spatialCanonicalWitness_with_cap_neck_charts_of_bounded_curvature` from the ONE named input
  `StandardSolution.BoundedCurvatureSpatiallyCanonical Θ eps τ₀ Λ C` (∀ S x t, t ∈ Icc τ₀ Θ → R ≤ Λ → witness),
  assumed `∀ τ₀ > 0, ∀ Λ, ∃ C ≥ 1`. Not reducible further: old-point τmin ≥ 1, far points at t < 1/2 are young.
- Compile: file 1 `LEAN_NUM_THREADS=2 lake env lean` in repo: no diagnostics. File 2 needs the olean-less
  StandardSpatialCanonical: scratch concatenation (file1 + StandardSpatialCanonical + file2) outside the repo,
  no diagnostics. Axioms (scratch, deleted): propext, Classical.choice, Quot.sound for all three headlines.
  `#lint` (scratch): only docBlame (excluded). Lines ≤ 100. Not wired into the root aggregate.
