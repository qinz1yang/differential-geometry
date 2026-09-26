# OPUS_FILL_LOG_SW3 — entry 27c, `BoundedCurvatureSpatiallyCanonical` (2026-09-26)

- `SpatialLocalCap.coreModel : CapCore core.carrier` (`FiniteHornGeometry.lean:155`): purely
  topological (image of the closed unit ball under a partial diffeomorphism, or a projective
  presentation). No metric model, no fixed family: any positive-time slice is admissible.
- Route chosen: no compactness/perturbation of witnesses. Uniform far control instead:
  file 1 `Perelman/StandardSolution/StandardFarRegion.lean`: by contradiction with the cylinder
  slice convergence, for `t ∈ [0, Θ]` and `‖x‖ ≥ D`: an `eps`-`SpatialNeck` at `x` whose map is
  radial `(‖x‖ + c a) • rot(x) q` (`c = √(1 - t_lim)`), plus radial metric control
  `⟪x,v⟫²(1-θ) ≤ ‖x‖² g(v,v)`, `g(x,x) ≤ (1+θ)‖x‖²`.
  file 2 `Perelman/StandardSolution/StandardSliceSpatialCanonical.lean`: distance sandwich from
  the radial control (smooth soft radius, `ofReal_abs_sub_le_riemannianEDistOf`; radial segment
  length), tip cap = closed Euclidean ball with a one-neck radial tube, far points = neck witness.
- PROVED (no sorry): file 1 `StandardSolution.exists_far_radial_spatialNeck` (eps, Θ<1, θ>0 ⇒ ∃ D
  for all `t ∈ [0,Θ]`, `‖x‖ ≥ D`); file 2 `StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts`
  (∃ C ≥ 1, every `(S, x, t)`, `t ∈ [0, Θ]`, witness `eps C C` with `capTubeHasNeckChart eps`: all of
  `[0, Θ]`, no curvature or age restriction) and the discharge
  `StandardSolution.exists_boundedCurvatureSpatiallyCanonical : ∀ τ₀ Λ, 0 < τ₀ → ∃ C, 1 ≤ C ∧
  BoundedCurvatureSpatiallyCanonical Θ eps τ₀ Λ C` (exactly the `hband` input of
  `…_of_bounded_curvature`). Not wired into the root aggregate.
- Compile (read-only, `LEAN_NUM_THREADS=2 lake env lean`): file 1 in place, no diagnostics. File 2
  needs olean-less StandardInitialSpatialCanonical/StandardYoungSpatialCanonical/file 1: scratch
  concatenation (static + young + file 1 + file 2) outside the repo, no diagnostics. Axioms (scratch):
  propext, Classical.choice, Quot.sound for all three headlines. `#lint` (scratch): only docBlame on
  the pre-existing def `BoundedCurvatureSpatiallyCanonical`. Lines ≤ 100.
