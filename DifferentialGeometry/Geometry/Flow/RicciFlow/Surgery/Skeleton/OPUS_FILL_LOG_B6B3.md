# B6b'' — history glue for B6d's approximant hypotheses (2026-09-26)

- Start. Read OPUS_FILL_LOG_B6D.md, B6d headline `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants`
  (`AncientPointedFlowLimitTransfer.lean:1206`), `SpatialCanonicalWitness` (structure, alternatives),
  `SpatialCanonicalWitnessTransport.lean` (`pushforward` :929, `pushforwardOfInjective` :1048,
  `restrictOpen` :1106), `CanonicalNeighborhoodInduction.lean` (`DerivativeBoundBefore` :30,
  `SpatiallyCanonicalBefore` :40, `EventSlabsDerivative` :220, `EventSlabsSpatiallyCanonical` :228),
  review G (coordinator).
- B6d's two approximant hypotheses, quoted: (i) "∀ k, ∀ᶠ n, ∀ s ∈ Icc (-(k+1)) 0, ∀ z : W k n,
  z ∈ closedBall (X.obj n).metric basepoint (k+1) → qW < R(h k n s) z → ∃ Wt : SpatialCanonicalWitness
  (h k n s) eps C1 C2 z, Wt.capTubeHasNeckChart eps"; (ii) "∀ k, ∀ᶠ n, ∀ s ∈ Ioo (-(k+2)) 0, ∀ z,
  qD < R(h k n s) z → |derivWithin (R(h k n ·) z) (Iic s) s| ≤ Ctime·R²".
- FAILURE (F1, data gap, both hypotheses): the history data are on OPEN slab intervals
  (`… t ∈ Ioo a t₀ …`). At `v = tₙ + s/Rₙ` equal to an event time (the post-surgery initial metric of
  the next stage), no history clause gives a spatial witness or a derivative bound; likewise at `s = 0`
  when `tₙ = t₀` (only `…Before t₀`). B6d quantifies over EVERY `s`, so (i)/(ii) cannot be produced for
  all `s` from F5 + `EventSlabsDerivative`/`DerivativeBoundBefore`. For each `n` the exceptional set is
  finite. Repairs: (ii) at event times by continuity of `∂ₜR(h s)(z)` along the smooth solution `h`
  (IsSolutionOn on the window) — not done; (i) needs a B6d-side change (use approximant slices at
  regular times `s'ₙ → s`, or quantify over `s` outside a finite set per `n`).
- FAILURE (F2, containment): a witness at the stage point `f j z` yields one for `h k n s` on `W k n`
  only when the witness's closed ball (radius > 2·radius) and all its neck charts (neck, cap-chain
  necks, cap-tube chart neck) lie in `range (f j)`. This is not implied by the data for every `z` in
  the (k+1)-ball: it needs (a) neck-window extent bounds (`exists_spatialNeck_window_edist_le`,
  B6d, uncommitted) and cap-chain extents, (b) backward non-shrinking of `h s` distances on `W` from the
  rescaled pinching (`Ric ≥ −o(1)`), so that the h(s)-ball of radius `E/√qW` around `z` stays in `W`
  (time-0 radius k+3) once `qW ≥ E²` (B6d's `qW` is free, so this is admissible). Review G(2)
  suggests B6d's approximant input be the NECK ALTERNATIVES rather than full witnesses; then only
  neck windows need (a)+(b).
- Threshold (review G(1)): the derivative glue asserts the bound where `R(h s) z > qD` with
  `q ≤ R·qD` (strict margin preserved: `R_stage > R·qD ≥ q`); take `qD ≥ sup qcanₙ/Rₙ` (e.g.
  `qcanₙ ≤ Cq·Rₙ`, `qD := Cq`). The limit-side margin is B6d's.
- DONE (what is proved), file `Surgery/Topology/TracedRegionAncientLimitWitnesses.lean` (327 lines;
  imports `TracedRegionAncientLimitData`, `SpatialCanonicalWitnessTransport`,
  `MasterFlowCompatibility`, `TowerInductionStep`; not the B6d files, which it does not use).
  In-repo read-only `LEAN_NUM_THREADS=2 lake env lean`: no output. Scratch copy: `#lint` 14 linters,
  only docBlame (excluded) on the def; axioms of all 8 public declarations: propext,
  Classical.choice, Quot.sound. Names unique. Not registered in the root aggregate.
  1. `FiniteHorn.SpatialCanonicalWitness.localPullOfInjective` (+ `capTubeHasNeckChart.localPullOfInjective`)
     and `FiniteHorn.exists_spatialCanonicalWitness_scaleMetric_localPullMetric`: a witness for `g`
     at `f w` (+ neck chart) with its closed ball and neck charts inside `range f` gives a witness
     (+ chart) for `scaleMetric c (localPullMetric g f)` at `w` (injective local diffeomorphism `f`).
  2. `FiniteHorn.abs_derivWithin_parabolic_le_of_abs_derivWithin_le` (any `s`, differentiable or not)
     and `FiniteHorn.abs_derivWithin_scalar_le_of_scaleMetric_localPullMetric` (scaled pullback on a
     left neighbourhood).
  3. `ObservedHistory.abs_derivWithin_scalar_le_of_survivor_maps`: B6b' survivor data (iv) + a
     stage-level bound at regular times ⇒ B6d's (ii) at every `s ∈ Ioo (−θ) 0` whose time is not a
     stage start time.
  4. `RetainedCoreHistory.abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds`: B5-form
     `EventSlabsDerivative` + current `DerivativeBoundBefore` + final-slab clause ⇒ the stage-level
     bound at regular times `v < t`.
  5. `ObservedHistory.mem_stageDomain_activeStage_of_le`.
- NOT delivered: the composed headline (blocked by F1, F2).
