# B3c — cone exclusion at the escape radius + headline (2026-09-26)

- 03:02 start: read AGENTS.md, NAMING.md §2–6, Skeleton/README.md, OPUS_FILL_LOG_B3B.md,
  BoundedCurvatureAtDistanceLimit.lean. Next: survey the NormalizedSequence cone chain.
- 03:19 survey done. Reusable generic pieces found (all compiled, none tied to NormalizedSequence):
  `exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape` (TerminalScalarRay:490, the
  limit ray for incoming slabs), `nonempty_spatial_neck_at_limit_of_endpoint_blowup`
  (Neck/PointedEndpoint, sequence necks on segments -> limit necks),
  `SpatialNeck.exists_at_minimizing_point_of_frontier_eq_slice` (Neck/SpatialMinimizer),
  `exists_punctured_cone_end_of_spatial_necks` (Neck/FiniteEnd:1076, needs Rm >= 0 on the whole
  limit), `sectional_nonnegative_of_pointed_admissible_pinching` (PointedPinchingLimit),
  `exists_scalar_rescaled_source_comparison` (Convergence/ScalarRescaling),
  `exists_nonnegative_local_flow_with_end_comparison` (Limits/LocalEndComparison, unused so far),
  `exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence`
  (TracedTerminalCompactness:1574), `solution_not_rescaled_cone_limit` (Compactness/ConeExclusion).
  NormalizedSequence-tied (not reused): NormalizedEscapeLimit, NormalizedLimitNecks,
  NormalizedNeckSequence, NormalizedRescaledLimit, NormalizedLocalBackwardFlow,
  NormalizedEndCurvature, NormalizedConeExclusion (template only).
- Plan: F1 `Topology/BoundedCurvatureAtDistanceNecks.lean` (neck at a minimizing point from a
  spatial witness; limit ray with necks, Rm >= 0, completion point); F2
  `Topology/BoundedCurvatureAtDistanceCone.lean` (second-level local backward limit at the end
  points from the original sequence, comparison into the punctured end, cone exclusion); F3
  `Topology/BoundedCurvatureAtDistance.lean` (B3c assembly + headline).
- Statement notes (to be confirmed): (a) and (c) are not needed (L1's window theta0/Q_i suffices
  for the second level since Q'' >= Q_i); Q_i -> infinity IS needed (Rm >= 0 on the whole first
  limit, required by the punctured-cone construction); witnesses only needed at the final slice.
- 03:53 progress: scratch F1 compiles (no sorry): `SpatialCanonicalWitness.nonempty_spatialNeck_of_minimizing_segment`
  (a point strictly inside a unit-speed minimizing segment whose ends have C2-lower/higher scalar
  curvature is an alpha-neck centre, 13000^2 eps <= alpha; caps via the capTubeHasNeckChart neck
  recentred by -1/2 + SpatialMinimizer; whole-component alternatives excluded by scalar bounds),
  `ClosedSlab.nonempty_scaled_spatialNeck_of_minimizing_segment` (terminal-slice version in the
  normalized metric), `exists_isometric_ray_with_spatialNecks_of_scalar_escape` (L1's limit ->
  isometric ray to the missing point, R -> infinity along it, alpha-necks eventually along it),
  `metricRm04StandardAt_nonneg_of_normalized_terminal_pinching` (Rm >= 0 on the limit, Q -> inf).
  Lean note: `∀ {..}`/`let` inside long theorem types gave "unknown free variable" at the
  declaration; stating everything as theorem parameters fixed it.
- scratch F2a compiles: public copy of L1's private scaled-tests volume lemma
  (`RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests`) and
  `RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests`
  (the :671 supplier with per-index test radius sigma_n, sigma0 <= sigma_n sqrt Q_n). L1 should
  later drop its private copy and use this one (lead: L1 is uncommitted; no import cycle).
- next: F2 second level (local backward flow at the end points from the original sequence,
  comparison into the punctured end, `solution_not_rescaled_cone_limit`).
- 04:17 F2 second level: comparison (`exists_scalar_rescaled_source_comparison`), second-level
  scale Q2 = R(y), radius-1 buffer from the spatial witness at y (C2-bounded scalar on
  B(y, R(y)^{-1/2})), second-level limit via the scaled-tests supplier, the historical solution
  on V = B(base, 1/2) all elaborate; the single proof exceeded the default heartbeat budget,
  so it is being split (generic "local backward flow with comparison" lemma + assembly).
- 04:56 B3c PROVED in scratch (L1 + F1 + F2 + F3 concatenation compiles with no output):
  `RetainedCoreHistory.exists_normalized_scalar_bound_of_final_slab_window` (positive form of
  B3c: the normalized scalar is eventually bounded on every normalized ball). Hypotheses = L1's
  + Q_i -> infinity + q_i/Q_i -> 0 + spatial witnesses at the FINAL slice only +
  13000*(13000*eps) <= min (neckModelTolerance (1/4000000/26000)) (1/4000000/26000/64).
  (a) depth -> infinity and (c) sigma_i sqrt Q_i -> infinity are not needed. Next: headline,
  then splitting into the three repo files, lint, axioms.
- 05:18 DONE. Headline and B3c proved, no sorry. Files (new, not registered, no git writes):
  `Surgery/Topology/BoundedCurvatureAtDistanceNecks.lean` (451 lines),
  `Surgery/Topology/BoundedCurvatureAtDistanceCone.lean` (1125 lines),
  `Surgery/Topology/BoundedCurvatureAtDistance.lean` (290 lines).

## Result

Headline `RetainedCoreHistory.exists_scalar_bound_at_distance_of_final_slab_window`
(κ C1 C2) (hκ : 0 < κ) (Ctime Cgrad) (hphi : admissible phi) :
∃ εcone > 0, ∀ ε ≤ εcone, ∀ A > 0, ∃ Q Λ, 1 ≤ Q ∧ 1 ≤ Λ ∧ ∀ P₀ H hend t S hS y q ρ,
1 ≤ q → Λ q < R(y,t) → time last ≤ t − Λ/R(y,t) → (final-slice spatial witnesses at every
x with R(x,t) > q) → EventSlabsDerivative Ctime q last → S'.DerivativeBoundBefore Ctime q t →
S'.GradientBoundBefore Cgrad q t → EventSlabsPinched phi → PhiAlmostNonnegative S'.flow
(Ico (time last) t) phi → TerminalNoncollapsedBefore hend S' hS κ ρ t → Λ ≤ ρ √R(y,t) →
∀ z ∈ B_t(y, A/√R(y,t)), R(z,t) ≤ Q R(y,t)        (S' := S.restrictIncoming …).
Differences from the B3b log's form: witnesses are only required on the final slice t (weaker
hypothesis); 0 < ε is not assumed. εcone = min (neckModelTolerance (1/4000000/26000))
(1/4000000/26000/64) / 13000², independent of κ, C1, C2, Ctime, Cgrad, phi.

B3c (positive form) `RetainedCoreHistory.exists_normalized_scalar_bound_of_final_slab_window`:
L1's hypotheses + `Q_i → ∞` + `q_i/Q_i → 0` + final-slice witnesses +
`13000·(13000·ε) ≤ min (…)` ⇒ ∀ R > 0, ∃ B, eventually R_L(y)/Q_i ≤ B on the normalized ball
B(x_i, R). (a) and (c) of the logged B3c are not needed; `Q_i → ∞` is needed (Rm ≥ 0 on the
whole first limit, which `exists_punctured_cone_end_of_spatial_necks` requires). Depth: only L1's
fixed window θ₀ > 0 is used; the local limit flow at the end points lives on a normalized window
of length θ/2 with θ = min(θ₀, 1/(6(Ctime+1)C2)); the cone exclusion
(`solution_not_rescaled_cone_limit` → `solution_cone_terminal_exclusion`) needs any positive
depth, so normalized depth → ∞ is not required.

Route (as built): L1 → `exists_isometric_ray_with_spatialNecks_of_scalar_escape` (limit ray to
the missing point; necks along it from `SpatialCanonicalWitness.nonempty_spatialNeck_of_minimizing_segment`
on the minimizing segments + `nonempty_spatial_neck_at_limit_of_endpoint_blowup`) →
`metricRm04StandardAt_nonneg_of_normalized_terminal_pinching` → `exists_completion_endpoint_of_isometry`
→ `exists_punctured_cone_end_of_spatial_necks` (W, q_W, punctured cone, points x_n with
c ≤ R d² ≤ B) → `RetainedCoreHistory.final_slab_punctured_cone_end_exclusion` (second level:
`exists_scalar_rescaled_source_comparison`, witness-based radius-1 buffer at y_n = F(x_n) with
scale R(y_n), `exists_normalized_terminal_pointed_convergence_of_scaled_tests`, historical
solution on B(base, 1/2), pinching of the historical pullback,
`exists_nonnegative_local_flow_with_end_comparison`, `solution_not_rescaled_cone_limit`).

Compile: F1, F2 directly with `LEAN_NUM_THREADS=2 lake env lean -Dweak.linter.mathlibStandardSet=true`
(no output); F3 and the whole chain via a scratch concatenation L1+F1+F2+F3 (no output apart
from long-line warnings on scratch-renamed instance lines). Axioms (scratch): headline, B3c, the
exclusion, the local-flow lemmas, the ray lemma, the neck lemma all [propext, Classical.choice,
Quot.sound]; `#lint` 14 linters, 0 errors.

Lead notes: L1's private `normalized_inner_ball_volume_lower_bound_of_scaled_tests` is now
duplicated by the public `RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests`
(Cone file, which does not import L1); L1 can import the Cone file and drop its copy. The three
new modules still need registering in the root aggregate and a `lake build`.
