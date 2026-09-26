# SB13 — brick B13: fine-cut necks on short terminal slabs (history window), 2026-09-26

Worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf` @ 0798da941). Paths relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`.

## Progress
- start. Read AGENTS.md, DESIGN_S_FACTORY, logs SB14/SB12/B3D/B3E (B3F absent: the arbitrary-slice
  bounded-curvature bound is NOT delivered), `Contract/HornFineCutNecksLongSlab.lean`.
  Long-slab uses in B12: (i) BCD ball bound window `2Λb < R_L(x)(s − a)` (BCD's own final-slab
  window `time last ≤ t − Λ/R(y,t)`); (ii) strong-neck window `4θB ≤ R_L(x)(s − a)`.
- Read the suppliers: B5 `Topology/TracedRegionOrCapWindow.lean:546,665`, B2 `TracedRegion.lean:318,722`,
  H `HornNeckImprovement.lean:58,249`, `HighCurvatureModelBounds.lean:246` (`abstract_model_theorem`),
  `SelectedCountersequenceAdapter.lean:27,53` (`ClosedModelHypotheses`, `ModelRadiusWorksClosed`),
  the S contract `CanonicalNeighborhoodsThroughSurgeryStrong.lean:24,113`, the continuation leaves
  `CanonicalNeighborhoodContinuationLeaves.lean:20,146,188,232`, DESIGN_MAXWINDOW §0 (M1–M7), LEAD_NOTES.

## Verdict (no Lean written: every route to an unconditional B13 goes through an undelivered brick)

1. BLOCKER (B3e, DESIGN_MAXWINDOW M1). B5's dichotomy (`…_at_scale`, :665) is conditional on `hscal`:
   `R ≤ 2·Q·R(x)` along every backward trace from the ball `B(x, A/√R)` over the whole depth `T/R`.
   Nothing in the tree supplies `hscal` at a young point:
   - spatially at the slice `τ` it is bounded curvature at distance; the only headlines (B3d
     `BoundedCurvatureAtDistanceBoundedThreshold.lean:901`, B3e-constants
     `BoundedCurvatureAtDistanceConstants.lean`) keep the final-slab window
     `time last ≤ τ − Λ/R(x,τ)`, which is exactly the short-slab failure (B12 uses it at
     `HornFineCutNecksLongSlab.lean:140,174`, window `2Λb < R_L(x)(s − a)`); the purely spatial deep-horn
     ball is FALSE (SB9);
   - in time, the derivative clause gives depth `≤ 1/(2·Ctime·R)` only, while H needs depth `θ/R`
     with `θ = θ(δ, κ, ρ, Φ)` fixed before `Ctime` is known to it (S quantifies `∀ Ctime` before `ε`
     and H's `θ` does not see `Ctime`); depth `θ/R` needs the maximal-window bootstrap (M2–M5).
   The arbitrary-slice theorem (`OPUS_FILL_LOG_B3F.md`) does not exist; B3E only exposed `coneAccuracy`.
2. BLOCKER (H on the survivor flow). H goes through `abstract_model_theorem`, i.e.
   `ModelRadiusWorksClosed`, whose `ClosedModelHypotheses` require every slice COMPLETE and a whole-slice
   curvature bound on every compact time window. B2's survivor flow lives on the open ball
   `U = B(x, A/√R)` (`TracedRegion.lean:722`): incomplete. So H cannot be "rerun on the survivor flow";
   a local version needs the local ancient-limit machinery (B6a/B6b'/B6c-κ/B6d + maximal depth), i.e.
   the Crossing X-core itself (LEAD_NOTES 10:45Z: "young unscathed points share the Crossing X-core").
3. Consuming the Crossing leaf does not help either: `CrossingContinuation`
   (`CanonicalNeighborhoodContinuationLeaves.lean:232`) outputs `CanonicalBoundsOn`, whose witness clause is
   age-gated (`τmin ≤ R·(t − a)`, :25); at the young horn points of a short slab it yields only the
   derivative and gradient bounds. `τmin` is `∀` in S, so S's own witness clause is unusable as well.
4. FALSE as briefed: "(2) the cap-window alternative is impossible for deep horn points by
   `qcan ≤ Cbirth·scale` and `Kfine·max(Λ/r², max qcan 1) ≤ Q`". Those give a LOWER bound on the record
   scale only; an earlier event cut at scale `≈ Q` (the class does not record the cut level) produces
   cap-window points with `R ≈ Q` at any depth. The exclusion is topological, not an inequality:
   (i) the ε-neck sphere of the horn through `x` and the neck sphere of the cap's standard model through
   `x` bound the same tip side; (ii) that side is contained in the cap window, where the terminal
   scalar is `≥ c·scale` (B5's `exists_scalar_lower_bound_of_cap_window_trace`, :31) and `≤ C·scale/(1−θcap)`
   (standard-solution upper bound transported to `L`: not in the tree); (iii) hence the side contains
   neither a core-frontier point (`R ≤ Λ/r² < c·scale` once `Kfine` is large) nor the singular end,
   contradicting the horn's end structure. (i) and the upper bound in (ii) are new bricks.
5. Not a blocker: the terminal normalization only needs SPATIAL necks at slices `τ → s`
   (`TerminalSpatialCanonicalAlternatives.lean:473`, `eventually_normalizedNeck_of_spatialNecks`). On a
   slab with `R(s − a) < 1` no `StrongNeck G.flow` can exist (`time_domain` needs `[τ − 1/R, τ] ⊆ [a,s)`),
   so B13 must deliver fine spatial necks at slices, not `StrongNeck G.flow`.

## Dependency of an unconditional B13
B3e (arbitrary-slice bounded curvature at distance, 2.5–5k) → maximal traced depth `T* = ∞` along
contradiction sequences of young horn points (DESIGN_MAXWINDOW §2–§4, X-core) → ancient κ-limit with two
arms ⇒ round cylinder (reuse `exists_windowed_tolerances_for_original_arm_cylinder_limit`'s limit step on
the local approximants) ⇒ fine spatial necks at slices ⇒ `eventually_normalizedNeck_of_spatialNecks`;
plus the cap-window exclusion (4). This is the Crossing X-core applied to horn points; it should be
built once, in the Crossing lane, with a horn-point consumer, not duplicated here.
No files written, no compile, no git writes.
