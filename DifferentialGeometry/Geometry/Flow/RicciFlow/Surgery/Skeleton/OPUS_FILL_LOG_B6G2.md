# B6g2 — DESIGN_B6D_GLUE bricks B4, B5, B6 (2026-09-26)

- Start. Read AGENTS.md (pc3), DESIGN_B6D_GLUE.md (whole), OPUS_FILL_LOG_B6G1.md, H7 digest.
  Method: in-repo `lake env lean` for files whose imports have oleans; otherwise scratch modules
  `B6G2.*` under `%TEMP%/claude/b6g2` (imports rewritten, `lean -R src -o olean/...`,
  LEAN_PATH = scratch oleans + lake path). Nothing under `.lake`, nothing staged, root aggregate
  untouched.
- Note: a concurrent `lake build` in pc3 (started 09:28 and 09:35) was rewriting oleans in my
  import closure; compiles that hit a missing olean were retried after it finished.

## B4 — lifting short paths through the pullback
- File `Geometry/Metric/Pullback/LocalDistance.lean`, namespace `DifferentialGeometry`.
- `exists_riemannianEDistOf_localPullMetric_eq_of_ball_subset_range`.
- Deviations: (1) name — §2's `riemannianEDistOf_localPull_lt_of_ball_subset_range` does not
  describe the conclusion (an existential with an equality); (2) generalized from `I3`/`ThreeSpace`
  to arbitrary models `I` (source, `[FiniteDimensional ℝ E]` needed by `localPullMetric`) and `J`
  (target), with only `[T2Space N]` (source) — the §2 instance is a specialization.
- Proof: `IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn` (source univ, target range f);
  `≤` by `edistOf_map_le_of_metric_upper_on_ball` for `Φ.symm` on a closed ball of radius strictly
  between `d(fz,p)` and `ρ`; `≥` by the same lemma for `Φ` when `d_pull(z,w) < ρ`, trivially otherwise.
  No compactness needed. Private helper: general-model inverse-derivative identity.
- In-repo compile: rc 0, no output.
- Axioms `[propext, Classical.choice, Quot.sound]`; `#lint` 0/2 (14 linters).

## B5 — F2 core — DONE
- File `Surgery/Topology/NeckAlternativesLocalPull.lean` (151 lines), namespace `FiniteHorn`,
  imports Transfer (uncommitted), B4, `CrossModelBallCapture`.
- `exists_neckAlternatives_localPull_of_metric_lower`: §2 statement except that the four
  `[SigmaCompactSpace M/N]` binders are DROPPED (unused; strictly more general, B6/B13 unaffected).
  `1 ≤ C` is kept as a hypothesis (H7 note: the caller clamps `C` to `max 1 C`; B6 gets it from
  `W.one_le_comparison_constant`).
- Proof as §1: `D` from `exists_spatialNeck_window_edist_le`; capture
  `ball_subset_image_of_metric_lower_crossModel` (Φ from `exists_partialDiffeomorph_of_injOn`) gives
  `ball_g(fz, r/L) ⊆ range f`; window extent `≤ (C + (D + 2ε⁻¹)√C)/√Q < r/L` (neck at `fz`: uses
  `√C ≥ 1`; neck at `w`: `√R(w) ≥ √Q/√C` and the triangle inequality); necks pulled back by
  `SpatialNeck.pushforward` along `Φ.symm` with `isometryOn_symm_of_isometryOn`; the partner
  point and its exact distance by B4; scalars by `metricScalarAt_localPull`; the component
  clause by `Continuous.image_connectedComponent_subset`.
- Scratch compile (B6G2.NeckAlt): no output. Axioms standard. `#lint` 0/1; standard linter set: no
  output.

## B6 — producer of B6d's `hW` — DONE
- File `Surgery/Topology/TracedRegionAncientLimitNeckAlternatives.lean` (97 lines), namespace
  `Surgery.Topology.ObservedHistory`, imports `TracedRegionAncientLimitData` (committed),
  `NeckAlternativesLocalPull` (B5), `Metric.PullbackScaling`. Does NOT import Witnesses (not
  needed); the window-membership fact of the private `mem_Icc_of_mem_window` is inlined.
- `exists_neckAlternatives_of_survivor_maps`: exactly the §2 statement (the three unused named
  hypotheses `hqs`, `hL`, `ha` are written `(_ : …)`, same type).
- Uses only κ-free stage witnesses at the time `v = t + s/R < t₀` (H7 decision: nothing at or
  after `t₀ n`). Proof: `j := activeStage v`; `h s = localPull (scaleMetric R stage_v) (f j)` by
  `hp` + `localPullMetric_scaleMetric`; `qs ≤ R·qW < R·R_{h s}(z) = R_stage(f j z)` gives the
  witness; `neckAlternatives_of_spatialCanonicalWitness` on `Wt.scaleMetric R hR`; B5 with
  `r := 1`, `C := max (2|C1|) C2 ≥ C2 ≥ 1`, `Q_pos` from the witness.
- Scratch compile (B6G2.SurvNeck): no output (43 s). Axioms standard. `#lint` 0/1; standard
  linter set: no output.

## Summary
- 3 new files, 336 lines, 3 public theorems (+1 private helper), names unique library-wide, no
  sorry/axiom/nolint/heartbeat options, no comments/docstrings, lines ≤ 100 (imports excepted).
- Not registered in `DifferentialGeometry.lean` (lane rule); register after Transfer:
  `Geometry.Metric.Pullback.LocalDistance`, `…Surgery.Topology.NeckAlternativesLocalPull`,
  `…Surgery.Topology.TracedRegionAncientLimitNeckAlternatives`.
- Scratch probes removed.
