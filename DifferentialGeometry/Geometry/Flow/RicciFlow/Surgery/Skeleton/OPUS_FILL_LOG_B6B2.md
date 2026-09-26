# B6b' — survivor maps, early-time κ tests and the solution property of the B6b limit (2026-09-26)

- Start. Read review F item 3 (coordinator), OPUS_FILL_LOG_B6C.md, OPUS_FILL_LOG_B8.md, my B6b file
  (committed a161fc07e, oleans present), `Geometry/Measure/LocalIsometry.lean:37`,
  `Geometry/Metric/Distance/LocalPullCompactness.lean:95`, `CrossingRoom.lean` (crossing clause).
- Consumer shapes quoted:
  - B6C log (B6c-κ target): "a history-side input `hnc : ∀ k, ∀ᶠ n, ∀ t ∈ [−(k+1), 0], ∀ z : W k n,
    ∀ ρ, 0 < ρ → ρ ≤ radii n → Icc (t − ρ²) t ⊆ Icc (−(k+2)) 0 → IsCompact (riemannianClosedBallOf
    (h k n t) z ρ) → (∀ s ∈ Icc (t − ρ²) t, ∀ y ∈ riemannianBallOf (h k n t) z ρ, ρ⁴ |Rm(h k n s)|²(y)
    ≤ 1) → ofReal (κ ρ³) ≤ vol_{h k n t}(riemannianBallOf (h k n t) z ρ)` with `radii → ∞`".
  - B8 log: "(a) `IsSolutionOn` of `{h k n}` on `closed (−(k+2)) 0` (B6b has it internally, input
    `hsol` of B6a — export it)".
- Matched: radii n := ρ·√Rₙ (→ ∞ since Rₙ → ∞); `|Rm|²` written `curvDerivNormSq 0`; volume
  `riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)` (SigmaCompact/Borel instances on `Opens`
  are file-local; both are Props / `borel`, so any consumer instance agrees).
- Hypothesis change: the time-tₙ volume test `hvol` is replaced by the history noncollapsing at all
  times `v ≤ tₙ` (`hnc`), which is `RetainedCoreHistory.NoncollapsedBefore κ ρ tₙ` unfolded
  (`fun n v p r hv hr hb => hNC n v p r hv hr hb`); the old `hvol` is its `v = tₙ` instance.
- DONE. File `Surgery/Topology/TracedRegionAncientLimitData.lean` (~555 lines), in-repo read-only
  compile `LEAN_NUM_THREADS=2 lake env lean <file>`: no output. Scratch copy with
  `linter.mathlibStandardSet` + `#lint`: 0 errors on 11 declarations (14 linters); axioms of the
  headline: propext, Classical.choice, Quot.sound. Name unique library-wide. Not registered in the
  root aggregate. Private helpers of B6b reused via `open private … from …TracedRegionAncientLimit`.
- Headline `ObservedHistory.exists_ancient_pointed_flow_limit_with_survivor_maps_of_isTracedRegion`:
  same hypotheses as B6b with `hnc`; conclusion = B6b's with, for every k, eventually in n:
  (i) `W k n` = normalized ball of radius k+3; (ii) `IsSolutionOn {h k n}` on
  `closed (−(k+2)) 0`; (iii) current-slab identity; (iv) `∃ a ≤ tₙ, a = tₙ − 2(k+2)/Rₙ, ∃ f hf`,
  every `f j : W k n → stage j` (j in `[activeStage a, activeStage tₙ]`) an INJECTIVE local
  diffeomorphism, regular crossings, `f last = val`, and `h k n s = Rₙ·localPullMetric
  (stageMetric j (tₙ + s/Rₙ)) (f j)` for every `s ∈ [−2(k+2), 0]` and every j whose stage domain
  contains `tₙ + s/Rₙ`; (v) the B6c-κ volume tests above, with `κ` the history constant.
- Proof of (v): pulled-back ball `B(z, r/√R)` has compact closure, so for `r'' < r/√R` its image
  under `f j` is the history ball (`image_riemannianBallOf_localPullMetric`) and has the same
  volume (`riemannianVolumeMeasure_image_eq_of_injective_local_isometry`); the history ball is
  parabolically Rm-controlled at radius r'' (traces = the survivor maps; slab clause from the
  curvature hypothesis through `curvDerivNormSq_scaleMetric`/`curvDerivNormSq_localPullMetric`;
  crossing clause via `RegularCrossing.rmNormSq_eq` at `T_{i+1}`), so `hnc` applies; then
  `r'' ↑ r/√R` (`le_of_tendsto`) and the scaling iff `riemannianVolumeMeasure_ball_ge_scaleMetric_iff`.
- Note: the B6b headline in `TracedRegionAncientLimit.lean` is now a strict weakening (up to the
  `hvol`/`hnc` hypothesis form); the lead may drop it or derive it later.
