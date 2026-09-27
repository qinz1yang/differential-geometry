# BS6 (lane BS6) — ball bound at a post-surgery stage start (2026-09-26)

- Read AGENTS.md, DESIGN_BASESLICE §0/§2/§3, H9 digest (route fixed), H8 digest, B3F log.
- Route decided (H9, no recentring), made concrete with existing public suppliers:
  * retained domain `U := backwardSurvivorDomain j.castSucc j.succ` (open), terminal map
    `backwardSurvivorTerminalMap` (local diffeo into `terminalRegularOpen`), metric identity
    `backwardSurvivorMap_metric_crossing`; its image lies in `range oldTerminal` (compact, `old_compact`).
  * `TerminalMetricConverges` (k = 0) on that compact image gives `g_σ ≤ (1+ε) gbar`; scalar closeness
    from `TerminalLimitMetric.eventually_scalar_close_on_compact`; `RegularCrossing.scalar_eq`.
  * distances: `riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset`,
    `edistOf_le_of_quad_of_localDiffeomorph`, `riemannianEDistOf_le_restrictOpen`.
  * first touch = minimiser of `d_a(y,·)` on the compact complement of `U`; the open ball of that radius
    lies in `U`, the minimiser lies in its closure (`closure_riemannianBallOf`, compact ⇒ complete).
  * capture at the touching point: copy of the private `exists_window_point_of_edist_le`
    (BackwardTraceDistortion) with the cap-scale lower bound `hscale`
    (`exists_presented_cap_scalar_lower_bound_of_canonical_window_core`).
  * `¬CWP` at σ in stage j.castSucc from `¬CWP(y, a)`: `BackwardPointTrace.append` + BS3-type slack.
- Compile method: scratch modules `BS6Scratch.*` under the scratchpad (`bs6/cc.sh`), B3F chain rebuilt there
  (the shared B3FScratch oleans were removed by another lane).
- Statement probe: BS6 §2 statement copied verbatim into the headline file (the scratch probe with a
  `sorry` body could not be elaborated at first because the shared `B3FScratch` oleans were deleted by
  another lane mid-run; the headline file itself now carries the verbatim statement).
- DONE (compiled clean, scratch): `Surgery/Topology/BoundedCurvatureAtDistanceAfterEventCapture.lean`
  * `OrientedThreeStage.exists_first_touch_of_not_subset` (first touch of the complement of an open set by a
    ball on a compact stage: minimiser, ball of that radius inside, minimiser in its closure);
  * `RetainedCoreHistory.not_regularCrossing_of_not_mem_backwardSurvivorDomain`,
    `capWindowPoint_at_event_of_not_regularCrossing` (retained centre, F3),
    `capWindowPoint_at_event_of_edist_le` (age-zero capture: non-retained point within `dd` of the centre,
    `R ≤ M` there, `2·TE + √(8M)·dd < Dcap` ⇒ CWP);
  * private copy of `exists_window_point_of_edist_le` (BackwardTraceDistortion, private) — DEFERRED MERGE.
- DONE (compiled clean, scratch): `Surgery/Topology/BoundedCurvatureAtDistanceAfterEventPullback.lean`
  * `ObservedHistory.eventually_backwardSurvivor_scalar_close_and_edist_le`: for σ ↑ time j.succ, on the
    retained domain, `|R_σ(Φx) − R_a(x)| < δ` and `d_σ(Φx, Φz) ≤ √2 · d_{g_a|U}(x, z)` (compact convergence on
    `range oldTerminal`, `RegularCrossing.scalar_eq`, `backwardSurvivorMap_metric_crossing`).
- DONE (compiled clean, scratch, standard linter set on, zero output):
  `Surgery/Topology/BoundedCurvatureAtDistanceAfterEvent.lean`:
  `RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_after_event`, statement
  VERBATIM §2 BS6 (checked by whitespace-normalised string comparison with DESIGN_BASESLICE.md), no
  extra hypotheses, no `sorry`.
  Constants (in this order): B3e event at `(4A, 2Cq, θ/2)` gives `QB, ΛB, DB, RB, ζB`; `Kc := 2QB+1`;
  `Dcap := max DB (2·TE + √(8Kc)·√e·A) + 1`; `Rrad := max RB Dcap`; `ζ₀ := min ζB (min 1/2 ε₀(Dcap))`;
  `Q := 2QB+2`; `Λ := 4ΛB`.
  Proof: (1) `y` retained, else CWP at age 0; (2) σ ↑ a chosen for this history with
  `σ > max (a_{j}, a/2, a − θ/(2S))` and the pull-back comparison at tolerance `R/8`; B3e at σ at the
  preimage `y₀` (¬CWP at σ by `append` + BS3 `of_le_time` + `mono`); (3) any ball `B_a(y,d) ⊆ U`, `d ≤ √e·A/√R`,
  has `R_a ≤ Kc·R`; (4) first touch of `Uᶜ` by `B_a(y, √e·A/√R)` has `R_a ≤ Kc·R` by closure, so the
  age-zero capture gives CWP(y, a, Dcap, θ): contradiction, the whole ball is retained; (5) `B_t ⊆ B_a` by
  `g_a ≤ e·g_t`, and `R_t ≤ R_a + R/4`.
- Axioms (`#print axioms` in a scratch probe, removed): headline, first-touch, pull-back comparison and
  capture lemma all depend on `[propext, Classical.choice, Quot.sound]` only.
- Line counts: AfterEvent 266, AfterEventCapture 233, AfterEventPullback 92 (591 total).
- Deviations: none in the statement. Route = H9 digest (no recentring); the "path first touch" is realised as
  the distance minimiser on the compact non-retained set plus `closure_riemannianBallOf`.
- Deferred merges / notes for the lead:
  * private copy of `exists_window_point_of_edist_le` (BackwardTraceDistortion.lean, private) in
    AfterEventCapture — merge by making the original public.
  * `OrientedThreeStage.exists_first_touch_of_not_subset` is general metric geometry; natural home would be
    Geometry/Metric/Distance, but `closure_riemannianBallOf` lives in Perelman/CanonicalNeighborhood/
    WitnessClosedBallJets (import direction), so it stays in Surgery/Topology for now.
  * files follow this directory's convention (no copyright header / module docstring), like the other
    Surgery/Topology files; add headers when the directory is normalised.
  * new modules are NOT registered in `DifferentialGeometry.lean` (per instructions). Imports:
    BoundedCurvatureAtDistanceSliceEvent + CapWindowPointTimeSlack (both uncommitted) + the two new files.
