# B5 — traced region or cap-window point, with capture age (2026-09-26)

- 03:15 Read AGENTS.md, NAMING §2–6, Skeleton/README, DESIGN_CROSSING (F2, B4, B5, B7), X2
  (`BackwardTraceDistortion.lean`), X2b, B2 (`TracedRegion.lean`), B4
  (`TracedRegionBackwardStep.lean`), `CapWindowPoint`, `CapWindowStandardComparison.lean:20`,
  `CapWindowDerivativeTransfer.lean:68` (template for the standard scalar lower bound),
  `StandardTerminalBlowup.lean:61`.
- Finding (plan): X2's capture needs `Ctime·M·(t−u) ≤ 1/2` (derivative bounds give the curvature
  along traces), so at depth `T/R` with `Ctime·Q·T > 1/2` it does not apply. B5 therefore takes the
  B7 output as hypothesis: scalar `≤ 2M` along every (partial) backward trace of every ball point on
  `[u, t]` (traces are unique, `BackwardPointTrace.point_unique`). Pieces: (a) capture with that
  hypothesis (X2's proof, private lemmas via `open private`), (b) standard scalar lower bound with
  the `1/(1−τ)` factor at a cap-window trace, (c) the age bound by contradiction at an intermediate
  non-event time, (d) the dichotomy.
- Finding: `Cbirth` of `exists_standard_comparison_of_cap_window_trace` is Θ- and C-independent in
  its proof (`WindowPersistence.lean:713`, from
  `exists_uniform_window_image_scalar_bound_of_scaled_pullback`), but the published statement
  quantifies it after Θ; B5 inherits `∃ Cbirth` after Θ = Θ(T,Q).
- 03:22 Compile method: TracedRegion/TracedRegionBackwardStep have no oleans yet, so scratch file
  outside the repo = those two bodies + mine, `LEAN_NUM_THREADS=2 lake env lean`. Pieces (a)
  `exists_cap_capture_of_ball_point_without_trace_of_scalar_le` and (b)
  `exists_scalar_lower_bound_of_cap_window_trace` compile clean.
- 03:32 DONE. New file `Surgery/Topology/TracedRegionOrCapWindow.lean` (736 lines, imports
  TracedRegion, TracedRegionBackwardStep, BackwardTraceDistortion, CapWindowDerivativeBounds,
  CanonicalCapScalar; X2's private lemmas via `open private … from …BackwardTraceDistortion`, as X2b
  does). Not registered in the root aggregate (TracedRegion/B4 are not registered either).
  Verification: scratch concatenation (TracedRegion + TracedRegionBackwardStep bodies + this file)
  outside the repo, `LEAN_NUM_THREADS=2 lake env lean`: 0 errors, 0 warnings. `#print axioms` of the
  five public theorems: propext, Classical.choice, Quot.sound. `#lint` (14 linters): only docBlame
  on B2's three defs (excluded linter); nothing on this file. Scratch removed.
- Public theorems (ns `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory`):
  1. `exists_scalar_lower_bound_of_cap_window_trace`: `∃ c>0, ∀ Θ∈(0,1), ∀ C, ∃ Cbirth, ∀ D>0, ∃ R m₀
     ζ₀ δ₀, ∀ …(same hypotheses as exists_standard_comparison_of_cap_window_trace)…,
     c·q ≤ (1 − q(t − T_j))·Gk.flow.scalar t y` (q = cap scale; c = c_std/2 from
     `exists_standard_scalar_lower_bound`).
  2. `exists_capWindow_age_bound_of_scalar_le_along_trace`: same constant block; history-level
     `u ≤ t`, derivative data (`EventSlabsDerivative C qcan (activeStage t)`, current-slab and
     final-slab `DerivativeBoundBefore C qcan t`), a cap-window trace `A` of `y` from `j.succ`
     (`‖x‖ < D+1`, `qcan ≤ Cbirth·q`, `1 ≤ a₀·q`, `u ≤ T_j`), `0 < θcap < Θ`, scalar `≤ M` along
     `A` on `[T_j, t]`, and `M·(t−u)·(1−θcap) ≤ c·θcap` ⟹ `t − T_j ≤ θcap·q⁻¹`. Proof: otherwise
     pick τ ∈ (θcap, min(q(t−T_j), Θ)) with `T_j + τ/q` not an event time; the standard comparison
     at that time (event slab or final slab) gives `c·q ≤ (1−τ)·M`, and `q(t−u) ≥ τ` contradicts.
  3. `exists_cap_capture_of_ball_point_without_trace_of_scalar_le` (X2's capture with the
     derivative route replaced by the hypothesis below; any stage, `hlast` for the final slab):
     conclusion as X2 plus `scale ≤ 4M` and `u ≤ T_j` (instead of X2's age product).
  4. `exists_isTracedRegion_or_capWindowPoint_of_scalar_le_along_traces` (general form, bound
     `8√3(1+φ1+φ0)·M`, depth `t−u`, window `2·TE + √(8M)·exp(9·8√3(1+φ1+φ0)·M·(t−u))·ρ < Dcap`,
     age `2M(t−u)(1−θcap) ≤ c·θcap`; `hscale` derived from
     `exists_presented_cap_scalar_lower_bound_of_canonical_window_core`, hence `TE < Dstar`).
  5. `exists_isTracedRegion_or_capWindowPoint_at_scale` (DESIGN B5 shape): with `u = t − T/R`,
     `ρ = A/√R`, `M = Q·R` (`1 ≤ Q·R`), `D(A,T,Q) := 2·TE + √(8Q)·exp(9·8√3(1+φ1+φ0)·Q·T)·A <
     Dcap ≤ Dstar`, `1 − c/(8TQ) ≤ θcap`, `1/4 ≤ θcap < Θ`:
     `isTracedRegion t y (A/√R) (T/R) (8√3(1+φ1+φ0)·(Q·R)) ∨ CapWindowPoint records (activeStage t)
     y t Dcap θcap`.
- The hypothesis B5 consumes (B7 must produce exactly this; it replaces DESIGN's `hQ` + `hball`):
  `∀ x ∈ B_t(y, A/√R), ∀ w (u ≤ w) (hwt : w ≤ t) (B : BackwardPointTrace (activeStage w)
  (activeStage t) _ x) v (w ≤ v) (v ≤ t), metricScalarAt (stageMetric (activeStage v) v)
  (B.point (activeStage v) _ _) ≤ 2·(Q·R)` (traces are unique, `point_unique`, so "every trace" is
  "the trace"). B7 (depth induction through the partial limit) is NOT included: it needs B6c's
  finite-horizon limit bound to re-anchor B4 at each step (B4 turns `≤ QR₀` above `u` into `≤ 2QR₀`
  on `[u − Δ, u]`, so plain iteration doubles each step); far over 300 lines.
- Findings for the lead: (i) Θ must satisfy `1 − c/(8TQ) ≤ θcap < Θ < 1`, so Θ, hence the
  published `Cbirth`, `Rrad`, `m₀`, `ζ₀`, `δ₀`, depend on (T, Q); along the sequence this is the
  `n ≥ n₀(A,T)` choice, but `hbirth : qcan ≤ Cbirth·scale` must be supplied for Cbirth(Θ). The
  proof's Cbirth is Θ- and C-independent (`WindowPersistence.lean:713`); exposing it needs an edit
  of `exists_standard_comparison_of_cap_window_trace` (not done, out of lane). (ii) Terminal slab:
  apply 5 to `H.extendHorizon T … (G.closedPrefix T …)` with B2's `eventSlabsPinched_extendHorizon`,
  `extendHorizon_finalSlab_phiAlmostNonnegative`, `extendHorizon_finalSlab_derivativeBoundBefore`,
  `eventSlabsDerivative_extendHorizon`; the records/InFixedHamiltonIvey data and `CapWindowPoint` of
  the extended history must be transported back by the consumer (not done here).
