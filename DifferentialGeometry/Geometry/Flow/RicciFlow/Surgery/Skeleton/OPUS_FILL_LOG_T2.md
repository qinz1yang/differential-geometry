# OPUS_FILL_LOG_T2 (DESIGN_B13 brick T2: terminal cap side from a frequent cap window)

Worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf`). Paths relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`.

## 2026-09-26 entry 1 (start, statement check)

Read AGENTS.md (pc3: no header, no module docstring, no comments), DESIGN_B13 §0 F4/F5, §2 T2, §3,
review H12 digest. `OPUS_FILL_LOG_T1.md` not present yet; T1's frozen statement is in DESIGN_B13 §2
and in `Surgery/Topology/TerminalCapSideExclusion.lean` (sorry body, T1 lane). T1 consumes
`frontier W = N.chart '' {z | z.val.2 = 0}` with `N` from
`SpatialNeck.exists_normalizedNeck_of_two_mul_le` (chart = `nk.map`), so T2's
`frontier W = range (fun y => nk.map (y, 0))` is the right output shape.

Compile method: scratch module `T2S.<Base>` under the scratchpad (`t2/lc.sh`), uncommitted imports
rewritten (registry `t2/mods.txt`), `LEAN_NUM_THREADS=2`, `-DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true -Dlinter.style.longLine=false -Dlinter.style.header=false`.
Nothing written under `.lake` / `E:`.

Statement probe: §2 T2 elaborated verbatim (opens as in `UniformDebitSurgeryStepOfFactory.lean`,
with the private `SigmaCompactSpace G.terminalRegularOpen` instance); only `declaration uses sorry`.

H12 "gap" row (`p₀.recenterConstant * δbound ≤ 1/2`): §2 T2 takes the two birth-scale facts
`∀ j b, qcan ≤ Cbirth * scale` and `∀ j b, 1 ≤ a₀ * scale` directly as hypotheses, so T2 never
calls the birth-scale lemma and does not need the conjunct (adding it would be an unused binder).
The conjunct belongs to T4, which derives those two facts
(`IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale`, whose `hΛδ` is that conjunct).
No deviation in T2.

## Plan (four steps, suppliers)

Fix `k := Fin.last`, `a := H.time k`, `Gk := G`. Bridge:
`RetainedCoreHistory.exists_standard_comparison_of_cap_window_trace`
(`Surgery/Topology/CapWindowStandardComparison.lean:20`) at `(Θ, Ctime)`, window radius
`D := D₁ + alpha⁻¹ + 1`, accuracy `ε := e` (window comparison), `η := eta_low`
(`exists_uniform_standard_metric_scalar_lower_comparison`), order `N := ⌈(2 alpha)⁻¹⌉₊`.
Outputs `(R, m₀, ζ₀, δ₀)` are T2's `(Rrad, m₀, ζ₀, δ₀)`; `Cbirth` is the bridge's; `c := c₀/2`
(`exists_standard_scalar_lower_bound`), `Cup := max Creset c`. `alpha := eps / (2 (eps + 2))`
(so `2 alpha < eps`, `eps⁻¹ + 1 ≤ (2 alpha)⁻¹`).

- **T2a (pigeonhole).** `∃ᶠ τ, CapWindowPoint` ⇒ one `(j, b)` frequently (finite
  `Σ j, RetainedBoundaryIndex j`, `Filter.eventually_all`), one instance `(hl, A, xw)`, and in the
  limit `s − t_{j+1} ≤ θcap / scale`. Hence the bridge applies at EVERY `t ∈ (a, s)`.
- **T2b (window in the terminal regular region, scalar bounds).** At each `t`, the bridge gives
  `Ξ_t`, and `window_metric_eq_localPullMetric_scaleMetric` (`CapWindowFlowPushforward.lean:223`)
  gives `S τ_t = localPull (q · g(t)) ι_t`, `ι_t := val ∘ val ∘ Ξ_t`. `ι_t = ι_{t₀}` by
  `BackwardPointTrace.endpoint_eq_of_point_first_eq` (record window anchoring). Scalar:
  `q c₀/2 ≤ R(t, ι v) ≤ q Creset` on the whole window (lower comparison + bridge `|S.scalar| ≤
  Creset`). Regularity: `exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels`
  (`TerminalCanonicalCapture.lean:18`) with `A := q Creset`, derivative bound = the S clause,
  pinching from `exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen`. Limit bounds on
  `L` by `TerminalLimitMetric.tendsto_metricScalarAt`.
- **T2c (neck).** New general lemma `SpatialNeck.exists_uniform_transport_trans_of_rm_bound`
  (uniform tolerance, keeps the map). New standard lemma: a window metric `e`-close to `Q(T)`,
  `T ∈ [0, Θ]`, carries a `2 alpha`-neck at `x₁` (`‖x₁‖ = D₁ ≥ Dfar`) whose central sphere is
  `D₁ · rot(S²)`: `StandardSolution.exists_far_radial_spatialNeck` (`StandardFarRegion.lean:400`) +
  `exists_window_metricComparisonOn_of_lt` (C4B1, uncommitted) + the uniform transport. Push to
  `g(t)` along `ι_t` (`SpatialNeck.pushforward`, `SpatialNeck.scaleMetric q⁻¹`); then
  `TerminalLimitMetric.eventually_spatialNeck_of_incoming_spatialNecks`
  (`TerminalSpatialCanonicalAlternatives.lean:544`) gives the `eps`-neck of `L` with the same
  central sphere.
- **T2d (W).** `W := ι'(ball D₁)`; open (open map), connected, `closure W = ι'(closed ball)`
  compact, `frontier W = ι'(sphere D₁) = range (nk.map (·, 0))`. No Jordan–Brouwer.

## Lemma 1 (done): uniform neck transport keeping the map

`Perelman/CanonicalNeighborhood/SpatialNeckUniformTransport.lean` (new):
`FiniteHorn.SpatialNeck.exists_uniform_transport_trans_of_rm_bound`. `delta` depends only on
`(alpha, r₀, K)` (`r₀ ≤ R(p)`, `|Rm|(p) ≤ K`); conclusion `∃ nk', nk'.map = nk.map.trans F`.
Compiles clean (standard linter set).
Deferred merge: the committed `SpatialNeck.exists_uniform_transport_tolerance`
(`Surgery/Topology/AncientPointedFlowLimitTransfer.lean:515`, `r₀ ≤ R ≤ r₁`, scalar closeness as a
hypothesis, `Nonempty` output) and C4B2's uncommitted same-named lemma
(`SpatialCanonicalWitnessUniformTransport.lean:85`, NAME CLASH with the committed one) are
siblings; neither exposes the map with an intrinsic `Rm` bound, so a new name was used.
