# OPUS fill log XA4 — bricks X3 (X3p, F3, X3a, X3) and X4ext of DESIGN_CROSSING_ASSEMBLY.md

Worker: Opus 5.5, worktree D:\differential-geometry-pc3 (codex/pc-target-c-psf, HEAD e68bf6466), started 2026-09-26.
Scratch: C:\Users\liao9\AppData\Local\Temp\claude\D--differential-geometry-moise-int\08693914-694c-4a5b-8767-edd7f4799e4d\scratchpad\xa4
(sync.sh copies uncommitted suppliers as XA4Scratch.<Name>; s.ps1 compiles one module read-only).

## Status
- started: read DCA §0/§2/§3, DESIGN_X4D §1.6/§1.7/§2, DESIGN_MAXWINDOW §3–4, logs XA1/XA2/XP1/XP2.
- Suppliers consumed (uncommitted, via scratch): X0 `InitialWindowScalarBound`, X1k `RetainedCoreHistoryExtendAt`,
  X2 `NestedSubsequence` + `TracedRegionMaximalDepth`, P1s `CrossingPersistenceInputs`.
- Lead message (mid-task): W1′ is owned by lane XP3 (`OPUS_FILL_LOG_XP3.md`); X3a must consume XP3's file, not copy.

## Shared B5-in-Σ lemma (new file `Surgery/Topology/CrossingTracedRegion.lean`)
- `RetainedCoreHistory.derivativeBound_inputs_extendAt`: the three derivative inputs (`hslabs`, `hcurrent`,
  `hfinal`) of B5 / the B7 step / the backward step for `K = H.extendAt …` at `extendAtTime`, at constants
  `(2 Ctime, 2 q)` from `EventSlabsDerivative Ctime q last` and `G.DerivativeBoundBefore (2Ctime) (2q) t`.
- `RetainedCoreHistory.exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces`: for fixed `A T Q`,
  `∃ K₀ ≥ 0, ∀ᶠ n`, a scalar bound `2QRₙ` along all backward traces reaching `tₙ − T/Rₙ` in `Kₙ` makes the
  normalized ball a traced region of `Kₙ` at depth `T/Rₙ`, bound `K₀Rₙ` (`K₀ = 8√3(1+φ1+φ0)Q`).
  Route: B5 (`TracedRegionOrCapWindow.lean:665`) at `C = 2Ctime`, threshold `2qcan`, `θ₁ = max(1/4, 1−c/(8TQ))`,
  `Θ = (θ₁+1)/2`, `Dcap = window width + 1`; records of `Kₙ` from X1k's `capWindowPoint_extendHorizon_iff`;
  `a₀`, `δb ≤ δ₀`, radius/order/accuracy, `qcan ≤ Cbirth·λ`, `1 ≤ a₀λ` from P1s (called with `t₀ := time last`,
  derivative clause vacuous). Right branch: CWP at `(Dcap, θ₁)` transported by the iff, then monotone to
  `(Dₙ, θcapₙ)` eventually — contradicts the bad-point clause.
  Hypotheses are the Σ fields it uses (minimal binders; `hderG` is `hsliver`'s derivative clause moved to `tₙ`).
- Compile: clean (standard linter set), 49–59 s.

## X4ext (new file `Surgery/Topology/CrossingDepthExtension.lean`)
- `depthExtendable_add_of_windowAnchorBound`: DCA §2.7 statement; the anchor hypothesis is X4's conclusion
  along `σ` verbatim (ψ absorbed into σ). Binders: the Σ fields used (as in the shared lemma) plus
  `hRt : Tendsto (Rₙ·tₙ) atTop atTop` (X0's `tendsto_scalar_mul_time_atTop_of_inCutoffClass`), needed to place
  `tₙ − T/Rₙ` in `[0, tₙ]` for the new depth `T > T*`.
- Route (MAXWINDOW §4.3): `Δ = 1/(8(Ctime+1)(M+1))`, `T' = max(T* − Δ/2, T*/2)`, target `T* + Δ/4`
  (= the stated `T* + 1/(32(Ctime+1)(M+1))`). For `v ≥ tₙ − T'/Rₙ`: trace uniqueness
  (`BackwardPointTrace.point_unique` on the `restrictFirst`s) + traced region at `T'` + `scalar_abs_le_rm`
  give `R ≤ 9K₁Rₙ`. For `v < tₙ − T'/Rₙ`: anchor `≤ MRₙ`, backward step
  (`TracedRegionBackwardStep.lean:121`) with `M' = 2(M+1)Rₙ`, constants `(2Ctime, 2qcan)`, `htime` from
  `4Ctime(M+1)·(3Δ/4) ≤ 1/2`, gives `≤ 4(M+1)Rₙ`. Then the shared lemma with `Q = 9K₁ + 4(M+1)`.
- Compile: clean (standard linter set), 69–79 s. Axioms (probe, deleted): all three declarations above
  `[propext, Classical.choice, Quot.sound]`.

## X3p + F3 (new file `Surgery/Topology/CrossingBaseSliceBound.lean`)
- Σ block (DCA:258–305) reproduced as a `variable` block (without `hεfar`, whose `windowFarAccuracy` does not
  exist yet and which none of my theorems uses); each theorem `include … in` only the fields it uses
  (no unusedSectionVars). All statements are therefore verbatim DCA §2.5 inside Σ.
- `RetainedCoreHistory.tendsto_scalar_at_bad_point_atTop` (helper: `Rₙ → ∞` from `hq`, `hbad`).
- F3 `RetainedCoreHistory.tendsto_scalar_mul_time_atTop` (`Rₙ t₀ₙ → ∞`): X0's
  `tendsto_scalar_mul_earlier_time_atTop_of_inCutoffClass` with `C = 1` (`Rₙ(tₙ − t₀ₙ) ≤ Rₙηₙ ≤ 1/(n+1)`).
- X3p `RetainedCoreHistory.eventually_scalar_le_on_normalized_ball_at_base` (verbatim): per-`n` dispatch
  `t₀ₙ > aₙ` → BS5-terminal (`BoundedCurvatureAtDistanceSliver.lean:69`), `t₀ₙ = aₙ` → BS6
  (`…AfterEvent.lean:45`, `j.succ = last` from `eventCount ≠ 0`, which holds since `Rₙt₀ₙ ≥ Λ > 0`;
  the stage index is moved by a local `∀ k, j.succ = k → …` + `subst`). Both at `Cq = Cs`, `q = qsₙ`,
  `ρ = ε`, `θ = 1/2`; `Q = max Q₁ Q₂`. ¬CWP at `t₀` from `hbad` via `CapWindowPoint.of_le_time` with
  `S = (1/(n+2))/ηₙ` (from `hsliver`'s scale clause) and slack `1/(n+2)`, then `mono` to `(Dₙ, θcapₙ)`
  for `n ≥ 2`. Derivative/gradient thresholds relaxed `qcan → qs` by two private one-liners.
- Compile: clean (standard linter set), 70 s.

## Before-`t₀` data of `Kₙ = extendAt` in ObservedHistory form (new file
`Surgery/Topology/RetainedCoreHistoryExtendAtBefore.lean`; needed by X3a (W1′/B6 inputs) AND by X7 for X5)
- `RetainedCoreHistory.stageMetric_activeStage_extendHorizon_eq`: two horizon extensions of `H` whose final
  slabs agree on `[a, min T₁ T₂]` have equal slice metrics below `min T₁ T₂`.
- `…isParabolicallyRmControlledBall_extendHorizon_of_agree` (ball transport between such extensions) and
  `…isParabolicallyRmControlledBall_of_extendHorizon` (reverse of `HistoryHorizonExtension.lean:387`).
- `volume_ge_extendAt_of_terminalNoncollapsedBefore`: X5/W1′'s `hnc` (`v < t₀`, `r ≤ ρ`, parabolic ball in
  `extendAt t` ⇒ `κ r³` volume) from `H.NoncollapsedBefore κ ρ a` (Σ `hslabs`) for `v ≤ a` and
  `TerminalNoncollapsedBefore … t₀` (Σ `hbefore`) through `extendAt v` for `v > a`.
- `exists_spatialCanonicalWitness_extendAt_of_before`: X5/B6's `hwit` from `EventSlabsSpatiallyCanonical` +
  `SpatiallyCanonicalBefore t₀` (point typed in `stage (activeStage v)`, defeq to `stageAt v`).
- `curvatureOperatorLowerBoundAt_extendAt_of_pinched`: W1′/X5's `hpinch` from `EventSlabsPinched` +
  `PhiAlmostNonnegative` (all `v`, not only `v ≤ t`).
- Compile: clean (standard linter set), 61 s.

## X3a + X3 (new files `Surgery/Topology/LocalFlowLimitShiftedConvergence.lean`, `Surgery/Topology/CrossingTimeZeroBound.lean`) — in progress
- W1′ consumed from XP3 (`TracedRegionLocalLimitDepthSchedule.lean`, `Compactness/Limits/LocalPointedFlowLimit.lean`,
  both compile clean in my scratch chain); no copy of W1′.
- `FiniteHorn.tendsto_metricDerivNormSupOn_localPull_shifted_to_zero_of_time_lipschitz` (new, generic): the
  "per-radius B9 copy" of the design reduced to its only non-generic input — ShiftedTransfer:205 with the
  global-flow convergence replaced by time-0 convergence to `P.metric` plus W1′'s windowed Lipschitz clause
  (proof copied from :205 with `s = 0`; uses the private `metricDerivNorm_localPullMetric_of_injective` by
  `open private`). With it, B9 (`ShiftedTransfer:354`) itself is INSTANTIATED (no copy) with `G := const P.metric`,
  `σ s := σ₀` (one shifted sequence `σ₀ → 0⁻` avoiding event times and `[t₀, t]`), `E n := {σ₀ n}ᶜ`; its `hW` is
  B6 (`exists_neckAlternatives_of_survivor_maps`) at `s = σ₀ n` exactly as in B13.
- `Rm ≥ 0` at `P.metric`: Curvature:26 instantiated with `G := const P.metric`, `h' k n _ := h k n 0`.
- Whole-slice bound: Transfer:440 on `(P.M, P.metric)`; pull-back to the approximant balls by
  `eventually_ball_subset_image_closed_ball` (BallImage:160) + `pointedScalar_uniform_on_compact_of_canonical_domains`.
- DEVIATION (needed hypothesis, not in Σ): `hεX : ε ≤ crossingNeckAccuracy` where
  `crossingNeckAccuracy := neckModelTolerance (min (η₀/2) (1/44))`, `η₀ := (Transfer:440).choose` (a `def`, like
  `coneAccuracy`): the approximant necks come at accuracy `ε` and must be at most B9/Transfer:440's tolerance.
  B11/X5's `epsW` is the same formula but existential; X7 must add `crossingNeckAccuracy` to `εbar`'s `min`.

## Resumed (XA4′), 2026-09-26
- Scratch moved to `scratchpad\xa4b` (copied xa4's oleans/scripts; module prefix still `XA4Scratch`).
- On disk at resume: `LocalFlowLimitShiftedConvergence.lean` (184 lines, compiled by predecessor) and
  `CrossingTimeZeroBound.lean` (557 lines, full draft of the traced-region wrapper, the depth schedule,
  X3a and X3; its last compile attempt hit the missing committed `TracedRegionBackwardStep` olean).
- First compile of the draft: X3a exceeded the per-declaration heartbeat budget (every step re-checks
  W1′'s conclusion instantiated at `(K ∘ σ).toHistory`). No budget override; instead split along the
  real interface:
  - NEW generic file `Surgery/Topology/TracedRegionTimeZeroScalarBound.lean` (321 lines):
    `ObservedHistory.exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule` — for any observed-history
    blow-up sequence with traced regions of radius `k+3` at depth `τ k ≤ 1` (W1′'s `htraced`), `R(t−t₀) → 0`,
    W1′'s `hnc`/`hpinch`, spatial canonical witnesses with neck charts before `t₀` above `qs n ≤ R n·Cq`
    (B6's `hwit` form) and `0 < eps ≤ crossingNeckAccuracy`: `∃ ψ StrictMono, ∃ C₀ ≥ 1, ∀ A > 0, ∀ᶠ i`,
    `R ≤ C₀·Rψᵢ` on `B(t_{ψ i}, y_{ψ i}, A/√R)`. Proof = W1′ → Curvature:26 → exceptional-set shifted
    sequence → B9 (hW from B6) → Transfer:440 → private pull-back lemma (BallImage:160 + Scalar:464).
    Also holds `crossingNeckAccuracy` (+ `_pos`) and the private `closedBall_one_subset_of_ball_eq`, moved
    out of CrossingTimeZeroBound.
  - `CrossingTimeZeroBound.lean` (316 lines): X3a is now the instantiation at `K ∘ σ` + transport by
    `scalar_ball_bound_extendAt_iff`; X3 unchanged.
  - Fixed: `SpatialNeck.mono` needs `Geometry/Neck/SpatialTolerance` import; `Nonempty` handled by `.map`.
- Compile (scratch chain, standard linter set, 4 threads): LocalFlowLimitShiftedConvergence 61 s,
  TracedRegionTimeZeroScalarBound 65 s, CrossingTimeZeroBound 52 s — all clean (0 errors, 0 warnings).
- Axioms (probe, deleted): X3a `exists_subseq_scalar_le_on_normalized_balls_at_base`, X3
  `exists_subseq_depthExtendable_pos`, `exists_depth_schedule_isTracedRegion_extendAt`, the generic lemma,
  `crossingNeckAccuracy_pos`, `tendsto_metricDerivNormSupOn_localPull_shifted_to_zero_of_time_lipschitz`:
  all `[propext, Classical.choice, Quot.sound]`.
- Module docstrings added to LocalFlowLimitShiftedConvergence, TracedRegionTimeZeroScalarBound,
  CrossingTimeZeroBound.
- DEVIATION (unchanged from above): X3a and X3 carry `hεX : ε ≤ crossingNeckAccuracy.{u}` before `σ`;
  otherwise verbatim DCA §2.5 inside Σ (Σ without `hεfar`, unused). X7 must put `crossingNeckAccuracy` into
  `εbar`'s `min`.
- Wiring for the lead (not done here): register `TracedRegionTimeZeroScalarBound`, `LocalFlowLimitShiftedConvergence`,
  `CrossingTimeZeroBound` in the root aggregate.
