# B7 — depth induction for B5's `hscal` on the final slab (2026-09-26)

- Start. Read AGENTS.md, Skeleton/README, OPUS_FILL_LOG_B3C/B6B, DESIGN_CROSSING (B4/B5/B7),
  headline `BoundedCurvatureAtDistance.lean`, `TracedRegionDepthStep.lean`, B5
  (`TracedRegionOrCapWindow.lean:546,665`), B2 extendHorizon transfers (`TracedRegion.lean:648–935`).
- Finding (failure first, analysed before writing Lean): the re-anchoring induction does NOT close
  for arbitrary `T`. On the final slab with the window inside it every backward trace is trivial,
  so the question is purely: bound `R(x, v)` for `x ∈ B_t(y, A/√R)`, `v ∈ [t − T/R, t]`.
  (1) Re-anchoring at slice `v` gives `R(x,v) ≤ Q(A')·R(y,v)`, but the base's own scale `R(y,v)`
  is controlled only by `|∂R| ≤ Ctime R²`, i.e. `1/R(y,v) ≥ 1/R − Ctime(t − v)`: finite only for
  normalized depth `T < 1/Ctime`. Nothing in the headline links different slices.
  (2) Even for `T < 1/Ctime` the anchor radius is not step-independent: `x@v ∈ B_v(y, A'/√R(y,v))`
  needs the distortion `d_v ≤ e^{2∫|Ric|}·d_t` along the `g_t`-segment inside the ball, whose
  exponent is `≍ K(phi)·(bound on the ball)·T`, i.e. `≍ Q(A')·T`; so `A' = e^{c·Q(A')·T}·A` has a
  fixed point only when `T ≲ 1/Q(A')`. Step-wise re-anchoring (`D_{k+1} = e^{c/Ctime} D_k`,
  steps `δ_k ≍ 1/(Ctime·Q(D_k))`) gives total depth `Σ δ_k`, which converges for fast-growing `Q`.
  (3) Forward ODE check: `R(x,v) = K·R` forces `R(x,t) ≥ R/(Ctime·T + 1/K)`, contradicting the
  headline only when `Ctime·T < 1/Q(A)`. So every local argument has horizon `≍ 1/(Ctime·Q(A))`,
  which is what one step of B4 already gives. Arbitrary `T` needs the finite-horizon curvature
  bound of the limit (B6c / F9 of DESIGN_CROSSING), confirming OPUS_FILL_LOG_B6B.
- Deliverable decided: `hscal` (B5 shape) on the final slab for `2·Ctime·Q(A)·T ≤ 1`, from the
  headline at the slice `t` plus one depth step; the depth may cross events (the step lemma uses
  `EventSlabsDerivative`), so no `Λ'` margin is needed beyond the headline's own window.
- DONE. File `Surgery/Topology/TracedRegionDepthInduction.lean` (new, not registered, no git
  writes; 150 lines). Theorems:
  * `RetainedCoreHistory.scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball` (any
    history, any `u ≤ t`): `R ≤ Q·R₀` on `B_t(y, ρ)` + `2·Ctime·Q·T ≤ 1` + `u = t − T/R₀` +
    `qcan ≤ Q·R₀` + the B4 derivative hypotheses ⇒ B5's `hscal` with radius `ρ`, bound `2·(Q·R₀)`
    (depth-0 anchor + one `scalar_le_two_mul_along_backward_traces_of_depth_step`).
  * private `scalar_le_on_ball_extendHorizon_of_final_slab` (transfer of the slice-`t` ball bound
    of `S` to `H.extendHorizon t hT S hS` at `activeStage tt = last`, via `HEq`).
  * `RetainedCoreHistory.exists_scalar_le_along_backward_traces_of_final_slab_window`
    (κ C1 C2 hκ Ctime Cgrad hphi): `∃ εcone > 0, ∀ ε ≤ εcone, ∀ A > 0, ∃ Q Λ, 1 ≤ Q ∧ 1 ≤ Λ ∧`
    [exactly the headline's hypotheses on `H hend S hS y q ρ`] `→ ∀ hT tt, ↑tt = t → ∀ y', HEq y' y
    → ∀ T > 0, 2·Ctime·Q·T ≤ 1 → ∀ uu, ↑uu = t − T/R(y,t) →` B5's `hscal` for
    `H.extendHorizon t hT S hS` at `tt`, `y'`, `R := R(y,t)`, `A`, `Q` (bound `2·(Q·R)`).
    `Q, Λ, εcone` are the headline's. Depth may cross events (EventSlabsDerivative), so no extra
    window margin: the only window is the headline's `time last ≤ t − Λ/R`.
- B5 hypothesis this fills (`exists_isTracedRegion_or_capWindowPoint_at_scale`, TracedRegionOrCapWindow:708):
  `∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y (A / √R),
   ∀ w (_ : u ≤ w) (hwt : w ≤ t) (B : BackwardPointTrace … x) v (hwv : w ≤ v) (hvt : v ≤ t),
   metricScalarAt (stageMetric (activeStage v) v) (B.point (activeStage v) …) ≤ 2 * (Q * R)`,
  with `u = t − T/R`. So B5's left branch is unconditional on the final slab for
  `T ≤ 1/(2·Ctime·Q(A))`; B5's other side conditions there: `1 − c/(8TQ) ≤ θcap`, i.e.
  `θcap ≥ 1 − c·Ctime/4` at the maximal `T`. NOT for arbitrary `T` (finding above).
- Verification: scratch modules outside the repo (`scratchpad/b7`): Necks, Cone, Headline (import
  rewritten) compiled with `lean -o` (pc3 toolchain binary, `LEAN_PATH` = scratch out + `lake env`),
  then this file with its first import rewritten to the scratch headline, with
  `-Dweak.linter.mathlibStandardSet=true`, `LEAN_NUM_THREADS=2`: no output. `#print axioms` of both
  public theorems: propext, Classical.choice, Quot.sound. `#lint` (14 linters): 0 errors. Public
  names unique library-wide. Lines ≤ 100. Scratch removed.
