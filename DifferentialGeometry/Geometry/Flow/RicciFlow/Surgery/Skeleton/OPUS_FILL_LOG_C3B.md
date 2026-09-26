# OPUS_FILL_LOG_C3B (brick 11 of DESIGN_C3B: the `CapWindowContinuation` leaf assembly)

## 2026-09-26 entry 1 (start)

Read: AGENTS.md, NAMING.md, Skeleton/README.md, DESIGN_C3B.md, LEAD_NOTES_20260926.md (11:15Z:
bridge at `t' = t + μ'`), logs L1, L23, L4, L5, L6, L7, L89, the leaf, the bridge.
Uncommitted inputs without oleans: L5 (`StandardWindowShiftConvergence`), L6
(`StandardClosenessWindowedWitness`), L89 (`CapWindowDerivativeTransfer`). Plan: compile these to
a scratch output directory outside the repo (`lean -o`, scratch dir prepended to `LEAN_PATH`),
then compile the assembly files against them.

## 2026-09-26 entry 2 (scratch oleans; failures first)

Scratch compile method: the three uncommitted inputs are copied outside the repo under a
distinct top-level module prefix (`C3bScratch.L5`, `C3bScratch.L6` with its L5 import renamed,
`C3bScratch.L89`), because Lean resolves the package root `DifferentialGeometry` from the first
`LEAN_PATH` entry that has it. Each is compiled with
`lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true -o <scratch>/out/C3bScratch/X.olean`
under `LEAN_PATH = <scratch>/out ; (lake env LEAN_PATH)`, `LEAN_NUM_THREADS=2`. L5 48 s, L89 53 s,
L6 42 s, all with no output.

### FAILURE 1: the L6 margin cannot be met near the end of the slab (decision (b) is insufficient)

L6 (`exists_uniform_orientedWitness_of_standard_close`) needs the window flow on `closed 0 T'`
with `T + μ ≤ T'`, where `μ` is fixed before `(D, N, e)`. So in slab time the bridge must be
called at `t' ≥ t + μ/q` with `t' < s`. Quantifier chain: `μ → (D,N,e) → bridge (R, m₀, ζ₀, δ₀)
→ Rcap, mcap` (before `qcan`), and `G, t₀, η` come after all of these. `q` is bounded below only
by `(2ρmax²)⁻¹`, which is also fixed before `G`. The leaf needs every `t ∈ [t₀, t₀+η) ∩ (a, s)`,
and `t₀` may lie arbitrarily close to `s` (event branch: `s` is the next event time and the flow is
singular there). When `q(s − t) < μ`, no admissible `t'` exists. Changing `μ` per point does not
help: `D, N, e` and hence `Rcap, mcap` would move. The derivative clause needs the same S-witness
in the aged case (`T > Θ₃`, below), so this is not confined to the witness clause.
Needed instead: the endpoint form (DESIGN_C3B §4 L6 as first stated; = option (a) of the L6 log):

```lean
theorem exists_uniform_orientedWitness_of_standard_close_endpoint {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ τQ : ℝ, 0 < τQ ∧ ∀ (Θ r : ℝ), Θ < 1 →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
      ‖z.val‖ < r → τQ ≤ T * S.scalar T z →
      OrientedWitness S o δ standardModelKappa z T
```

With it the bridge is called at `t` itself and no margin bookkeeping is needed.

### FAILURE 2: the bridge's current-slab hypothesis `Gk.DerivativeBoundBefore C qcan' t`

The leaf supplies only `…DerivativeBoundBefore Ctime qcan t₀`, while the bridge needs the bound on
`(a, t)` for the point's `t ∈ [t₀, t₀+η)`. The bridge's `qcan'` is quantified after its
constants, so per point it can be taken as large as `Cbirth·q` (`≥ 2qcan` by the `ρmax` choice).
This does not remove the need. For `t₀ > a`, DESIGN_C3B's L10a (continuity, `2Ctime`, `2qcan`)
closes it. L10a is not delivered. For `t₀ = a` the bound on `(a, a+η)` is L10b (post-event
slice). LEAD_NOTES_20260926.md (L10b bullet) says L10b is "not needed" because the age clause excludes `t₀ = a`, but
the derivative/gradient clauses have no age condition. Young fresh caps (`j.succ = k`,
`T ≤ Θ₃`) go through D2, and D2 calls the bridge, which needs the bound on `(a, t)`. So L10b is
needed for this leaf at `t₀ = a`.
Statement needed (both cases at once):

```lean
theorem exists_derivativeBoundBefore_of_before {P₀ : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory P₀) (k : Fin (H.eventCount + 1)) {s : ℝ}
    (Gk : (H.stage k).IncomingSlab (H.time k) s)
    (hGk : Gk.flow.base.metric (H.time k) = H.initialMetric k) {Ctime : ℝ≥0} {qcan t₀ : ℝ}
    (hq : 0 < qcan) (ht₀ : t₀ ∈ Ico (H.time k) s) (hprev : H.EventSlabsDerivative Ctime qcan k)
    (h : Gk.DerivativeBoundBefore Ctime qcan t₀) :
    ∃ η, 0 < η ∧ ∀ t, t < t₀ + η → Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) t
```

(At `t₀ = a` this needs more hypotheses, such as the cutoff records and the standard-cap
evolution on fresh caps. That is DESIGN_C3B's L10b and is still open.)

Consequence: the leaf is not provable from the delivered bricks. Below, every other step is
delivered as compiled lemmas.

## 2026-09-26 entry 3 (progress)

Compiled so far (no output; scratch `#print axioms`: propext, Classical.choice, Quot.sound):
- helper `Surgery/Topology/CapWindowFlowPushforward.lean` (in place, `lake env lean`):
  L7a `DifferentialGeometry.Topology.partialDiffeomorphOfInjective` (+ `_apply`, `_source = univ`);
  `ObservedHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val`,
  `injective_…_val_val`, `localPullMetric_scaleMetric_backwardSurvivorIncomingMetric` (the metric
  check: `extendedMetric` on `[time k, t]` is the restriction of `Gk`, both below `t` and at `t`),
  `window_metric_eq_localPullMetric_scaleMetric` (bridge window flow = scaled pullback of `Gk`
  along `Φ = (Ξ ·).val.val` wherever `time k ≤ b + τ/q ≤ t`);
  `OrientedThreeStage.IncomingSlab.orientedWitness_of_scaled_localPull_window` (design step 4:
  shift `A = 1`, L7 pushforward, undo `A = q`; exact, no tolerance loss).
- assembly file (scratch copy with renamed imports): pipeline step 5
  `IncomingSlab.exists_canonicalWitness_of_orientedWitness`; derivative/gradient case A by curvature
  jets (`exists_scalar_derivative_bounds_of_scaled_localPull_witness`: needs the witness only on
  the window flow `S` at `(z,T)`, not on `Gk`; this matters because for `j.succ < k` the S-window
  may reach before `time k`, where L89's case-A lemma, which needs the witness on `Gk`, does not
  apply); `le_mul_of_half_standard_scalar_lower` (young/aged split at
  `Θ₃ = 2τQ/(c₀+2τQ)` from the ½ lower comparison, which avoids the `|R_S − R_Q| < 1` trigger);
  `RetainedCoreHistory.IsCanonicalCutoffRecordFamily.birth_scale_bounds` (`ρmax² ≤ Cbirth/(4qcan)`,
  `≤ a₀/2` gives `2qcan ≤ Cbirth·q`, `1 ≤ a₀·q`).

## 2026-09-26 entry 4 (delivered; the leaf is NOT proved)

Files (new, not registered in the root aggregate, nothing else edited, no git writes, no
`lake build`):
- `Surgery/Topology/CapWindowFlowPushforward.lean` (248 lines). Compiled in place with
  `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`,
  no output.
- `Surgery/Topology/CapWindowContinuationAssembly.lean` (471 lines). It imports the uncommitted L6
  and L89, so it was compiled as a scratch copy whose only difference is the three import lines
  (`C3bScratch.{Pushforward,L6,L89}`, checked with `diff`), against the scratch oleans of entry 2,
  with the same options. No output.
- Scratch `#print axioms` for all 15 public declarations of the two files: `propext`,
  `Classical.choice`, `Quot.sound`. Scratch `#lint` (14 linters): assembly clean; helper: only
  `docBlame` on `partialDiffeomorphOfInjective`, which AGENTS.md excludes. Lines ≤ 100, no
  comments, no sorry, no option overrides. All public names are grep-unique.

Main result (per point, from the delivered bricks only), in the leaf's quantifier order:

```lean
theorem RetainedCoreHistory.exists_capWindowPoint_bounds_of_room (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (C₀ τ₀ : ℝ) (Ctime₀ : ℝ≥0), 1 ≤ C₀ ∧ 0 < τ₀ ∧
    ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), C₀ ≤ C1 → C₀ ≤ C2 → τ₀ ≤ τmin →
      Ctime₀ ≤ Ctime → Ctime₀ ≤ Cgrad →
    ∀ (Dcap θcap : ℝ), 0 < Dcap → θcap < 1 →
    ∃ (Rcap μ : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧ 0 < μ ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory P₀, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
    ∀ t : ℝ, H.time k < t → t + 2 * ρmax ^ 2 * μ < s →
      Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t + 2 * ρmax ^ 2 * μ) →
    ∀ y : (H.stage k).Carrier, H.CapWindowPoint records k y t Dcap θcap →
      qcan < Gk.flow.scalar t y →
      (τmin ≤ Gk.flow.scalar t y * (t - H.time k) →
        ∃ W : CanonicalWitness Gk.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤ Ctime * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v)
```

Constants: `C₀ = Cε` (pipeline); `δ = min δ₀ ¼`; `τ₀ = max τQ δ⁻¹ + 1`;
`Ctime₀ = max C_A C_B`. Here `C_A` is the absolute jets constant and `C_B` is brick 0 at
`Θ₃ = 2τQ/(c₀+2τQ)`. Then `Θ = max θcap ½`, `μ = (1−Θ)/2`, bridge at `Θ+μ` with
`C = 2Ctime` and `(D_W, e_W, N_W)` from L6 at `(Θ+μ, Dcap+1, μ)`, and `η` from the ½-lower
comparison. `Rcap = max R₁ R₂`, `mcap = max m₁ m₂` (brick 0 at `D = Dcap`), `δmax = min δ₁ δ₂`,
`εcap = min ζ₁ ζ₂`, `ρmax = min √(Cb/(4qcan)) √(a₀/2)` with `Cb = min Cbirth₁ Cbirth₂`.
Per point: bridge at `t' = t + μ/q` (`μ/q < 2ρmax²μ`). Young case `T ≤ Θ₃`: brick 0 at `t`.
Aged case: the ½ lower comparison and `c₀/(1−T)` give `τQ ≤ T·R_S`, then L6, then jets on `S`,
then scaling to `Gk`. Canonical clause: `R(t−a) ≥ τmin` gives `τQ ≤ T·R_S`, then L6, then the
pushforward to `Gk`, then the pipeline.

The two extra hypotheses, `t + 2ρmax²μ < s` and `DerivativeBoundBefore … (t + 2ρmax²μ)`, are
exactly failures 1 and 2 (entry 2). The leaf needs `η` with `t₀ + η + 2ρmax²μ ≤ s`. That fails
when `s − t₀ ≤ 2ρmax²μ`, and `ρmax, μ` are fixed before `G`.

### Remaining gap

The leaf is not proved. Two statements remain, both in entry 2:
1. `exists_uniform_orientedWitness_of_standard_close_endpoint` (L6 with `μ = 0`, `T' = T`).
2. The current-slab derivative bound: L10a for `t₀ > a`, L10b for `t₀ = a`.

With (1), rerun the per-point theorem with the bridge at `t` itself: drop `μ` and the room
hypothesis. `exists_scalar_derivative_bounds_of_window_orientedWitness` already accepts `T ≤ T'`,
and `orientedWitness_of_capWindow_flow` already accepts `t ≤ t'`. With (2) the hypothesis becomes
`Gk.DerivativeBoundBefore (2Ctime) (2qcan) t` for `t < t₀ + η`. The leaf glue is then: `a₀`
from the HI supplier (inside), `hH.1`/`hH.2.2.2.2` for the identification and `Λδ ≤ ½`,
`H.event_initial j` or `hG.2` for the initial metric, and `η` from (2) and `s − t₀`.

Other public declarations (exact names):
- helper: `DifferentialGeometry.Topology.partialDiffeomorphOfInjective` (+ `_apply`, `_source`);
  `…ObservedHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val`,
  `…ObservedHistory.injective_backwardSurvivorIncomingDomain_val_val`,
  `…ObservedHistory.localPullMetric_scaleMetric_backwardSurvivorIncomingMetric`,
  `…ObservedHistory.window_metric_eq_localPullMetric_scaleMetric`,
  `…OrientedThreeStage.IncomingSlab.orientedWitness_of_scaled_localPull_window`.
- assembly: `…IncomingSlab.exists_canonicalWitness_of_orientedWitness`,
  `…IncomingSlab.exists_scalar_derivative_bounds_of_scaled_localPull_witness`,
  `…IncomingSlab.exists_scalar_derivative_bounds_of_window_orientedWitness`,
  `…Topology.le_mul_of_half_standard_scalar_lower`,
  `…RetainedCoreHistory.IsCanonicalCutoffRecordFamily.birth_scale_bounds`,
  `…RetainedCoreHistory.capWindow_flow_metric_eq`, `…RetainedCoreHistory.orientedWitness_of_capWindow_flow`,
  `…RetainedCoreHistory.eventSlabsDerivative_two_mul`,
  `…RetainedCoreHistory.exists_capWindowPoint_bounds_of_room`.

Placement notes for acceptance: `partialDiffeomorphOfInjective` belongs next to
`diffeomorphRangeOfInjective` (`Topology/Manifold/LocalDiffeomorphRange.lean`), and
`le_mul_of_half_standard_scalar_lower` is plain real arithmetic. L89's case-A lemma (witness on
`Gk`) is not used. The jets route on `S` replaces it, because when `j.succ < k` the S-window can
reach before `time k`. The per-point theorem is close to the default heartbeat budget, so keep
further additions in separate lemmas.
