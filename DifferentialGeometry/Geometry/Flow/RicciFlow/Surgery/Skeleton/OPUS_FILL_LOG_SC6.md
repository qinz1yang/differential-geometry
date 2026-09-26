# OPUS fill log SC6: T4′ consumer wave 6 = plumbing bricks (2026-09-26)

Worker lane SC6. Scope: (1) sequence-level depth induction producing B13's `htraced`, and the B13 call
with its class inputs; (2) top-ball bounds at the top slice; (3) the `extendHorizon` transfer of
`StronglyCanonicalBefore`. New files only; read-only compiles (`LEAN_NUM_THREADS=2 lake env lean
-DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`); uncommitted imports through scratch
modules `SC6.*` under the session scratchpad `sc6/`. No git writes, no lake build, no root-aggregate edit.
SC4 owns line/packaging/converter, SC5 owns finite-window splitting and the ℝ×N capture.

## Progress
- read AGENTS.md (pc3: no header, no module docstring, zero comments), SC2/SC3/SC4/XA3/XA4 logs,
  DESIGN_S_SUPPLY §0–§3, B13 (`TracedRegionAncientLimitScalarBound.lean:42`), SC3's five files,
  `FineCutNeckSupplyStrong.lean`, `RetainedCoreHistoryExtendAt(Before).lean` (XA4), `extendHorizon`.
- scratch chain `SC6.*` (14 uncommitted suppliers: SP1 ×3, SC3 ×4, SC1 trigger chain ×4, ClassSupply,
  XA4 extendAt ×2) being compiled to scratch oleans.

## Item 3 = `extendHorizon` transfer (`Surgery/Topology/HistoryStrongNeckExtendHorizon.lean`)
Statements (ns `…Surgery.Topology.RetainedCoreHistory`; `H' := H.extendHorizon T hT S hS`, any `T`, `S`):
```lean
theorem backwardSurvivorDomain_extendHorizon (first k) (hle : first ≤ k) :
    H'.toHistory.backwardSurvivorDomain first k hle = H.toHistory.backwardSurvivorDomain first k hle
theorem historyStrongNeck_extendHorizon_iff (k) (G : (H.stage k).IncomingSlab (H.time k) s) (eps y t) :
    H'.toHistory.HistoryStrongNeck k G eps y t ↔ H.toHistory.HistoryStrongNeck k G eps y t
theorem stronglyCanonicalAt_extendHorizon_iff … : H'.StronglyCanonicalAt k G ε ε₁ C1 C2 y t ↔ H.StronglyCanonicalAt …
theorem stronglyCanonicalBefore_extendHorizon_iff … :
    H'.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan t₀ ↔ H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan t₀
theorem eventSlabsStronglyCanonical_extendHorizon_iff … :
    H'.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan k ↔ H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan k
theorem exists_slab_stronglyCanonicalBefore_extendHorizon_closedPrefix (hend) (G) (hG) (hat : time last < T)
    (hTs : T < s) (hcan : H.StronglyCanonicalBefore (Fin.last _) G ε ε₁ C1 C2 qcan s) (v) (hv : H'.activeStage v = last) :
    -- H' := H.extendHorizon T _ (G.closedPrefix T hat hTs) hG; exactly the `hterm` binder of
    -- `HistoryStrongNeckClassSupply` (SC3-e) for H'
    ∃ s' G', v < s' ∧ (G' = stage metric on [time (activeStage v), v]) ∧ H'.StronglyCanonicalBefore (activeStage v) G' … s'
```
Weakest natural form: every `k` (not only `Fin.last`), every horizon extension `S` (not only `closedPrefix`).
Route: `HistoryStrongNeck` is not definitionally horizon-independent (`BackwardPointTrace H'` and
`BackwardPointTrace H` are different structure types, so the survivor domains are different `Opens` terms).
A private body `strongNeckBody K … O f hf` abstracts the survivor domain `O` and the terminal maps `f`
(`HistoryStrongNeck K = ∃ first hle, strongNeckBody K … (K.bSD …) (K.bSTM …) _` by `rfl`); the body is
horizon-independent by defeq; `O₁ = O₂` (trace conversion `⟨A.point, A.endpoint_eq, A.crossing⟩`) and the
pointwise equality of the terminal maps (`backwardSurvivorMap_eq_point`) close it by `subst`.
Deviation: this mechanical brick was elaborated together with its proof (no separate `sorry` pass).
- Compile: clean (zero output), 48 s.

## Findings before the item-1/2 statements (failures first)

1. **The depth increment must be uniform in the radius `A`, so the induction needs a UNIFORM top upper
   bound `Qup` (independent of `A`).** SC3-d's gain at radius `A` is `1/(10·Qup(A))` (normalized). The
   supply at depth `T` (SC5's ℝ×N capture) needs the traced region at depth `T` on ALL radii (it builds
   the limit on `[−T, 0]`), so with `Qup(A) → ∞` the induction `P(T) ∀A ⇒ P(T+δ) ∀A` has `δ = inf_A = 0`
   and stalls. Perelman's route (KL §53) makes `δ` uniform from the GLOBAL curvature bound of the time-0
   limit (complete, `Rm ≥ 0`, necks everywhere ⇒ `sup R < ∞`), i.e. `∃ Qup, ∀ A, ∀ᶠ n, R ≤ Qup·Rₙ` on the
   normalized `A`-ball. That is the hypothesis shape `hball` below (`Qup` before `∀ A`, `Qlow(A)` after).
2. **Top-ball bounds for all `A` are NOT a consequence of neck data + closeness to `L` alone.** From
   spatial witnesses the committed chain gives `C2`-comparability only on normalized radius
   `A(√C2 − 1) < √C2` (`exists_scalar_bound_at_distance_of_spatialCanonicalWitness`,
   `SpatialBoundedCurvatureAtDistance.lean:283`); the gradient bound gives the upper bound only on
   `r ≤ 1/(4·Cgrad·√R)` (`SlabGradientScalarControl.lean:25`). In an `ε`-horn `R^{-1/2}` can have slope
   `~ε²`, so the singular end can sit at normalized distance `~ε⁻²`: an all-`A` bound is Perelman's
   bounded-curvature-at-bounded-distance (cone argument). The tree HAS it for final-slab windows:
   `RetainedCoreHistory.exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy`
   (`BoundedCurvatureAtDistanceConstants.lean:52`, committed; `ε ≤ coneAccuracy`, `∀ A, ∃ Q Λ`, slab age
   `time last ≤ t − Λ/R(y)`, class witnesses, derivative/gradient/pinching/terminal noncollapsing). It
   gives `Qup(A)`, not a uniform `Qup` (Finding 1).

## Item 1 statements (recorded BEFORE proving; elaborated with `sorry`: only `declaration uses sorry`)
File `Surgery/Topology/HistoryStrongNeckDepthInduction.lean`, ns `…Surgery.Topology.RetainedCoreHistory`.

**SC6-a** (class clause + "every class witness is a neck" ⇒ SC3's `HasStrongNeckAt`):
```lean
theorem hasStrongNeckAt_of_forall_neckAlternative
    (hclass : H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount))
    (v) (p) (hev : H.time (activeStage v) < v) (hterm : activeStage v = last → ∃ s G, v < s ∧ agree ∧
      H.StronglyCanonicalBefore (activeStage v) G ε ε₁ C1 C2 qcan s)
    (hq : qcan < R(stageMetric (activeStage v) v) p)
    (hneck : ∀ W : SpatialCanonicalWitness (stageMetric (activeStage v) v) ε C1 C2 p,
      W.capTubeHasNeckChart ε → ∃ nk, W.alternative = .neck nk) :
    H.toHistory.HasStrongNeckAt ε₁ v p
```
**SC6-b** (SC3-d with the witness-level supply; the one-history step):
`isTracedRegion_of_forall_neckAlternative` — SC3-d's hypotheses with `hsupply` replaced by `hclass`,
`hterm` on `[t − T, t]`, `qcan < L`, `ε₁ ≤ 1/30000`, and
`hneck : ∀ x ∈ ball, ∀ v ∈ [t − T, t] (non-event), ∀ trace B, L ≤ R(B.point) → ∀ W … at B.point,
W.capTubeHasNeckChart ε → ∃ nk, W.alternative = .neck nk`; conclusion SC3-d's
`isTracedRegion t p ρ (T + (10 * Qup)⁻¹) (8 * √3 * (1 + phi 1 + phi 0) * max Qup 1)`.

**SC6-c** (sequence-level depth induction; output = `htraced` of B13 verbatim):
```lean
theorem exists_isTracedRegion_of_forall_neckAlternative_of_depth_induction
    {P₀ : ℕ → OrientedThreeStage} (H : ∀ n, RetainedCoreHistory (P₀ n)) (t) (y) (R : ℕ → ℝ)
    (hRlim : Tendsto R atTop atTop) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hphi) (hpinch : ∀ n, EventSlabsPinched) (hlast : ∀ n, final-slab pinching if active = last)
    (htop : ∀ n, time (activeStage (t n)) < t n) (hε₁ : ε₁ ≤ 1/30000)
    (hq : ∀ c > 0, ∀ᶠ n, qcan n < c * R n) (hclass : ∀ n, EventSlabsStronglyCanonical … (qcan n) last)
    (hterm : ∀ n v, v ≤ t n → non-event → activeStage v = last → ∃ s G, … StronglyCanonicalBefore …)
    {Qup} (hball : ∀ A > 0, ∃ Qlow > 0, ∀ᶠ n, ∀ x ∈ ball(y n, A/√Rₙ), Qlow Rₙ ≤ R x ∧ R x ≤ Qup Rₙ)
    (hsupply : ∀ T ≥ 0, (∀ A T', 0 < A → 0 < T' → T' ≤ T → ∃ K ≥ 0, ∀ᶠ n,
        isTracedRegion (t n) (y n) (A/√Rₙ) (T'/Rₙ) (K Rₙ)) →
      ∀ A c, 0 < A → 0 < c → ∀ᶠ n, ∀ x ∈ ball(y n, A/√Rₙ), ∀ v, t n − T/Rₙ ≤ v → ∀ hvt : v ≤ t n,
        non-event → ∀ B : BackwardPointTrace … x, c Rₙ ≤ R(B.point) →
        ∀ W : SpatialCanonicalWitness (stageMetric (activeStage v) v) ε C1 C2 (B.point),
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = .neck nk) :
    ∀ A T, 0 < A → 0 < T → ∃ K, 0 ≤ K ∧ ∀ᶠ n,
      (H n).toHistory.isTracedRegion (t n) (y n) (A / √(R n)) (T / R n) (K * R n)
```
`hsupply` is the per-layer supply as an explicit hypothesis in SC5's output shape: its premise is the
traced region at every depth `T' ≤ T` (on all radii), its conclusion that every class witness at the
trace points of depth `≤ T` above the floor `c·Rₙ` is a neck. At `T = 0` the premise is vacuous and the
conclusion is at the top slice only (discharged by SC2-b `eventually_forall_neck_alternative_of_subset_hornHalfRange`
once the normalized ball lies in its compact `B`). Route: depth `(m+1)·δ`, `δ = (10·Qup)⁻¹`, by induction
on `m`: SC6-b at `T = m·δ/Rₙ`, `Qlow' = Qlow Rₙ`, `Qup' = Qup Rₙ`, floor `L = Qlow Rₙ (3/4)^⌈10 Qup m δ⌉`
(= `c·Rₙ`), `K = 8√3(1+φ1+φ0)·Qup`; then `mono_depth`.

**SC6-d = the B13 call** (`Surgery/Topology/HistoryStrongNeckAncientLimit.lean`, recorded BEFORE proving,
elaborated with `sorry`):
```lean
theorem exists_bounded_ancient_pointed_flow_limit_extendAt_of_forall_neckAlternative :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ {P₀ : ℕ → OrientedThreeStage} (H Hext : ∀ n, RetainedCoreHistory (P₀ n)) (hend) {s τ} (G) (hG)
      (hat : ∀ n, time last < τ n) (hτs : ∀ n, τ n < s n),
      (∀ n, Hext n = (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)) →
    ∀ (t) (ht : ∀ n, (t n : ℝ) = τ n) (y) (R) (hR : ∀ n, 0 < R n), Tendsto R atTop atTop →
      Tendsto (fun n => R n * τ n) atTop atTop →
    ∀ {κ ε ε₁ C1 C2 qcan} {Ctime} {phi}, 0 < κ → 0 < ε → ε ≤ epsW → ε₁ ≤ 1/30000 → (∀ n, qcan ≤ R n) →
      AdmissiblePinchingFunction phi → (∀ n, EventSlabsPinched) → (∀ n, PhiAlmostNonnegative (G n) on Ico) →
      (∀ n, EventSlabsDerivative Ctime qcan last) → (∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n)) →
      (∀ n, EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan last) →
      (∀ n, StronglyCanonicalBefore last (G n) ε ε₁ C1 C2 qcan (s n)) →
      (∀ n, NoncollapsedBefore κ ε (time last)) → (∀ n, TerminalNoncollapsedBefore … κ ε (τ n)) →
    ∀ {Qup}, (hball of SC6-c for Hext) → (hsupply of SC6-c for Hext) →
      let X := (rescaled stage metrics of Hext at t, as B13)
      <B13's conclusion verbatim with H n := (Hext n).toHistory, t₀ n := t n, ρ := ε>
```
All T4′ class fields enter in their T4′ form (`FineCutNeckSupplyStrong` binders, with `ρ = ε`, `qs = qcan`,
`Cs = Cq = 1`, `t₀ = t`, sliver `0`). `Hext` is tied to its producer by the equation `hext`.
Discharge map: `htraced` = SC6-c on `Hext` (with `hclass` via item 3's `eventSlabsStronglyCanonical_extendHorizon_iff`,
`hterm` via item 3's `exists_slab_stronglyCanonicalBefore_extendHorizon_closedPrefix`, `hlast` via
`extendHorizon_finalSlab_phiAlmostNonnegative`); `hnc` via XA4 `volume_ge_extendAt_of_terminalNoncollapsedBefore`;
`hpinch` via XA4 `curvatureOperatorLowerBoundAt_extendAt_of_pinched`; `hwit` via XA4
`exists_spatialCanonicalWitness_extendAt_of_before` (+ `StronglyCanonicalBefore.spatiallyCanonicalBefore`);
`hderiv` via `abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt` (DerivativeCutoff:86) with
`extendHorizon_finalSlab_derivativeBoundBefore`.

## Item 1 proof status
- SC6-a, SC6-b, SC6-c PROVED as stated (`HistoryStrongNeckDepthInduction.lean`), clean compile (zero
  output), 37–53 s. SC6-c's induction constant `K = 8√3(1+φ1+φ0)·Qup`; `0 < Qup` derived from `hball`.
- SC6-d PROVED as stated (`HistoryStrongNeckAncientLimit.lean`), clean compile, 34–38 s. The three B13
  private local instances (`SigmaCompactSpace`/`MeasurableSpace`/`BorelSpace` on `Opens`) are copied
  (deferred merge: they belong next to `Opens` instances in a shared home; four files now carry them).
- Scratch note: `TracedRegionBackwardStep.olean` is missing from the shared build (hash/trace present,
  olean absent since 03:57); it is compiled as scratch module `SC6.TracedRegionBackwardStep` (verbatim copy).

## Item 2 statements (recorded BEFORE proving; elaborated with `sorry`)
File `Surgery/Topology/ScalarComparisonAtDistance.lean`, ns `…Surgery.Topology.RetainedCoreHistory`.

**SC6-e** (two-sided cone bound, single history, final-slab window): the committed upper bound
`exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy` (binder list verbatim) with
conclusion strengthened to `Q⁻¹ * R(y) ≤ R(z) ∧ R(z) ≤ Q * R(y)` on `ball(y, A/√R(y))`:
`exists_scalar_bounds_at_distance_of_final_slab_window_of_le_coneAccuracy`. Route: `(Q₁, Λ₁)` from the
committed lemma, `Q = 2Q₁`, `Λ = 2Q₁Λ₁`; lower bound by contradiction: IVT in the ball
(`exists_riemannianEDistOf_lt_of_mem_Icc_scalar`, private, `open private`) gives `w` with
`R(w) = R(y)/(2Q₁)` and `d(w, y) < A/√R(y) ≤ A/√R(w)`; the committed lemma at base point `w` (its window,
floor and scale conditions follow from `Λ = 2Q₁Λ₁`) gives `R(y) ≤ Q₁R(w) = R(y)/2`.

**SC6-f** (top-ball bounds for the T4′ sequence, `hball`-shaped, radius-dependent):
```lean
theorem eventually_scalar_bounds_at_distance_extendAt_of_le_coneAccuracy (hεle : ε ≤ coneAccuracy)
    (hκ : 0 < κ) (hρ : 0 < ρ) (hphi) (H Hext) (hend) (G) (hG) (hat) (hτs)
    (hext : ∀ n, Hext n = (H n).extendAt …) (t) (ht : ∀ n, (t n : ℝ) = τ n) (y) (R)
    (hscal : ∀ n, R_{Hext n}(t n, y n) = R n) (hRlim : Tendsto R atTop atTop)
    (hage : Tendsto (fun n => R n * (τ n - time last)) atTop atTop)
    (hwit : ∀ n, (G n).SpatiallyCanonicalBefore ε C1 C2 qcan (s n)) (hderiv) (hderivG) (hgradG)
    (hpinch) (hpinchG) (hncG : ∀ n, TerminalNoncollapsedBefore … κ ρ (τ n)) :
    ∀ A > 0, ∃ Qlow Qup, 0 < Qlow ∧ ∀ᶠ n, ∀ x ∈ ball_{Hext n, t n}(y n, A/√Rₙ),
      Qlow * R n ≤ R x ∧ R x ≤ Qup * R n
```
DEVIATION (Findings 1–2): `Qup` depends on `A` here; SC6-c needs `Qup` before `∀ A` (the global
curvature bound of the time-0 limit). The age hypothesis `hage` holds in T4′ since `τₙ → sₙ⁻` stays a
fixed distance after `time last` relative to `Rₙ⁻¹ → 0` — the consumer chooses `τₙ`.
  CORRECTION to the last sentence: `hage` is NOT automatic in T4′. The histories vary with `n`, and
  nothing bounds the final slab length `sₙ − time last` below relative to `Rₙ⁻¹`: young deep horn points
  (`Rₙ·(τₙ − time last)` bounded) are possible. SC6-f covers the old case; the young case needs the
  event-crossing cone bound (`BoundedCurvatureAtDistanceSliceEvent/AfterEvent/Sliver`, which carry
  cap-window hypotheses at fixed `p₀`, DESIGN_S_SUPPLY F4) — open for the T4′ assembly.

## Item 2 proof status
- SC6-e, SC6-f PROVED as stated (`ScalarComparisonAtDistance.lean`), clean compile, 45 s. SC6-e uses the
  private IVT lemma of `BoundedCurvatureAtDistanceConstants.lean` through `open private` (no copy).
  SC6-f's `hncG` enters the committed cone lemma for the slab `(G.closedPrefix τ).restrictIncoming` by
  defeq (`closedPrefix`/`restrictIncoming` re-wrap the same metric).

## Deliverables (all new, uncommitted, NOT in the root aggregate)
| File (`Surgery/Topology/`) | Lines | Public declarations |
|---|---|---|
| `HistoryStrongNeckExtendHorizon.lean` | 156 | `RetainedCoreHistory.backwardSurvivorDomain_extendHorizon`, `historyStrongNeck_extendHorizon_iff`, `stronglyCanonicalAt_extendHorizon_iff`, `stronglyCanonicalBefore_extendHorizon_iff`, `eventSlabsStronglyCanonical_extendHorizon_iff`, `exists_slab_stronglyCanonicalBefore_extendHorizon_closedPrefix` (+ private `ObservedHistory.strongNeckBody` and two lemmas) |
| `HistoryStrongNeckDepthInduction.lean` | 235 | `RetainedCoreHistory.hasStrongNeckAt_of_forall_neckAlternative`, `isTracedRegion_of_forall_neckAlternative`, `exists_isTracedRegion_of_forall_neckAlternative_of_depth_induction` |
| `HistoryStrongNeckAncientLimit.lean` | 243 | `RetainedCoreHistory.exists_bounded_ancient_pointed_flow_limit_extendAt_of_forall_neckAlternative` |
| `ScalarComparisonAtDistance.lean` | 204 | `RetainedCoreHistory.exists_scalar_bounds_at_distance_of_final_slab_window_of_le_coneAccuracy`, `eventually_scalar_bounds_at_distance_extendAt_of_le_coneAccuracy` |
- Compile: each file read-only (`lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`,
  2 threads) through scratch modules `SC6.*`: zero output (no errors, no warnings; long lines only in imports).
  `#lint` on scratch copies: "All linting checks passed" for all four (14 linters).
- `#print axioms` for all 12 public declarations: `[propext, Classical.choice, Quot.sound]`; the
  `#print`/`#lint` lines lived only in scratch files (removed).
- New public names grep-unique library-wide. No committed file modified; one `open private`
  (`exists_riemannianEDistOf_lt_of_mem_Icc_scalar`); three copied private local instances (see item 1).
- Imports (uncommitted suppliers): item 3 ← SP1 `HistoryStrongNeck`; item 1 ← SC3 `HistoryStrongNeckClassSupply`
  (→ SC3 chain + SC1 trigger chain); SC6-d ← items 1/3 + XA4 `RetainedCoreHistoryExtendAtBefore` (→ X1k
  `RetainedCoreHistoryExtendAt`) + B13; item 2 ← X1k `RetainedCoreHistoryExtendAt` + committed cone chain.
- Acceptance order: SP1 ×3; SC3 (`TruncatedNeckScalar`, `BackwardTraceConcat`, `HistoryStrongNeckTrace`,
  `HistoryStrongNeckExtension`); SC1 (`InteriorCollar` → `SpatialCanonicalWitnessNeckExclusion`,
  `TerminalHornCanonicalNeck` → `HistoryStrongNeckTrigger`); `HistoryStrongNeckClassSupply`; XA4
  (`RetainedCoreHistoryExtendAt` → `…Before`); then `HistoryStrongNeckExtendHorizon`,
  `HistoryStrongNeckDepthInduction`, `ScalarComparisonAtDistance`, `HistoryStrongNeckAncientLimit`.
  NOTE: `TracedRegionBackwardStep.olean` is absent from the shared build (committed module; rebuild it).

## Deviations (with reasons)
1. SC6-c's top-ball hypothesis has `Qup` BEFORE `∀ A` (uniform), `Qlow` after (Finding 1: the depth
   increment `1/(10·Qup)` must be radius-independent because the supply at depth `T` needs all radii).
2. Item 2 is delivered with radius-dependent `Qup(A)` (SC6-f) and only for old points (`hage`); the
   uniform `Qup` and the young case are not plumbing (Finding 2, correction under SC6-f).
3. SC6-d fixes `t₀ = t` (sliver `0`), `ρ = ε`, `qs = qcan`, `Cs = Cq = 1` and requires `∀ n, qcan ≤ R n`
   (B13 wants the threshold bounds for every `n`; the consumer passes to a tail).
4. The per-layer supply is an explicit hypothesis whose conclusion is the witness-level neck statement
   (`∀ W, W.capTubeHasNeckChart ε → ∃ nk, W.alternative = .neck nk`, SC2-b's form), above a floor `c·Rₙ`
   for every `c > 0`, at trace points of depth `≤ T`, premised on the traced region at every depth `≤ T`.
5. Item 3 was elaborated together with its proof (mechanical).

## What the T4′ assembly still lacks after SC6
- **SC5's two bricks** (finite-window splitting; ℝ×N capture): the capture must discharge SC6-c/SC6-d's
  `hsupply` (its conclusion shape is fixed above; its premise gives the traced region at all depths `≤ T`).
  At `T = 0` it is SC2-b at the top slice once the normalized ball sits in SC2-b's compact `B ⊆ hornHalfRange`
  (closeness to `L`, consumer).
- **SC4's line/packaging/converter** (SC4-a/b consume B13's hypothesis list; SC6-d shows that list is
  dischargeable from the T4′ class for `extendAt` sequences — SC4 may call SC6-c/SC6-d's discharges).
- **Uniform top bound `Qup` (NEW, not plumbing)**: `∃ Qup, ∀ A, ∀ᶠ n, R ≤ Qup·Rₙ` on normalized `A`-balls at the
  top slice = global curvature bound of the time-0 blow-up limit (KL §53: complete, `Rm ≥ 0`, necks at all
  high-curvature points ⇒ bounded). The Crossing lane's analogue is XA4's X3 whole-slice bound
  (`CrossingTimeZeroBound.lean`); an S/horn version is needed. SC6-f gives `Qup(A)` and `Qlow(A)`.
- **Young deep horn points** (`Rₙ(τₙ − time last)` bounded): SC6-f needs `hage`; the event-crossing cone
  bounds in the tree carry cap-window hypotheses at fixed `p₀` (DESIGN_S_SUPPLY F4).
- **Base-point typing**: `y n` must be typed in `(Hext n).toHistory.stageAt (t n)` (SC6-d/SC6-f); moving a
  terminal-slab point there is a `generalize (activeStage (t n)) = k; subst` (pattern in SC6-f's proof).
- The final constant bookkeeping (`εcone ≤ min(epsW(SC6-d), coneAccuracy, …)`, `ε₁ ≤ 1/30000`, `εc`/`eps`
  of SC2-e) and the SC2-e contrapositive at the approximant base points.
