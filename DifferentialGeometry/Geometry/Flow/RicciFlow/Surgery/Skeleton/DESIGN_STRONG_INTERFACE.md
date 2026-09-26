# Design: the strong-neck interface (option A of DESIGN_S_SUPPLY, corrected by H13), 2026-09-26

Read-only design on `codex/pc-target-c-psf` @ 88a4eec5a (worktree `D:\differential-geometry-pc3`).
Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.

Every Lean text in §1 and §4 was elaborated with `sorry` bodies in four probes outside the tree
(imports: `Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupply`,
`Surgery/Topology/{HistorySurvivorIncoming, CanonicalNeighborhoodContinuationLeaves,
CanonicalNeighborhoodsThroughSurgeryStrong, PinchingThroughSurgery}`,
`Perelman/StandardSolution/StandardSliceSpatialCanonical`), `LEAN_NUM_THREADS=2`,
`-DmaxSynthPendingDepth=3`. Output: only `declaration uses sorry`. The probes were run against the
committed text of `PoincareEndgame`/`…Strong`; the worktree has other lanes' uncommitted edits
there (see the caveat in (I4)). The two one-line API lemmas
(`spatiallyCanonicalBefore`, `of_threshold_le`) and the cover lemma were PROVED in the probe. All
proposed names are unused library-wide (grep). Probes deleted.

Recommendation up front: **A-lite (§4)**. It needs the same production bricks as A, changes
`PoincareEndgame.lean` only at the S leaf, leaves `UniformDebitSurgeryStepStrong` and every CN
statement untouched, and is provable from the class as it stands (modulo the X-core, which C3c and
C4(C) need anyway). A (additive) is fully specified below as the fallback.

## 0. Failures first

**F1. No proved leaf must be re-proved, in either A (additive) or A-lite.** Checked against the
statements:
- C1 `pinchingThroughSurgery` (`Surgery/Topology/PinchingThroughSurgery.lean:12`): `PinchingThroughSurgery`
  (`CanonicalNeighborhoodInduction.lean:239`) has no canonical hypothesis at all.
- C3a `deepContinuation` (`DeepContinuation.lean:213`) and C3b `capWindowContinuation`
  (`CapWindowContinuationLeaf.lean`): their statements (`CanonicalNeighborhoodContinuationLeaves.lean:146,188`)
  take no spatial clause and output only `CanonicalBoundsOn` (spacetime witnesses at age `≥ τmin`
  plus derivative/gradient). The strong clause is neither consumed nor produced there.
- `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing` (`:284`): unchanged.
- What changes in A are two proved COMPOSITIONS, which are superseded, not edited:
  `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (`CanonicalNeighborhoodsThroughSurgeryStrong.lean:272`)
  and `exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong` (`:192`); plus T5
  (`Contract/UniformDebitSurgeryStepOfFineCutNeckSupply.lean:69`), superseded by T5′. All three stay
  correct. In A-lite only T5 is superseded.
- "C3b′/C3c′ extend C3b/C3c" means at brick level (the bridge L1–L9, the X-core); the committed
  leaf proofs are not touched.

**F2. The strong clause can be ADDITIVE.** Three facts make it so:
1. `StronglyCanonicalBefore ⇒ SpatiallyCanonicalBefore` with the same constants (proved), so the
   spatial clause can stay as is, next to a strong clause with its OWN constant pair `(C1h, C2h)`.
2. The pair must be separate: `C1h` must depend on `ε₁` (F4(b)), while C4 picks `C1s C2s` before
   `ε₁` exists and before `κ`. DESIGN_C4 F3's `θcap`-after-`κ` problem does not arise for the new
   pair, because nothing that feeds `κ` (C2) consumes it.
3. **Pass-2 decoupling.** No CN leaf consumes the strong clause. So the composition first runs the
   existing induction (pass 1: the full class on every slab), then a second induction over `k` for
   the strong clause. The strong leaves therefore get the WHOLE-slab class as hypotheses. They need
   no `…On`/sSup continuation, and there is no compatibility requirement between C4's spatial
   witness and the strong witness (two independent `∃ W`). This dissolves H13's C4 item "strong-
   compatible `W` carried through `Before/On` and the continuation induction".

**F3. `CanonicalBefore`'s window at old points is exactly `R⁻¹`, inside the slab.** The neck
alternative of `CanonicalWitness` is `LocalNeck` (`FiniteHornGeometry.lean:140,251`), whose
`StrongNeck.time_domain` (`:122`) is `Icc (t − R⁻¹) t ⊆ Ico a s`. `τmin` only gates existence. So the
old points give a `HistoryStrongNeck` with `first := k`, the survivor domain being the whole stage
(brick P1). A cap/positive/round old witness makes the clause vacuous, which is allowed.

**F4. Vacuity and degenerate witnesses.**
- (a) *Zero-length window:* impossible. `StrongNeck` has `Q_pos`, the comparison is on normalized
  `[−1, 0]`, and the window has length `R⁻¹ > 0`.
- (b) *`∃ W` satisfied by a trivial `W`:* the clause is vacuous wherever the producer picks a
  non-neck `W`. That is sound only because the non-neck alternatives are geometric:
  - cap = `CapCore` + ε-neck tube at distance `≥ 10000/√R`;
  - positive/round = a whole compact component.

  At the consumer's points (deep in the ℝ×N limit on large balls) none of them exists, so every
  witness is a neck. The consumer MUST prove this (H13: whole-neighbourhood capture, diameter
  `≤ 4C1h/√R`); `C1h` is fixed before `Kfine`.

  The producer, conversely, is FORCED to use cap witnesses near a young glued core:
  - At a point `y` whose spatial ε-neck avoids the non-cylindrical tip, the shorter ε₁-tube
    (`ε ≤ εbar(ε₁) ≤ ε₁`) can still reach the CYLINDRICAL part of the glued ball `capRegion`, which
    is new material with no backward trace.
  - A length margin `ε⁻¹ − ε₁⁻¹` cannot exclude this uniformly. The glued ball has normalized radius
    `≈ r_core·√R_std ≤ r_core·√K(Θ)`, and `Θ` (via `θcap`) is chosen after `κ`, which is after
    `εbar`.
  - So such points must take a cap witness. This needs `C1h ≳ ε₁⁻¹ + r_core·√K(Θ)`, which is legal
    because `C1h` is `∃` after `κ` (F5).
- (c) `gflow` is pinned on the whole window: on `[time first, time k]` by the slab equalities, and on
  `[time k, s)` by `G`. Consistency at event times is `backwardSurvivorSlabMetric_terminal`
  (`HistorySurvivorFlow.lean:132`); H13 accepted the definitions.
- (d) *Full/truncated dichotomy (H13's S1 counterexample):* it does NOT belong in the class
  predicate. §4.3's consumer extends windows of normalized depth 1 at every neck point, and a
  truncated alternative in the class re-creates H12(4). It belongs to the standard-solution brick
  S1′ (§1, probe-elaborated):
  - a neck witness at standard age `σ` is a full `StrongNeck` when `σR ≥ 1`;
  - otherwise it is a `TruncatedNeck` of depth `σR` whose whole ε₁-tube lies outside the core ball
    (`‖·‖ > Dcore`).

  In the history the truncated part is completed by the record's `IncomingBackwardNeck`
  (`GeometricCutoff.lean:58`; its `stageChart`/`crossing` already cross earlier events), which
  yields a FULL window. The whole-tube avoidance is what puts the tube in `backwardSurvivorDomain`
  (`exists_regularCrossing_of_not_mem_capRegion`, `MetricCutCapScalarLower.lean:536`).
- (e) **New: depth deficit.** `IncomingBackwardNeck` certifies depth exactly `r²` (nominal). Near age 0
  the needed pre-gluing depth is `R⁻¹ − (t−T) ≤ r²(1 + Cδ)`, because
  `R ≈ scale·R_std ≥ scale ≥ r⁻²(1 − Λδ)` (`inv_two_mul_sq_lt_static_scale`,
  `CanonicalNeighborhoodContinuationLeaves.lean:88`). The missing `≤ Cδ` normalized time before
  `T − r²` is brick S2e: extend closeness backwards using the class's curvature bounds plus
  time-Lipschitz control. Splicing instead with the previous slab's strong clause would lose accuracy
  at every event, and chains of short slabs compound the loss (DESIGN_C4 F2(i)). Not recommended.

**F5. Quantifier order**, checked against the leaf binders:
- **`ε₁` first.** T4′ is `∃ ε₁`. CN′ (A) or `StrongNecksOfCutoffClass` (A-lite) is
  `∀ ε₁, ∃ εbar(ε₁)`. `εbar` depends only on `ε₁`; its content is `ε ≤ ε₁` (P1's
  `StrongNeck.mono`, `NeckTransportDecoupled.lean:185`), `ε ≤ epsCan`, and the Crossing `εbar`. No
  cap parameter or `B` enters.
- **K1 is retired, and H13's "uniform in κ" is met by an existing theorem.**
  `kappa_canonical_neighborhood` (`Perelman/CanonicalNeighborhood/AncientCanonicalNeighborhood.lean:146`)
  has `C1 C2` before `κ` and outputs a SPACETIME `CanonicalWitness`, whose neck alternative is a
  `StrongNeck`. Under the `∃ W` form the producer takes `W := toSpatial` of that witness after
  transport. It never has to upgrade a given spatial neck, and that upgrade was K1's only purpose.
- **`δmax ρmax εcap` after `qcan`.** C3b′ and C3c′ use the Crossing order (`∀ qcan ≥ q₀, ∃ δmax ρmax
  εcap, ∀ qs`). The splice needs `δmax ≤ δ(ε₁)` and `ρmax ≤ ρ(qcan)`, both chosen later than their
  inputs. In A-lite these constants are `∃` after every class constant and before `p₀` (S's `∃ p₀`
  comes last).
- **`C1h C2h` after `κ`.** This is allowed (F2.2). In C4′ they are `∃` after `κ phi`, because C3c′'s
  `θcap` and S1′'s `C(Θ)` come after `κ`.
- **Threshold.** The strong clause is at `qs` (A) or at `qh ≥ qcan` (A-lite). Lifting uses
  `of_threshold_le` (proved).

## 1. Exact Lean text (A additive; A-lite in §4)

### (I1) predicates (namespaces as in the tree; `open DifferentialGeometry.Geometry.Curvature`)
```lean
namespace ObservedHistory
def HistoryStrongNeck (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (eps : ℝ) (y : (H.stage k).Carrier) (t : ℝ) :
    Prop :=
  ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ k) (hts : H.time first < s)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle)),
    H.time first ≤ t - (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first k hle j hf hl τ) ∧
    (∀ τ ∈ Ico (H.time k) s,
      gflow τ = (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hle)) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
        (RealTimeInterval.closedOpen (H.time first) s hts)) ∧
    ∃ z : H.backwardSurvivorDomain first k hle, z.val = y ∧
      Nonempty (StrongNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
          (RealTimeInterval.closedOpen (H.time first) s hts)) eps z t)
end ObservedHistory

namespace RetainedCoreHistory
variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

def StronglyCanonicalAt (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 : ℝ) (y : (H.stage k).Carrier)
    (t : ℝ) : Prop :=
  ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y, W.capTubeHasNeckChart ε ∧
    ((∃ n, W.alternative = .neck n) → H.toHistory.HistoryStrongNeck k G ε₁ y t)

def StronglyCanonicalBefore (k) {s} (G : (H.stage k).IncomingSlab (H.time k) s)
    (ε ε₁ C1 C2 qcan t₀ : ℝ) : Prop :=
  ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) t₀ → qcan < G.flow.scalar t y →
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t

def StronglyCanonicalOn (k) {s} (G …) (ε ε₁ C1 C2 qcan t₀ η : ℝ) : Prop :=
  ∀ y t, H.time k < t → t₀ ≤ t → t < t₀ + η → t < s → qcan < G.flow.scalar t y →
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t

def StronglyCanonicalWhere (k) {s} (G …) (ε ε₁ C1 C2 qcan : ℝ)
    (S : (H.stage k).Carrier → ℝ → Prop) : Prop :=
  ∀ y t, t ∈ Ioo (H.time k) s → qcan < G.flow.scalar t y → S y t →
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t

def EventSlabsStronglyCanonical (ε ε₁ C1 C2 qcan : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    H.StronglyCanonicalBefore j.castSucc (H.toHistory.event j).incoming ε ε₁ C1 C2 qcan
      (H.time j.succ)

theorem StronglyCanonicalBefore.spatiallyCanonicalBefore … :      -- proved in the probe
    G.SpatiallyCanonicalBefore ε C1 C2 qcan t₀ :=
  fun y t ht hR => (h y t ht hR).imp fun _ hW => hW.1
theorem StronglyCanonicalBefore.of_threshold_le (hq : q ≤ q') … :=  -- proved
  fun y t ht hR => h y t ht (hq.trans_lt hR)
theorem stronglyCanonicalBefore_of_where_cover (h₁ h₂ h₃ : StronglyCanonicalWhere … Sᵢ)
    (hcover : ∀ y t, S₁ y t ∨ S₂ y t ∨ S₃ y t) : H.StronglyCanonicalBefore k G … qcan s  -- proved
theorem stronglyCanonicalWhere_of_canonicalBefore (k G) (hε : ε ≤ ε₁) (hε₁ : ε₁ < 1 / 11)
    (hG : G.CanonicalBefore ε C1 C2 qcan τmin s) :
    H.StronglyCanonicalWhere k G ε ε₁ C1 C2 qcan
      fun y t => τmin ≤ G.flow.scalar t y * (t - H.time k)                -- brick P1
theorem StronglyCanonicalWhere.mono_constants (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') (hC1p : 1 ≤ C1)
    (hC2p : 1 ≤ C2) (h : …Where k G ε ε₁ C1 C2 qcan S) : …Where k G ε ε₁ C1' C2' qcan S  -- P0b
end RetainedCoreHistory
```
`StronglyCanonicalOn` is given for completeness only. By F2.3 neither A nor A-lite uses it.

### (I2) the class conjunct (A)
`CanonicalNeighborhoodsThroughSurgeryStronglyNeckedAt P₀ g₀ (B ε ε₁ Λ : ℝ)` is the body of
`CanonicalNeighborhoodsThroughSurgeryStrongAt` (`…Strong.lean:24`) verbatim, with three changes:
- `C1h C2h` are added after `C1s C2s` in the `∃` list, with `1 ≤ C1h ∧ 1 ≤ C2h`;
- `H.EventSlabsStronglyCanonical ε ε₁ C1h C2h qcan (Fin.last H.eventCount) ∧` is inserted after the
  event-slab `SpatiallyCanonicalBefore` conjunct;
- `H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1h C2h qcan s ∧` is inserted after
  `G.SpatiallyCanonicalBefore ε C1s C2s qcan s ∧`.

```lean
def CanonicalNeighborhoodsThroughSurgeryStronglyNecked (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) : Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 / 11 →
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε Λ : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    CanonicalNeighborhoodsThroughSurgeryStronglyNeckedAt P₀ g₀ B ε ε₁ Λ
```

### (I3) leaves and compositions (A)
C3b′, which extends C3b's bridge, L-bricks and S1′/S2/S2e/S3 (full text):
```lean
def StrongCapWindowContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 / 11 →
  ∃ εbar : ℝ, 0 < εbar ∧ εbar ≤ ε₁ ∧
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε ≤ εbar →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0) (C1s C2s Cs : ℝ),
    1 ≤ C1 → 1 ≤ C2 → 0 < τmin → 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (Dcap θcap : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
    0 < Dcap → θcap < 1 →
  ∃ (C1h C2h Rcap q₀ : ℝ) (mcap : ℕ), 1 ≤ C1h ∧ 1 ≤ C2h ∧ Dcap + 1 < Rcap ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory P₀) (hH : H.InCutoffClass g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.succ →
        H.EventSlabsDerivative Ctime qcan j.succ →
        H.EventSlabsGradient Cgrad qcan j.succ →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.succ →
        H.NoncollapsedBefore κ ε (H.time j.succ) →
        H.EventSlabsStronglyCanonical ε ε₁ C1h C2h qs j.castSucc →
        H.StronglyCanonicalWhere j.castSucc (H.toHistory.event j).incoming ε ε₁ C1h C2h qs
          fun y t => (H.toHistory.event j).incoming.flow.scalar t y *
              (t - H.time j.castSucc) < τmin ∧
            H.CapWindowPoint records j.castSucc y t Dcap θcap) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        G.CanonicalBefore ε C1 C2 qcan τmin s → G.DerivativeBoundBefore Ctime qcan s →
        G.GradientBoundBefore Cgrad qcan s → G.SpatiallyCanonicalBefore ε C1s C2s qs s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀) →
        H.EventSlabsStronglyCanonical ε ε₁ C1h C2h qs (Fin.last H.eventCount) →
        H.StronglyCanonicalWhere (Fin.last H.eventCount) G ε ε₁ C1h C2h qs
          fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < τmin ∧
            H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap
```
**C3c′ `StrongCrossingContinuation`** extends the X-core of C3c/C4(C). It is C3b′ with two changes:
- the binder line after `κ phi` is `∃ (Dcap θcap C1h C2h q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1
  ∧ 1 ≤ C1h ∧ 1 ≤ C2h ∧ 0 < q₀ ∧` (no `∀ Dcap θcap`, no `Rcap`), with `Dcap ≤ p₀.modelRadius`;
- both regions are `… < τmin ∧ ¬ H.CapWindowPoint records … y t Dcap θcap`.

**C4′ `StrongCanonicalContinuation`** is the composite (C4 extended with old points P1). It is C3b′
with these changes:
- no `Dcap θcap` inputs; after `κ phi` it reads `∃ (C1h C2h q₀ Dcap : ℝ) (mcap : ℕ), 1 ≤ C1h ∧
  1 ≤ C2h ∧ 0 < q₀ ∧ 0 < Dcap ∧`;
- no `records` binders;
- the event conclusion is
  `H.StronglyCanonicalBefore j.castSucc (H.toHistory.event j).incoming ε ε₁ C1h C2h qs (H.time j.succ)`;
- the terminal conclusion is `H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1h C2h qs s`.

```lean
theorem strongCanonicalContinuation_of_capWindow_of_crossing (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) (hcap : StrongCapWindowContinuation P₀ g₀)
    (hcross : StrongCrossingContinuation P₀ g₀) : StrongCanonicalContinuation P₀ g₀
  -- P1 on `τmin ≤ R(t−a)`; cover by le_or_lt / by_cases CapWindowPoint (Dcap := Crossing's,
  -- fed to hcap); C1h := max, via mono_constants; ε ≤ min εbar's; Dcap := max Dx Rcap. 150–250 lines.

theorem canonicalNeighborhoodsThroughSurgeryStronglyNecked_of_leaves
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hpinch : PinchingThroughSurgery P₀ g₀) (hnon : NoncollapsingThroughSurgery P₀ g₀)
    (hcont : CanonicalNeighborhoodContinuation P₀ g₀)
    (hspat : SpatialCanonicalContinuation P₀ g₀)
    (hstrong : StrongCanonicalContinuation P₀ g₀) :
    CanonicalNeighborhoodsThroughSurgeryStronglyNecked P₀ g₀
  -- pass 1 = the :277–:352 induction copied; pass 2 = Fin.induction calling hstrong;
  -- hstrong's `∃ q₀` is taken after κ and folded into `qfloor := max q₄ q₅`. 250–400 lines.
```
**S′ `UniformDebitSurgeryStepStrongNecked P₀ g₀`** is `UniformDebitSurgeryStepStrong` (`…Strong.lean:124`)
with these changes:
- prefix `∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 11 ∧`;
- `C1h C2h` after `C1s C2s` in the `∀` list, with `1 ≤ C1h → 1 ≤ C2h →`;
- the hypothesis `H.EventSlabsStronglyCanonical ε ε₁ C1h C2h qcan (Fin.last H.eventCount) →` after
  the event spatial hypothesis;
- `H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1h C2h qcan s →` after
  `G.SpatiallyCanonicalBefore ε C1s C2s qcan s →`.

T4′ `FineCutNeckSupplyStrong` is DESIGN_S_SUPPLY §1(A) verbatim, with two constant renames:
- `EventSlabsStronglyCanonical ε ε₁ C1s C2s qcan (Fin.last _)`;
- `H.StronglyCanonicalBefore (Fin.last _) G ε ε₁ C1s C2s qcan s`.

```lean
theorem uniformDebitSurgeryStepStrongNecked_of_fineCutNeckSupplyStrong (P₀ g₀)
    (hfine : FineCutNeckSupplyStrong P₀ g₀) : UniformDebitSurgeryStepStrongNecked P₀ g₀
theorem exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrongNecked
    (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric)
    (hstep : UniformDebitSurgeryStepStrongNecked P₀ g₀)
    (hcn : CanonicalNeighborhoodsThroughSurgeryStronglyNecked P₀ g₀) :
    Nonempty (PoincareControlledExtinction P₀.toClosedOrientedManifold g₀)
  -- ε₁ from hstep, εbar from hcn ε₁, then the :192 proof plus two threshold lifts.
theorem smoothPoincareConjecture_of_uniformDebitSurgeryStepStrongNecked
    (hstep : ∀ P₀ g₀, UniformDebitSurgeryStepStrongNecked P₀ g₀)
    (hcn : ∀ P₀ g₀, CanonicalNeighborhoodsThroughSurgeryStronglyNecked P₀ g₀) :
    smoothPoincareConjecture.{u}
```
Brick statement S1′ (probe-elaborated). `TruncatedNeck` is `StrongNeck`
(`FiniteHornGeometry.lean:122`) with a field `depth ∈ (0,1]`, with
`time_domain : Icc (t − depth·R⁻¹) t ⊆ D.carrier`, and with the comparison on `Icc (−depth) 0`.
```lean
theorem StandardSolution.exists_spatialCanonicalWitness_strong_or_truncated_neck
    {eps eps₁ Θ Dcore : ℝ} (heps : 0 < eps) (hle : eps ≤ eps₁) (hsmall : eps₁ < 1 / 11)
    (hΘ : Θ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ Icc 0 Θ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps ∧
          ((∃ n, W.alternative = .neck n) →
            Nonempty (StrongNeck S.val.toSolutionOn eps₁ x t) ∨
            ∃ nk : TruncatedNeck S.val.toSolutionOn eps₁ (t * S.val.toSolutionOn.scalar t x) x t,
              t * S.val.toSolutionOn.scalar t x < 1 ∧
              ∀ z ∈ Set.univ ×ˢ Set.Ioo (-eps₁⁻¹) eps₁⁻¹, Dcore < ‖nk.map z‖)
```
`C` depends on `(eps, eps₁, Θ, Dcore)`. The cap alternative is chosen at every point whose
ε₁-tube would meet `‖·‖ ≤ Dcore` (F4(b)). `Dcore` is the model radius of `capRegion`.

### (I4) `Surgery/Skeleton/PoincareEndgame.lean` edits (A)
Imports: add the new modules (strong leaves, strong assembly, T5′). Sorry leaves go 7 → 9:
- S is replaced by T4′;
- C3b′ and C3c′ are added;
- C2 ×4, C3c and C4 stay.
```lean
theorem fineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ := by
  sorry
theorem uniformDebitSurgeryStepStrongNecked (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrongNecked P₀ g₀ :=
  uniformDebitSurgeryStepStrongNecked_of_fineCutNeckSupplyStrong P₀ g₀ (fineCutNeckSupplyStrong P₀ g₀)
theorem strongCapWindowContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongCapWindowContinuation P₀ g₀ := by
  sorry
theorem strongCrossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongCrossingContinuation P₀ g₀ := by
  sorry
theorem canonicalNeighborhoodsThroughSurgeryStronglyNecked (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) : CanonicalNeighborhoodsThroughSurgeryStronglyNecked P₀ g₀ :=
  canonicalNeighborhoodsThroughSurgeryStronglyNecked_of_leaves P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (noncollapsingThroughSurgery P₀ g₀)
    (canonicalNeighborhoodContinuation P₀ g₀) (spatialCanonicalContinuation P₀ g₀)
    (strongCanonicalContinuation_of_capWindow_of_crossing P₀ g₀
      (strongCapWindowContinuation P₀ g₀) (strongCrossingContinuation P₀ g₀))
theorem smoothPoincareConjecture_holds : smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_uniformDebitSurgeryStepStrongNecked
    uniformDebitSurgeryStepStrongNecked canonicalNeighborhoodsThroughSurgeryStronglyNecked
```
**Caveat (worktree, uncommitted, another lane).** `PoincareEndgame.lean` and
`CanonicalNeighborhoodsThroughSurgeryStrong.lean` currently add `[SimplyConnectedSpace P₀.Carrier]`
to `noncollapsingThroughSurgery` and `canonicalNeighborhoodsThroughSurgeryStrong`. If that lands, A
must thread the same instance:
- through `canonicalNeighborhoodsThroughSurgeryStronglyNecked(_of_leaves)`;
- through the `hcn` binder of `smoothPoincareConjecture_of_uniformDebitSurgeryStepStrongNecked`.

A-lite is unaffected, because it touches only the S leaf.

Also delete `theorem uniformDebitSurgeryStepStrong … sorry`. `canonicalNeighborhoodsThroughSurgeryStrong`
may stay (it is valid) or be deleted. `crossingContinuation`, `spatialCanonicalContinuation` and
the C2 leaves are unchanged.

## 2. Per-leaf obligations (H13 items) and bricks

| Leaf | H13 obligation | Brick(s) |
|---|---|---|
| C3b′ | full/truncated dichotomy | S1′ |
| C3b′ | whole-tube survival: tube outside `capRegion` ⇒ in `backwardSurvivorDomain`; quantitative splice across the gluing time (`IncomingBackwardNeck` depth `r²`, not `R⁻¹`) | S2, S2e |
| C3b′ | chart transport through `Ξ` | S2 |
| C3b′ | high-curvature threshold, cap-exclusion trigger, chart compatibility on the old slab | S3 |
| C3c′ | K1 uniform in κ: RETIRED (F5); remaining: history E3 | X1′ |
| C4′ | old-point embedding `first := k` | P1 |
| C4′ | strong-compatible `W` through `Before/On` and the induction | dissolved (F2.3) |
| S (consumer) | whole-neighbourhood capture at each depth; cap and compact-component exclusion (domain `≤ 4C1h/√R` in the ℝ×N limit) | T3A-1, T3A-2 |
| S (consumer) | stepwise extension with event endpoints; uniform subsequence (`TerminalScalarAncientLimit.lean:475` only assumes windows) | T3A-2 |

The S3 threshold is `scale ≥ (n+1)qcan` via `ρmax`; see DESIGN_CROSSING_ASSEMBLY F8.

| Brick | Content | Suppliers (`file:line`) | Lines |
|---|---|---|---|
| P0 | `HistoryStrongNeck` API: `backwardSurvivorDomain k k = ⊤`, restrict a `StrongNeck` to the survivor-domain type, mono in `eps`, threshold | `HistorySurvivorDomain.lean:73`, `HistorySurvivorFlow.lean:38,132,143`, `NeckTransportDecoupled.lean:185,223` | 200–400 |
| P0b | `mono_constants` (`enlargeConstants` keeps `.neck`) | `SpatialCanonicalWitness.lean:165,201` | 60–120 |
| P1 | old points ⇒ `HistoryStrongNeck` (`first := k`) | `FiniteHornGeometry.lean:122,140`, `SpatialCanonicalWitnessProjection.lean:92`, `CanonicalCapCollar.lean:26` | 150–300 |
| S1′ | standard-solution dichotomy + tip-distance cap choice | `StandardSliceSpatialCanonical.lean:666`, `StandardFarRegion.lean:400`, `StandardTerminalBlowup.lean:61`, `StandardLifetime.lean:81` | 800–1500 |
| S2 | splice with `IncomingBackwardNeck` + whole-tube survival + chart transport | `GeometricCutoff.lean:58`, `CutoffRecordEventExtension.lean:91,177`, `IncomingBackwardNeckIsometries.lean:79,192`, `HistorySurvivorIncoming.lean:30–129`, `MetricCutCapScalarLower.lean:536`, `CapWindowStandardComparison.lean:20`, `BackgroundJetTransfer.lean:548`, `NeckTransportDecoupled.lean:397` | 1000–1800 |
| S2e | depth deficit `≤ Cδ` before `T − r²` from class curvature bounds | `Estimates/InitialMetricTimeBounds.lean:100`, `Estimates/Shi/Derivatives/TerminalBall.lean:373` | 300–600 |
| S3 | threshold/trigger/chart compatibility at the splice | `CanonicalNeighborhoodContinuationLeaves.lean:88,136` | 300–600 |
| C3b′ | assembly | the bridge of `CapWindowContinuationLeaf.lean` | 300–500 |
| X1′ | identify the X-core's common flow (`TracedRegion.lean:598,722`) with `backwardSurvivorSlabMetric` on `U ⊆ backwardSurvivorDomain`, then restrict its `StrongNeck` | X-core (shared, not counted), `HistorySurvivorFlow.lean:619,683` | 300–700 |
| C3c′ | assembly on the X-core (`θ := τmin`; `θcap ≥ 1/(1+c₀)` via `StandardTerminalBlowup.lean:61`) | DESIGN_CROSSING_ASSEMBLY X5, DESIGN_C4 §3 | 300–600 |
| C4′ + I (A) | composite, `_of_leaves` (pass 1 copy + pass 2), S′, T5′, extinction | `…Strong.lean:192,272`, T5 | 700–1200 |
| T3A + T4′ | consumer (unchanged from DESIGN_S_SUPPLY) | DESIGN_S_SUPPLY §3 | 2900–5800 |

Totals:
- production (P0–C3c′): 3.7–7.0k lines;
- interface: 0.7–1.2k (A) or 0.4–0.75k (A-lite);
- consumer: 2.9–5.8k.

Grand total 7.0–14.0k lines, excluding the X-core.

Order:
1. P0, P0b, P1, and the skeleton commit.
2. S1′.
3. S2, S2e, S3.
4. C3b′.
5. X1′ and C3c′ after the X-core.
6. T3A after DESIGN_MAXWINDOW M2.

## 3. Review prompt (A package, one statement)

> 请审查一个接口包（Lean 全文见 `Surgery/Skeleton/DESIGN_STRONG_INTERFACE.md` §1，已在探针中通过类型检查）。定义：`HistoryStrongNeck k G ε₁ y t`——存在 `first ≤ k` 与生存域 `backwardSurvivorDomain first k` 上的流 `gflow`，在各中间片等于 `backwardSurvivorSlabMetric`、在当前片等于 `G`、满足 `IsSolutionOn`，且在 (y,t) 有整管位于生存域内、窗口 `[t−R⁻¹,t]` 的 `StrongNeck ε₁`；`StronglyCanonicalBefore … ε ε₁ C1h C2h qcan`——每个 `R>qcan` 的点存在空间典范见证 W，且 W 为颈时即有 `HistoryStrongNeck`（"∃ W" 形式，常数 C1h C2h 独立于空间类的 C1s C2s）。类的新合取项为事件片与终片的强子句（加法式：空间子句与已证叶 C1、C3a、C3b 不变）。消费者 S′ = T4′（∃ε₁；∀p₀ 无约束）。生产者：C4′ 组合 = 旧点 P1（`CanonicalBefore` 的 `LocalNeck` 窗口恰为 R⁻¹，first:=k）+ C3b′（年轻帽窗点：标准解 S1′ 全/截断二分，截断时整条 ε₁ 管在核球外，由记录的 `IncomingBackwardNeck` 跨粘接补全窗口，深度亏量 ≤Cδ 由类曲率界补）+ C3c′（年轻非帽窗点：X-core 在跨事件公共流上给出时空典范见证；κ 一致性由 `kappa_canonical_neighborhood` 的 C1 C2 先于 κ 提供，故不需 K1）。组合采用两遍归纳：先证旧类于全部片，再归纳证强子句，故强叶取整片类为假设。量词序：∀ε₁ ∃εbar(ε₁) ∀B ε … ∀κ ∃C1h C2h q₀ Dcap，∀qcan ∃δmax ρmax εcap，∀qs∈[qcan,Cs qcan] ∀p₀。
> 请回答：(1) 真值与空洞性："∃W" 是否可被平凡见证满足而使 T4′ 失效（消费者须在 ℝ×N 极限中排除帽/紧分支）？C1h 依赖 ε₁ 是否合法？(2) 量词序有无隐藏循环（εbar 仅依赖 ε₁；C1h 在 κ 之后）？(3) 已证叶 C1/C3a/C3b 与已证组合是否确实无需重证？(4) 反例：(a) 标准解远柱区小 t（t·R<1）——截断+入射颈补全是否总给出全窗口？(b) 颈管在 (t−R⁻¹,t) 内穿过一次后续手术（管的一部分为新粘帽材料）——生产者改选帽见证是否总可行（需 C1h ≳ ε₁⁻¹+r_core·√K(Θ)，C1h 在 κ、θcap 之后）？(c) 龄 ∈(θcap,1) 的帽窗点——是否由 X-core 分支覆盖（`c₀/(1−σ) ≤ R_std` 使 σ>θcap≥1/(1+c₀) 时窗口不跨粘接）？(d) 深度亏量 S2e 是否真实、修法是否充分？

## 4. Option A-lite (no CN interface change). RECOMMENDED

The frozen class and every CN leaf stay as they are. The strong clause is a THEOREM from the class as
S receives it, consumed only by S. It is frozen as one new sorry leaf, `strongNecksOfCutoffClass`.

### 4.1 Statement (probe-elaborated)
```lean
def StrongNecksOfCutoffClass (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 / 11 →
  ∃ εbar : ℝ, 0 < εbar ∧ εbar ≤ ε₁ ∧
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε ≤ εbar →
  ∀ (C1 C2 C1s C2s qcan τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ) (phi : ℝ → ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < κ →
    Perelman.AdmissiblePinchingFunction phi →
  ∃ (C1h C2h qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    1 ≤ C1h ∧ 1 ≤ C2h ∧ qcan ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
    p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
    δbound ≤ δmax → ρbound ≤ ρmax →
  ∀ (H : RetainedCoreHistory P₀) (hH : H.InCutoffClass g₀ B p₀ δbound ρbound),
    H.EventSlabsPinched phi →
    H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
    H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
    H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
    H.EventSlabsSpatiallyCanonical ε C1s C2s qcan (Fin.last H.eventCount) →
    H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
    H.EventSlabsStronglyCanonical ε ε₁ C1h C2h qh (Fin.last H.eventCount) ∧
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      G.CanonicalBefore ε C1 C2 qcan τmin s → G.DerivativeBoundBefore Ctime qcan s →
      G.GradientBoundBefore Cgrad qcan s → G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
      (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
        H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀) →
      H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1h C2h qh s

theorem uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hpinch : PinchingThroughSurgery P₀ g₀)
    (hstrong : StrongNecksOfCutoffClass P₀ g₀) (hfine : FineCutNeckSupplyStrong P₀ g₀) :
    UniformDebitSurgeryStepStrong P₀ g₀
```
There are no floors on `C1 … τmin Ctime Cgrad`: the output constants are the leaf's own. The class
threshold is the single `qcan` that S receives; the spatial clause is at `qcan` too, i.e.
`qs = qcan`, `Cs = 1`.

**T5-lite binder chain.** It is feasible; every step is an upper/lower bound combined by
`min`/`max`:
1. `hfine` gives `ε₁ eta εcone`, and `hstrong ε₁` gives `εbar₁`.
2. `∀ B εbar`: `hpinch B` gives `phi δP ρP εP`. `Λ := c`, as in T5.
3. `∀ Ctime`: `ε := min εbar (min εF (min εcone εbar₁))`. This is T5's `ε` with one more `min`.
4. `∀ C1 … a₀`: `hstrong` gives `(C1h C2h qh δh ρh εh Dh mh)`.
5. `hfine κ C1h C2h qh a₀ Ctime Cgrad ε` gives `∀ εc ∃ Kfine`. Then F\* runs as in T5, with `qh` in
   the factory's threshold slot; the class lifts by `of_threshold_le`.
6. `p₀`:
   - `modelRadius := max … Dh`;
   - `modelAccuracy := min … (min εh εP)`;
   - `modelOrder := max … mh`;
   - `δbound := min … (min δh (min δP (2c)⁻¹))`;
   - `ρbound := min … (min ρh ρP)`.
7. Inside `∀ H`:
   - `InCutoffClass` from `hend`, `hhor`, records, and `c·δbound ≤ 1/2`
     (`CutoffParameters.recenterConstant_mul_le_half`, `…Strong.lean:262`);
   - pinching from `hpinch`;
   - the strong clauses from `hstrong`, feeding T4′.

`Kfine` comes before `p₀`, as T4′ requires.

Extra cost over T5: 150–300 lines.

### 4.2 `PoincareEndgame.lean` edit (A-lite)
Only the S leaf changes. Sorry leaves go 7 → 8. Add an import for the T5-lite module (which also
defines `FineCutNeckSupplyStrong` and `StrongNecksOfCutoffClass`). Replace
`theorem uniformDebitSurgeryStepStrong … := by sorry` by:
```lean
theorem fineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ := by
  sorry
theorem strongNecksOfCutoffClass (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ := by
  sorry
theorem uniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ :=
  uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (strongNecksOfCutoffClass P₀ g₀) (fineCutNeckSupplyStrong P₀ g₀)
```
Nothing else changes: the CN assembly, `smoothPoincareConjecture_holds` and the statements of C2,
C3c and C4. `strongNecksOfCutoffClass` may later be split into sorry sub-leaves on the same cover
(P1 old / cap-window / crossing), with the proved cover lemma `stronglyCanonicalBefore_of_where_cover`.

### 4.3 The lead's case split, against the definitions
- **(i) Old points, `τmin ≤ R(t−a)`.** YES. The window is `R⁻¹` (not `τmin/R`), and it lies in the
  slab (F3). So this is a `HistoryStrongNeck` with `first := k` (brick P1, 150–300 lines, needs
  `ε ≤ ε₁`).
- **(ii) Young cap-window points, `CapWindowPoint Dcap θcap` and age `< τmin`.** These are exactly
  H13's C3b obligations, now inside S's lane: S1′, S2, S2e, S3 (2.4–4.5k).
  - The `Θ` of the cap-window comparison is `max θcap 1/2`.
  - Its `p₀` requirements (`R m₀ ζ₀ δ₀`, `CapWindowStandardComparison.lean:20`) become
    `Dh mh εh δh`.
  - S's `∃ p₀` comes after them, so they are met. This is where A-lite escapes DESIGN_S_SUPPLY
    F3/F4: those failures came from `Kfine`-before-`p₀` INSIDE T4. Here the cap-parameter binders
    sit in `StrongNecksOfCutoffClass`, which precedes `p₀`, while T4′ still sees no `p₀` constraint.
- **(iii) Young unscathed points, age `< τmin` and `¬CapWindowPoint`.**
  - Backward trace + the previous slab's clause does NOT work: every splice loses accuracy, and
    short slabs chain the losses (DESIGN_C4 F2(i)). The recursion is well-founded over `k`
    (finitely many events), so the problem is accuracy, not termination.
  - The route that works is exactly the Crossing machinery:
    - B5 `exists_isTracedRegion_or_capWindowPoint_at_scale` (`TracedRegionOrCapWindow.lean:665`)
      traces across ANY number of events at normalized depth `T/R`;
    - W1's depth schedule; B6b′ survivor maps (`TracedRegionAncientLimitData.lean:321`) and B13
      (`TracedRegionAncientLimitScalarBound.lean:42`) build the limit;
    - B8 (`AncientLimitCanonicalWitness.lean:117`) or `kappa_canonical_neighborhood` gives a
      SPACETIME witness, transported back to the traced common flow;
    - X1′ turns that flow into a `backwardSurvivorSlabMetric` window.
  - No `hlong` is needed: depth is normalized and slab lengths never enter (X0 handles `t < η₀`,
    DESIGN_CROSSING_ASSEMBLY F2).
  - The X-core is shared with C3c and C4(C). A-lite needs it in its C4(C) form (witness on the
    cross-event flow, `θ := τmin`); C3c only needs the in-slab corollary.
- **(iv) Binder order, `τmin` versus `Θ(p₀)`.**
  - `τmin` is CN's `∃`, before `C1s` and `κ`. In S it is a `∀`, and S cannot choose it. It does not
    need to.
  - The two ages use different normalizations:
    - the young condition is `R(t−a) < τmin`, with `τmin ≥ τ₀ ≳ δ⁻¹` large;
    - `CapWindowPoint` uses `(t−T_j)·scale ≤ θcap < 1`.
  - Points with standard age `σ ∈ (θcap, 1)` are young in the `τmin` sense and are NOT cap-window
    points, so they fall in branch (iii), the X-core. There is no uncovered gap: the cover is
    `le_or_lt` plus `by_cases CapWindowPoint`.
  - What makes (iii) sound there is `c₀/(1−σ) ≤ R_std` (`StandardTerminalBlowup.lean:61`). With
    `θcap ≥ 1/(1+c₀)`, which the X-core's `∃ θcap` may choose, such a point has `R(t−T_j) ≳ 1`, so
    its window does not cross its own gluing. B5 handles this internally with its `Θ` close to 1.

### 4.4 Verdict
**Is A-lite provable from the class as it stands?** Yes, conditionally on the X-core in its C4(C)
form, exactly as C4 already is:
- (i) is immediate;
- (ii) uses only records plus the class (derivative and curvature bounds for S2e);
- (iii) uses only the class on the whole slab. The full-slab class is a stronger hypothesis than the
  Crossing leaf's `Before t₀`, so the X-core's contradiction argument applies unchanged. The floors
  of the Crossing leaf (`Ctime₀`, `τ₀`, `C1₀`) protect its OUTPUT constants; `StrongNecksOfCutoffClass`
  outputs its own constants, so it needs no floors. **This is the point to review.**

Shared with A: P0, P0b, P1, S1′, S2, S2e, S3, X1′, the X-core, and T3A/T4′. All production bricks
are identical.

What A-lite saves:
- no `…StronglyNeckedAt`/CN′, S′, pass-2 `_of_leaves`, or new extinction composition
  (0.4–0.6k lines);
- no change to the frozen CN/S statements, and 8 leaves instead of 9;
- C3c's and C4's statements stay frozen; C3b is not re-opened.

What A-lite costs:
- the C3b′ and C3c′ production moves into S's lane, which now depends on the X-core (in A the
  dependence sat in CN's C3c′ leaf; the total is the same);
- T5-lite (150–300 lines).

The accounting is otherwise equal. Pick A-lite.

### 4.5 Second review prompt (A-lite, single statement)

> 请审查单一命题 `StrongNecksOfCutoffClass`（Lean 全文见 `DESIGN_STRONG_INTERFACE.md` §4.1，已通过类型检查）：∀ε₁<1/11 ∃εbar≤ε₁，∀B ε≤εbar，∀ 类常数 C1 C2 C1s C2s qcan τmin Ctime Cgrad κ 与可容许 phi（无下界要求），∃ C1h C2h qh≥qcan 与 p₀ 约束 (εcap Dcap mcap δmax ρmax)，∀ 满足约束的 p₀ 与 InCutoffClass 中、带 pinching 且在全部片上满足现有类（CanonicalBefore/导数/梯度/空间典范于 qcan、NoncollapsedBefore）的历史：事件片与终片均满足 `StronglyCanonicalBefore ε ε₁ C1h C2h qh`（每个 R>qh 的点有空间见证，颈时即有跨事件生存流上的 `HistoryStrongNeck ε₁`）。它由 S 消费：S 在选 p₀ 之前满足其约束，再调用 T4′（T4′ 本身无 p₀ 约束），故 CN 接口与 S 陈述均不变。证明路线：旧点（R(t−a)≥τmin）取 `CanonicalBefore` 的 LocalNeck（窗口 R⁻¹ 在片内）；年轻帽窗点用标准解全/截断二分 + 记录的 `IncomingBackwardNeck` 补全窗口（深度亏量 ≤Cδ 由类曲率界补）；年轻非帽窗点用 Crossing 的 X-core（B5 跨任意多事件的追踪、祖先极限、`kappa_canonical_neighborhood` 的 κ 一致时空见证、回运至生存流）。
> 请回答：(1) 在类常数无下界、仅以全片类为假设时此命题是否为真？X-core 的矛盾论证是否需要 Crossing 叶的 floors 或"t₀ 前"归纳结构？(2) 龄 ∈(θcap,1) 的帽点、短片链、粘接后立即的远柱区点能否构成反例？(3) 与"在 CN 接口加强类"（方案 A）相比，是否丢失任何必要信息（例如前一片的强子句）？
