# Design: the S leaf's fine-cut-neck supply (the T4 fork), 2026-09-26

Read-only design on `codex/pc-target-c-psf` (worktree `D:\differential-geometry-pc3`, HEAD 1640a9e11,
T5 uncommitted). Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.

Every statement in §1–§2 was elaborated with `sorry` bodies in one probe outside the repo. The probe
imported `Surgery/Contract/UniformDebitSurgeryStepOfFactory`, `Surgery/Topology/HistorySurvivorIncoming`,
`Surgery/Topology/CanonicalNeighborhoodContinuationLeaves` and
`Perelman/CanonicalNeighborhood/AncientCanonicalNeighborhood`. It ran with `LEAN_NUM_THREADS=2` and
produced only `declaration uses sorry`. The probe has been deleted. All proposed names are unused
library-wide.

## 0. Failures first: H12 checked against the Lean

**F1. The `Dbig`/`εcut` dependence is genuine. Option (C) is dead.**

The chain, file by file:
1. `Surgery/StandardCap/StaticThresholds.lean:26`, `exists_uniform_positiveCoordinate_static_estimates`.
   For the model radius `D`, every admissible `δ ≤ δ₀(D, m, ε)` must satisfy
   `hfit : D + 1 ≤ transitionEnd + δ⁻¹`. The cut neck has to be long enough to hold the model ball of
   radius `D`.
2. This `δ₀` passes unchanged through `RecenteredStaticPreparation`, `StaticFamilyVolumePreparation`,
   `FiniteMetricEventVolume` and `FiniteMetricEventDebit`, where it is shrunk by constants.
3. `Surgery/Contract/HornFineCutoffRecord.lean:188`: `ε₀ := min (εbase/2) (…)`. By
   `exists_precision_order_compatible` (`Contract/HornMetricEvent.lean:104`), `εbase ≤ δ`.
4. `Contract/PoincareHornCutoffRecordOfFineCutNecks.lean:188` sets `ε₀ := min εfactory …`, with the
   factory called at `Dcap := Dbig` (`:404`). At `:720`, `εcut := min (min εcoarse eta) ε₀`.

Result: `εcut < 1/(2(Dbig + 1 − transitionEnd))`.

Now suppose some variant of the X-core had `Rrad(εc)` (the εc-first form of `DESIGN_B13` F6). An εc-neck
has length `εc⁻¹`, so it needs control on a normalized ball of radius `A ≳ εc⁻¹`. B3e's contradiction
takes `Rrad = Dcap = transitionEnd + 1 + n` (`Surgery/Topology/BoundedCurvatureAtDistanceSliceTerminal.lean:249`,
proof at `:290`). When the cap scale is comparable to `R(x)`, this forces `Rrad(εc) ≳ A ≳ εc⁻¹`.

Then the two requirements `Dbig ≥ Rrad(εcut) ≥ εcut⁻¹` and `εcut⁻¹ > 2(Dbig + 1 − transitionEnd)`
give `Dbig < 2·transitionEnd − 2`. But F\* requires `Dbig ≥ Dtrace + 1 > 64·transitionEnd`.

So no reordering of F\* can remove the circularity: `εcut ≲ 1/Dbig` is geometric (`hfit`), and it is
not an artefact of the order of the binders.

**F2. `Kfine` does precede `p₀` in T4. Reordering is harmless, but it does not help.**

What the statements say:
- `FineCutNeckSupply` (`Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupply.lean`) reads
  `∃ Rrad ζ₀ δ₀ ρ₀ m₀, ∀ εc, ∃ Kfine, ∀ p₀ δbound ρbound, ∀ H …`.
- In T5 every field of the `p₀` it builds (`fixed`, `Dbig`, `m`, `accuracy`, `c`, `ρbound`) and
  `δbound` are fixed before the call `hsupply (min εcut (1/4))`.

So T4 could be weakened to `∀ p₀ δbound ρbound, ∀ εc, ∃ Kfine(p₀, εc)`. T5 would still elaborate after
the `obtain ⟨p₀, …⟩` block is moved above that call.

This does not help, because in either order the T3 contradiction sequence has cap parameters that
are bounded below by fixed thresholds. The X-core needs `modelRadius → ∞` along its sequence. With
`Kfine` depending on `p₀`, that sequence runs at one fixed `p₀`.

**F3. The Crossing core outputs no backward window at a fixed `p₀`. Its window is an INPUT.**

The composed ancient-limit headline (`DESIGN_B6D_GLUE.md` B13,
`exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`) takes
`htraced : ∀ A T, ∃ K, ∀ᶠ n, isTracedRegion …` (`Surgery/Topology/TracedRegion.lean:76`) as a hypothesis.
- In the Crossing leaf, `htraced` comes from the maximal window (DESIGN_MAXWINDOW M2–M4) together with
  B3e and B5. All three need the cap-window exclusion at `Dₙ → ∞` and `θcapₙ ↑ 1`.
- The leaf can supply this because `CrossingContinuation` has `∃ Dcap θcap … εcap` of its own
  (`CanonicalNeighborhoodContinuationLeaves.lean:232`).
- S has no such freedom.

The output is a bounded ancient limit. A strong neck at a traced point would need two further steps:
- `kappa_canonical_neighborhood` (`Perelman/CanonicalNeighborhood/AncientCanonicalNeighborhood.lean:146`,
  whose neck alternative is `LocalNeck`, i.e. a `StrongNeck`);
- a history version of the E3 transport (`CanonicalAlternativeComparisonTransport.lean:18` is single-slab;
  see `DESIGN_CROSSING` F4).

So the X-core produces strong necks only inside its own contradiction argument, and not at a fixed `p₀`.
H12 item (3) is confirmed.

**F4. Late-age caps (normalized age in `(Θ(p₀), 1]`) cannot be handled by the cap-window machinery at a
fixed `p₀`.**

`exists_standard_comparison_of_cap_window_trace` (`Surgery/Topology/CapWindowStandardComparison.lean:20`)
has the order `∀ Θ < 1, ∃ P Creset Cbirth, ∀ D ε η N, ∃ R m₀ ζ₀ δ₀, ∀ p₀, R ≤ modelRadius → accuracy ≤ ζ₀`.
- The requirements on `p₀` grow as `Θ ↑ 1` and as the output accuracy `ε ↓ 0`.
- C3b's L-bricks inherit the same order.
- The only `p₀`-free information at a late-age cap point is the class (spatial witnesses, derivative
  and gradient bounds, κ). None of it gives the flow backwards.

Pushing `R(x)/Q_cap → ∞` does not escape this. By `R_std ≤ Creset/(1−θ)` it forces `θ → 1`, which is
exactly F4's band.

**F5. H12's `recenterConstant·δbound ≤ 1/2` gap and `DESIGN_B13` F8 (the `−3/a₀` floor) are T2-only.**
Under the recommended option T2 is retired, and both disappear. `InCutoffClass`
(`Surgery/Topology/CanonicalNeighborhoodInduction.lean:165`) already carries the first conjunct if it
is ever needed.

**F6. New trap: the trigger of the strong clause must not be a spatial εs-neck with εs ≪ ε₁.**

A clause of the form "spatial εs-neck ⇒ strong ε₁-neck" cannot be iterated backwards:
- after one window the points are only `ε₁`-neck-like, so the trigger is lost;
- a cap of diameter `C1(ε)/√R ≫ ε⁻¹/√R` is not excluded by a neck of length `ε⁻¹`.

Perelman's repeated extension excludes caps in the LIMIT, where the region is `ℝ×N` on arbitrarily
large balls.

Therefore:
- the clause is attached to the canonical witness itself: a neck alternative ⇒ a history strong neck
  (`StronglyCanonicalBefore` below);
- cap exclusion is proved by the consumer, topologically, on the limit.

**F7. The arms lemma is not uniform.** `exists_minimizingArms_of_horn_point`
(`Surgery/Topology/HornCentralSphereSeparation.lean:488`) has `∃ Q` after `P c e`. A uniform `Kfine`
cannot take its threshold from it. The recommended consumer T3A gets its line from the horn inside the
blow-up limit instead: two arms of normalized length → ∞, because `R_L(x)/ℓ → ∞`.

## 1. The fork

### (A) Strengthen the class: witness-level cross-event strong necks. RECOMMENDED.

The predicate and the clause (probe-elaborated). `backwardSurvivorDomain` is at
`Surgery/Topology/HistorySurvivorDomain.lean:73`, `backwardSurvivorSlabMetric` at `HistorySurvivorFlow.lean:38`,
and `StrongNeck` at `Perelman/CanonicalNeighborhood/FiniteHornGeometry.lean:122`.

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
def StronglyCanonicalBefore (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan t₀ : ℝ) : Prop :=
  ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) t₀ → qcan < G.flow.scalar t y →
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y, W.capTubeHasNeckChart ε ∧
      ((∃ n, W.alternative = .neck n) → H.toHistory.HistoryStrongNeck k G ε₁ y t)
-- StronglyCanonicalOn (…) (t₀ η) (S) : same body over H.time k < t, t₀ ≤ t < t₀ + η, t < s, S y t
def EventSlabsStronglyCanonical (ε ε₁ C1 C2 qcan : ℝ) (k : Fin (H.eventCount + 1)) : Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    H.StronglyCanonicalBefore j.castSucc (H.toHistory.event j).incoming ε ε₁ C1 C2 qcan
      (H.time j.succ)
theorem StronglyCanonicalBefore.spatiallyCanonicalBefore … :
    G.SpatiallyCanonicalBefore ε C1 C2 qcan t₀
theorem StronglyCanonicalBefore.of_threshold_le (hq : q ≤ q') … -- proved in the probe (one line)
end RetainedCoreHistory
```

Interface changes (all elaborated):
- `CanonicalNeighborhoodsThroughSurgeryStronglyNecked P₀ g₀ :=`
  `∀ ε₁, 0 < ε₁ → ε₁ < 1/11 → ∃ εbar > 0, ∀ B ε Λ, … → …StronglyNeckedAt P₀ g₀ B ε ε₁ Λ`.
  - The `…At` body is `CanonicalNeighborhoodsThroughSurgeryStrongAt`
    (`Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:24`) verbatim.
  - The two spatial clauses are replaced by `H.EventSlabsStronglyCanonical ε ε₁ C1s C2s qcan (Fin.last _)`
    and `H.StronglyCanonicalBefore (Fin.last _) G ε ε₁ C1s C2s qcan s`.
  - `εbar` now depends on `ε₁`, because K1 needs `ε ≤ εs(ε₁)`.
- `UniformDebitSurgeryStepStrongNecked P₀ g₀ := ∃ ε₁, 0 < ε₁ ∧ ε₁ < 1/11 ∧ ∀ B εbar, …`. It is
  `UniformDebitSurgeryStepStrong` (`:124`) with the same two replacements.
- The composition `exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrongNecked` (the
  `:192` proof) takes `ε₁` from S, then `εbar(ε₁)` from CN. The rest is threading plus `of_threshold_le`.

The supply T4′ (replaces T4; no cap-parameter binder at all):
```lean
def FineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 / 11 ∧
  ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧
  ∀ (κ C1s C2s qcan a₀ : ℝ) (Ctime Cgrad : ℝ≥0) (ε : ℝ),
    0 < κ → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < a₀ → 0 < ε → ε ≤ εcone →
  ∀ εc : ℝ, 0 < εc → εc < 1 / 2 →
  ∃ Kfine : ℝ, 1 ≤ Kfine ∧
  ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
  ∀ H : RetainedCoreHistory P₀, InitialIdentification P₀ g₀ H.toHistory →
  ∀ hend : H.time (Fin.last H.eventCount) = H.horizon,
    H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
    (∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (H.time j.succ)) →
    H.EventSlabsStronglyCanonical ε ε₁ C1s C2s qcan (Fin.last H.eventCount) →
    H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
  ∀ {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)),
    G.DerivativeBoundBefore Ctime qcan s → G.GradientBoundBefore Cgrad qcan s →
    H.StronglyCanonicalBefore (Fin.last H.eventCount) G ε ε₁ C1s C2s qcan s →
    (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
      H.TerminalNoncollapsedBefore hend G hG κ ε t₀) →
  ∀ {εP Λ : ℝ} (P : TerminalCorePresentation
      { stage := H.stage (Fin.last H.eventCount)
        startTime := H.time (Fin.last H.eventCount)
        endTime := s
        startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
        startTime_lt_endTime := G.lt
        slab := G
        terminal := L
        singular := hsing
        parameters := parameters } εP Λ), εP ≤ eta →
  ∀ Qc : ℝ, Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Qc →
    P.FineCutNecks εc Qc

theorem uniformDebitSurgeryStepStrongNecked_of_fineCutNeckSupplyStrong
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (hfine : FineCutNeckSupplyStrong P₀ g₀) :
    UniformDebitSurgeryStepStrongNecked P₀ g₀
```
`p₀` is universally quantified and unconstrained. `Kfine` depends only on `(εc, κ, C1s, C2s, qcan, a₀,
Ctime, Cgrad, ε)`, so F6, F7 of `DESIGN_B13` and H12 (1)/(3) vanish.

Why T4′ should be true (Perelman II §4.3 / KL 71.1):
1. Take deep horn points `xₙ` with `R_L(xₙ)/max(ℓ, qcan, 1) → ∞` that are not εc-necks, and slices
   `τₙ → s` at which the rescaled balls are close to `L`.
2. At `τₙ`, every point of the rescaled ball is a horn point. The class witness there is a neck, since
   caps are excluded by horn topology (T1c). The class then gives history strong necks, with windows
   traced across events by construction.
3. Cone exclusion on those windows gives bounded curvature at bounded distance.
4. Build the limit on `[−1, 0]`. It splits `ℝ×N` (a line from the horn). At normalized time `−k` the
   approximants are close to `ℝ×N` on large balls, so there are no caps. The class gives new strong
   necks, and the window extends to `−k−1`. This extension works across events, and a late-age cap
   cannot interrupt it: a point entering a cap region just after gluing would carry a cap witness,
   which contradicts the cap exclusion.
5. The limit is an ancient κ-solution with a line, hence a cylinder, hence εc-necks at `xₙ`. That is a
   contradiction.

No cap-window comparison is used, so no model radius or model accuracy enters.

**Who must PRODUCE the clause.** It sits where `SpatiallyCanonicalOn` is produced today: C4
(`SpatialCanonicalContinuation`, `Surgery/Topology/SpatialCanonicalContinuation.lean:144`), using C3's
outputs. Leaf by leaf:
- **Old points** (`τmin ≤ R(t − a)`, C3a Deep and C4 case A). C3's `CanonicalWitness` carries a
  `LocalNeck` (a `StrongNeck` in the slab). Brick P1 turns it into a `HistoryStrongNeck` with
  `first := k`. The survivor domain is the whole stage and `gflow` is `G`'s metric. Extra:
  150–300 lines.
- **Young cap-window points** (C3b, C4 case B), through the standard solution:
  - S1: a strong ε₁-neck of the standard solution at every neck-witness point with `ε ≤ εs(ε₁)`, at ages
    `[0, Θ]`. It extends 27c (`StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts`,
    `Perelman/StandardSolution/StandardSliceSpatialCanonical.lean:666`) with the time window.
  - S2: when `R⁻¹ >` the age, the window crosses the gluing time. Neck-witness points then lie beyond
    `capRegion`. Splice the window with the record's `IncomingBackwardNeck`
    (`Surgery/Topology/GeometricCutoff.lean:58`, depth `r² = scale⁻¹`). If the depth still falls short
    (`R_std < 1`), concatenate with the earlier slabs' `EventSlabsStronglyCanonical` (an induction input,
    so this is not circular). This needs `δmax ≲ ε₁`, which CN chooses after `ε₁`.
  - S3: transport through the window comparison, `StrongNeck.transport_of_comparisons`
    (`Perelman/CanonicalNeighborhood/BackgroundJetTransfer.lean:548`). The accuracy `ε₁` is fixed before
    CN picks `Dcap εcap`, so this is not circular.
  - Extra: 1.8–3.4k lines.
- **Young non-cap-window points, including late-age caps** (C3c, C4 case C), through the X-core's
  ancient limit:
  - K1 `kappaSolution_strongNeck_of_spatialNeck` (elaborated: `∀ ε₁, ∃ εs < ε₁, ∀ κ P,
    IsAncientKappaSolution κ P → SpatialNeck (P.S.base.metric 0) εs P.basepoint → StrongNeck P.S ε₁ …`).
    It uses κ-compactness and the splitting of a κ-solution containing a line. `εs` must be
    κ-independent, like `kappa_canonical_neighborhood`: 400–900 lines.
  - X1: transport of the limit's strong neck back to the approximants on their survivor flows, a
    history E3: 600–1200 lines.
  - The X-core is unchanged: C3c keeps its own `∃ Dcap θcap`, with `θcapₙ ↑ 1`.
- **Interface threading:**
  - `StronglyCanonicalOn` added to the four leaf statements;
  - a `canonicalBefore_end_of_continuation` analogue (`CanonicalNeighborhoodInduction.lean:96`);
  - `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (`…Strong.lean:272`);
  - the composition (`:192`).
  - Total 400–800 lines.

**Consumer T3A** (replaces T1, T2 and T3 for S):
- T3A-1, about 400–800 lines: from the horn necks of `L` to neck witnesses at `τ` on the rescaled ball,
  with caps excluded by the horn sphere's `ComplementPair`. This is T1c's topology,
  `exists_horn_neck_end_separation_tolerance` (`Surgery/Contract/HornNeckEssentiality.lean:125`).
- T3A-2, about 2–4k lines: the §4.3 blow-up on survivor flows by repeated extension.
  - It uses `exists_complete_nonnegative_bounded_ancient_solution_subsequence_on_terminal_maps_of_strongNeck_above`
    (`Perelman/CanonicalNeighborhood/TerminalScalarAncientLimit.lean:475`), whose `hneck` is exactly the
    class clause after cap exclusion.
  - It shares the DESIGN_MAXWINDOW M2 scaffolding.
- T3A-3, about 300–600 lines: line ⇒ cylinder ⇒ εc-neck on `L`, via
  `exists_windowed_tolerances_for_original_arm_cylinder_limit` (`Perelman/CanonicalNeighborhood/WindowedArmCylinderLimit.lean:27`)
  and `TerminalLimitMetric.eventually_normalizedNeck_of_strongNecks_of_scalar_control`
  (`Surgery/Topology/TerminalNeckNormalization.lean:434`).

### (B) Fixed-parameter X-core. Reduces to (A); killed as an independent route.

Statement (elaborated): B3e with `∃ Dcap Rrad ζ₀` moved before `∀ A`:
```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_fixed
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Dcap Rrad ζ₀ : ℝ, StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧ 0 < ζ₀ ∧
    ∀ A : ℝ, 0 < A → ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ … -- body of :249 verbatim
```
- It is probably TRUE; no counterexample was found. At a late-age cap, the Bryant-like tip gives
  `R ≲ A·R(y)` at normalized distance `A`.
- It is UNSUPPLIED. B3e's proof (`:290`) negates its own `∃ … Rrad ζ₀` and instantiates
  `Rradₙ = Dcapₙ = transitionEnd + 1 + n`. The contradiction uses non-cap-window points at growing
  radius, and the B5 capture-age bound needs `θcap(A, T) ↑ 1`.
- At a fixed `Rrad`, the offending points lie in caps of age in `(Θ(p₀), 1)` or at model radius
  `> Dcap`. There, F4 leaves only spatial data.
- Varying εc along the sequence changes nothing: εc is fixed before `Kfine`, and the sequence in T4 is
  indexed by `Kfine → ∞`.
- Pushing `R(xₙ)/Q_cap → ∞` forces age → 1 (F4).

Any proof must therefore obtain backward flow information at late-age cap points from somewhere other
than `p₀`, and only the class can supply that. That is (A).

Cost if pursued anyway: the X-core plus a new late-age mechanism. Not estimable, since the mechanism is (A).

### (C) Reorder F\*. Killed.

The dependence is `εcut ≤ δ/2 ≤ 1/(2(Dbig + 1 − transitionEnd))`. It is geometric (`hfit`, F1). The
fixed-point inequality is infeasible with the actual `Dbig ≥ Dtrace + 1 ≥ 64(r + tol⁻¹)` (F1).

"Decouple" would mean cutting at a neck coarser than the model ball. That breaks `PresentedStaticCap`
(the model window must lie inside the neck).

### (D) B12 weakening with `(s − a)⁻¹`. Killed.

Statement (elaborated; B12's `2θ ≤ Qc·(s−a)` is absorbed into `K·(s−a)⁻¹`):
```lean
theorem exists_fineCutNecks_of_inverse_slab_length :
    ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧ … ∀ {εc : ℝ}, 0 < εc → εc < 1 / 2 →
    ∃ K : ℝ, 1 ≤ K ∧ ∀ … (P : TerminalCorePresentation …), ε ≤ eta →
      ∀ Qc : ℝ, K * max (max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1))
          (s - H.time (Fin.last H.eventCount))⁻¹ ≤ Qc → P.FineCutNecks εc Qc
```
It is true: it is a corollary of B12 (`Surgery/Contract/HornFineCutNecksLongSlab.lean:291`).

It cannot feed S, for three reasons:
1. `UniformDebitSurgeryStepStrong` exports `∃ p₀ δbound ρbound v, 0 < v ∧ ∀ H …` with `v` before `H`,
   and F\*'s `v = Q^{-3/2}`. With `Q ≳ (s−a)⁻¹`, `v` depends on the history.
2. The volume argument (`exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants`,
   `Surgery/Topology/SingularEventExtinction.lean:33`) needs a uniform `v`.
3. The debits can be summable. With slab lengths `2^{-i}` one gets `Qᵢ ≈ 2^i` and `vᵢ ≈ 2^{-3i/2}`, so
   `Σvᵢ < ∞`, the volume bound allows infinitely many events, and event times can accumulate.

A separate finiteness argument would need a lower bound on slab lengths, which is `hlong` (unsupplied).

## 2. Recommendation: (A)

Why (A):
- It is the only option in which the S supply has no cap-parameter binder. F1, F2 and F4 all come from
  such binders.
- It is Perelman's own architecture: strong necks in the canonical-neighbourhood assumption, with
  §4.3 consuming them.
- Its production cost falls on leaves that already own the needed freedom: C3c chooses `Dcap` and
  `θcap`, and CN chooses `δmax` and `εcap` after `ε₁`.

What must go to review next, as one statement: T4′ (`FineCutNeckSupplyStrong`) with its two
definitions. The prompt is below.

> 请审查单一命题 T4′ `FineCutNeckSupplyStrong`（Lean 全文见 `Surgery/Skeleton/DESIGN_S_SUPPLY.md` §1(A)，已在探针中通过类型检查）。背景：原 T4（`FineCutNeckSupply`）要求帽参数 `Rrad ζ₀` 先于 εc、`Kfine` 先于 `p₀`，而 X-core 与帽窗比较（`CapWindowStandardComparison:20`）只在 `modelRadius→∞`、`θcap↑1` 时运行；F* 的 `hfit : D+1 ≤ transitionEnd+δ⁻¹` 迫使 `εcut ≲ 1/Dbig`，故重排 F*、固定 p₀ 的 X-core、`(s−a)⁻¹` 弱化均不可行。我们改为加强类：定义 `HistoryStrongNeck`——点 y 在时刻 t 有强 ε₁-颈，其抛物窗 `[t−R⁻¹,t]` 经 `backwardSurvivorDomain` 跨越事件被追踪、存活流满足 `IsSolutionOn`；`StronglyCanonicalBefore`——每个 `R>qcan` 的点有空间典范见证，且见证为颈时即为 `HistoryStrongNeck`。T4′：∃ ε₁ eta εcone；∀ κ C1s C2s qcan a₀ Ctime Cgrad ε≤εcone；∀ εc；∃ Kfine；**∀ p₀（无任何帽参数约束）**、∀ 满足类条件（含强颈子句）的历史与奇异终片、∀ εP≤eta 的终端呈现 P：`Kfine·max(Λ/r²,qcan,1) ≤ Qc ⇒ P.FineCutNecks εc Qc`。证明路线为 Perelman II §4.3：喇叭拓扑排除帽见证，类强颈给出窗口，锥排除得有界曲率，在极限中反复向后延伸（极限为 ℝ×N 时排除帽），得带直线的古代 κ 解，从而为圆柱。
> 请回答：(1) 真值：T4′ 在 `Kfine` 与 p₀ 无关时是否成立？晚龄帽（龄∈(Θ,1)）或粘接后立即进入帽区的点能否打断反复延伸？(2) 簿记：ε₁ 先于 CN 的 εbar、CN 在 ε₁ 之后选 δmax εcap，是否有隐藏循环？(3) 可供给性：强颈子句能否由 CN 各叶产出——旧点（片内 StrongNeck）、年轻帽窗点（标准解强颈，窗口跨粘接时与记录的 `IncomingBackwardNeck` 及更早片的强子句拼接）、晚龄与非帽窗点（X-core 古代极限 + κ 解"空间颈⇒强颈"）？(4) 若为假，请给出具体历史反例或最小修正。

## 3. Bricks for (A)

| Brick | Content | Suppliers (`file:line`) | Lines |
|---|---|---|---|
| P0 | `HistoryStrongNeck` + API: mono in `eps`; restrict the window; threshold mono; concatenation across windows | `HistorySurvivorDomain.lean:73`, `HistorySurvivorFlow.lean:38,180`, `HistorySurvivorIncoming.lean:196`, `FiniteHornGeometry.lean:122` | 300–600 |
| P0b | `StronglyCanonicalBefore/On`, `EventSlabsStronglyCanonical`, `→ SpatiallyCanonicalBefore`, `of_threshold_le` (done in the probe) | `CanonicalNeighborhoodInduction.lean:40,59` | 60–120 |
| I1 | Interface: `…StronglyNecked(At)`, `UniformDebitSurgeryStepStrongNecked`, the composition; `StronglyCanonicalOn` in the four leaf statements; induction end lemma; `_of_leaves` | `CanonicalNeighborhoodsThroughSurgeryStrong.lean:24,69,124,192,272`, `CanonicalNeighborhoodInduction.lean:96`, `SpatialCanonicalContinuation.lean:144`, `CanonicalNeighborhoodContinuationLeaves.lean:146,188,232` | 400–800 |
| P1 | Old points: in-slab `LocalNeck` ⇒ `HistoryStrongNeck` (`first := k`) | `FiniteHornGeometry.lean:122,272`, `HistorySurvivorFlow.lean:143` | 150–300 |
| S1 | Standard solution: a neck witness at age `≤ Θ` is a strong ε₁-neck (window inside `[0, age]`) | `StandardSliceSpatialCanonical.lean:666`, `StandardFarRegion.lean:400`, `StandardTerminalBlowup.lean:61` | 800–1500 |
| S2 | A window crossing the gluing: neck-witness points lie beyond `capRegion`; splice with the record's `IncomingBackwardNeck` and the earlier slabs' clause | `GeometricCutoff.lean:58`, `PreparedHistoryCutoff.lean:156`, P0 concatenation | 800–1500 |
| S3 | Transport of S1/S2 through the cap-window comparison into C3b/C4(B) | `BackgroundJetTransfer.lean:548`, `CapWindowStandardComparison.lean:20` | 200–400 |
| K1 | `kappaSolution_strongNeck_of_spatialNeck` (κ-independent `εs`) | `AncientCanonicalNeighborhood.lean:146`, κ-solution compactness in `Perelman/KappaSolutions/` | 400–900 |
| X1 | The limit's strong neck back to the approximants' survivor flows (history E3); wired into C3c/C4(C) | `CanonicalAlternativeComparisonTransport.lean:18`, DESIGN_B6D_GLUE B13, B6b′ survivor exports | 600–1200 |
| T3A-1 | Horn necks of `L` ⇒ neck witnesses at `τ` on rescaled balls; horn-topology cap exclusion | `HornNeckEssentiality.lean:125`, `TerminalSpatialCanonicalAlternatives.lean:473`, `HornSeparationFrontierScalar.lean:116` | 400–800 |
| T3A-2 | §4.3 blow-up by repeated backward extension on survivor flows; cap exclusion in the limit | `TerminalScalarAncientLimit.lean:475`, `BoundedCurvatureAtDistanceCone.lean`, DESIGN_MAXWINDOW M2 | 2000–4000 |
| T3A-3 | Line ⇒ cylinder ⇒ εc-neck on `L` | `WindowedArmCylinderLimit.lean:27`, `TerminalNeckNormalization.lean:434` | 300–600 |
| T4′ | Assembly of `FineCutNeckSupplyStrong` | the rows above | 200–400 |
| T5′ | Edit of T5: new hypotheses, `Dbig := max Dcap (Dtrace+1)`; drop `Rrad ζ₀ δ₀ ρ₀ m₀` | `UniformDebitSurgeryStepOfFineCutNeckSupply.lean` | 100–200 |

Totals:
- production (P1, S1–S3, K1, X1): 3.0–5.8k lines;
- consumer (T3A, T4′): 2.9–5.8k lines;
- interface (P0, I1): 0.8–1.5k lines.

Order:
1. The review prompt (§2).
2. P0, P0b and I1, as a skeleton with the new sorry leaves `FineCutNeckSupplyStrong` and the four
   strengthened leaf clauses.
3. P1 and K1.
4. S1–S3 and X1 on the C3b/C3c lanes.
5. T3A after DESIGN_MAXWINDOW M2 lands.

Impact on the delivered and planned T-bricks:
- **T5 survives.** Its proof skeleton, instantiations, `open private` helpers and F\* calls are
  unchanged. T5′ only swaps the hypothesis list (spatial clauses ⇒ strong clauses) and drops the
  `Rrad`/`ζ₀`/`δ₀`/`ρ₀`/`m₀` plumbing. Until I1 lands, the delivered T5 stays a correct conditional
  on `FineCutNeckSupply`.
- **T1 is not consumed.** Its topological core (T1c) is reused in T3A-1. Do not build T1a, T1b or the
  assembly.
- **T2 is retired**, together with F8 (the `−3/a₀` floor) and H12's `recenterConstant·δbound` gap.
- **T3 is replaced by T3A.** The X-core remains the Crossing lane's (C3c/C4(C)) and is no longer
  called by S.
- `uniformDebitSurgeryStepStrong_of_long_slabs` and B12 stay correct but unused.
