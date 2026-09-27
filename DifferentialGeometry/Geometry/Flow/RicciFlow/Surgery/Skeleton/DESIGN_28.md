# Entry 28: interface revision (design, 2026-09-26)

Target: `liao/codex/pc-target-c-psf` @ 1682df442. Paths are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`. This is a read-only design. No Lean file was edited.
Every proposed definition below was elaborated in a scratch probe outside the repo
(`lake env lean`, 0 errors). The probe also compiled the new scale lemma of (iv) with a
complete proof. The only `sorry` in the probe was the core-accuracy lemma of (v), which is a
proof brick and not an interface.

## Failures and deviations first

1. **(iii) cannot be done as briefed without changing C4.** A crossing proof by contradiction
   (`qcanₙ → ∞`) can only use earlier-slab spatial witnesses at points of curvature comparable to
   the blow-up scale `Qₙ > qcanₙ`. C4 currently outputs its threshold as `∃ qs, qcan ≤ qs` with no
   upper bound, so `qsₙ ≫ Qₙ` is allowed and the hypothesis would give nothing. The repair is to
   change `SpatialCanonicalContinuation` so that it outputs `Cs` together with `C1s C2s` (before
   `κ`) and a floor `q₄` (after `κ phi`). It then guarantees `qcan ≤ qs ≤ Cs * qcan` for
   `q₄ ≤ qcan`. Because of the floor, C3 must also accept `∀ qfloor` and return `qfloor ≤ qcan`.
   Both are sorry leaves or thin assemblies today, so no proved code is invalidated.
2. **(iv) The factory's cut scale does not give `qcan ≤ Cbirth·scale`.**
   `Contract/PoincareHornCutoffRecord.lean` gives `C2²·qcan < Q`, but `Cbirth` is an output of
   `exists_standard_comparison_of_cap_window_trace` that S never sees. Also, the bridge needs the
   **recentred static** scale, not `Q`. The design therefore does not route the bound through `Q`
   or `Qmin`. It goes through `ρbound` and needs exactly one new class clause,
   `p₀.recenterConstant * δbound ≤ 1 / 2`. The strong C discharges that clause from its existing
   `p₀.recenterConstant ≤ Λ`. **The strong S statement and the factory need no change for (iv).**
3. **(v) needs no statement change.** `εcap` is already chosen before `p₀` and after `Rcap`.
   What is missing is one lemma (the core version of the scalar lower bound, below), plus the rule
   that the cap-leaf proof takes `D* := Rcap` and never uses `ε₀(p.modelRadius)`. **Do NOT add a
   `CutoffParameters` field for `D*`.**
4. **The old C assembly must be deleted.**
   `canonicalNeighborhoodsThroughSurgery_of_continuation_of_noncollapsing_of_pinching` in
   `CanonicalNeighborhoodInduction.lean:300` cannot be kept. After (i), (iii) and (iv) it would need
   C4 and a bound `Λ` that the old C does not have (review E item 5: the old interface may not
   borrow `Λ`). It has zero consumers. The old C remains available as a projection of the strong
   one through `canonicalNeighborhoodsThroughSurgeryOfRecenter_of_strong`.
5. **(vi) is required, not optional.** In the strong S (`∀ B, ∃ Λ, ∀ Ctime, ∃ ε, ∀ …qcan…`), the
   derivative-bound threshold `qcan` arrives after `ε`. With the current wrapper, `εcan` depends on
   `q0` through `ηstar, mstar`. So S can only be proved after the switch.
6. **Pre-existing boundary slice, not introduced here.** All `…Before t₀` clauses are open at `t₀`.
   `NoncollapsedBefore κ ρ t₀` includes the slice `t = t₀`, and when `t₀ = H.time j.succ` that is
   the post-surgery slice. The small-scale leaf must handle `t = t₀` with a limit or at the event
   itself. The age-free spatial clause of (i) does not cover that slice either. Record this in the
   entry-25 brief.

## (iv) Class supply (do this first; (ii) depends on it)

**Current** (`Surgery/Topology/CanonicalNeighborhoodInduction.lean:147`):
```lean
def InCutoffClass (g₀ : P₀.Metric) (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ) : Prop :=
  Nonempty (InitialIdentification P₀ g₀ H.toHistory) ∧
    H.time (Fin.last H.eventCount) = H.horizon ∧ H.horizon < B ∧
    H.hasCanonicalCutoffRecords p₀ δbound ρbound
```
**Proposed** (append the new conjunct last, so `hH.2.1` stays valid in every statement):
```lean
def InCutoffClass (g₀ : P₀.Metric) (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ) : Prop :=
  Nonempty (InitialIdentification P₀ g₀ H.toHistory) ∧
    H.time (Fin.last H.eventCount) = H.horizon ∧ H.horizon < B ∧
    H.hasCanonicalCutoffRecords p₀ δbound ρbound ∧ p₀.recenterConstant * δbound ≤ 1 / 2
```
New lemma, placed in `CanonicalNeighborhoodContinuationLeaves.lean` after
`IsCanonicalCutoffRecordFamily` (the probe compiled it with no `sorry`):
```lean
theorem IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale {H : RetainedCoreHistory P₀}
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records)
    (hΛδ : p₀.recenterConstant * δ₀ ≤ 1 / 2) (i : Fin H.eventCount)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    (2 * ρ₀ ^ 2)⁻¹ < ((records i).static b).neck.scale := by
  obtain ⟨-, -, -, -, hrc, -, hδ, hρ⟩ := hrec
  have ht : 0 ≤ H.time i.succ := H.toHistory.time_nonneg i.succ
  set α := b.1.1
  have hn := (records i).nominal_small ⟨α⟩
  have hnpos := (records i).nominal_pos ⟨α⟩
  have hdpos := p.delta_pos _ ht
  have hd1 := p.delta_lt_one _ ht
  have hρpos := p.neckRadius_pos _ ht
  have hcmp := (records i).recenter_scale_comparison b
  have hsc := (records i).scale_eq α
  have hdα := (records i).delta_le α
  have hdαpos := (records i).delta_pos α
  have hΛ : (4 : ℝ) ≤ p.recenterConstant := p.recenterConstant_ge_four
  rw [hrc] at hcmp hΛ
  set r := (records i).nominalRadius ⟨α⟩
  set N := ((records i).neck α).scale
  set S := ((records i).static b).neck.scale
  have hSpos : 0 < S := ((records i).static b).neck.scale_pos
  have hr : r < ρ₀ := by
    have h1 : p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) ≤
        p.neckRadius (H.time i.succ) := by
      have : p.delta (H.time i.succ) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    exact hn.trans_le (h1.trans (hρ i))
  have hNlow : (ρ₀ ^ 2)⁻¹ < N := by
    rw [hsc]
    exact inv_strictAnti₀ (pow_pos hnpos 2) (by nlinarith)
  have hNpos : 0 < N := (inv_pos.mpr (pow_pos (hnpos.trans hr) 2)).trans hNlow
  have hΛδα : p₀.recenterConstant * (records i).delta α ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hdα.trans (hδ i)) (by linarith)).trans hΛδ
  have hhalf : 1 / 2 ≤ S / N := by
    have := (abs_le.mp (hcmp.trans hΛδα)).1
    linarith
  have hS : N / 2 ≤ S := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * ρ₀ ^ 2)⁻¹ = (ρ₀ ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]; ring
  rw [h2]
  linarith
```
The mathematics: the nominal radius satisfies `r < δ(t)²ρ(t) ≤ ρ₀`, so the nominal scale `N` is
greater than `ρ₀⁻²`. The comparison `|S/N − 1| ≤ Λrec·δα ≤ Λrec·δ₀ ≤ 1/2` then gives
`S ≥ N/2 > (2ρ₀²)⁻¹`.

**How the cap leaf uses it** (proof only, after (ii)). Choose
`ρmax ≤ min (√(Cbirth / (2·qcan))) (√(a₀ / 2))`. Here `Cbirth` comes from
`exists_standard_comparison_of_cap_window_trace Θ Ctime` (with `θcap ≤ Θ < 1`), and `a₀` comes
from `exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀`. The same call supplies
the two initial-data hypotheses of the bridge. Any event gives `0 < ρbound ≤ ρmax`, so
`qcan ≤ Cbirth·scale` and `1 ≤ a₀·scale` follow. The third bridge hypothesis,
`Gk.DerivativeBoundBefore C qcan t`, stays a proof obligation of the leaf (review E item 5). Bootstrap
it from the prior control with the strict margin `C' < Ctime₀` from the standard solution. Never
assume it at the current time.

**Builders to update.**
- In the strong assembly (see (i)), `intro B ε Λ hB hε hε' hΛ` (it is currently `_`). Add
  `(2 * Λ)⁻¹` as a fifth `min` component of `δmax`. Build the clause with a helper lemma:
  ```lean
  theorem recenterConstant_mul_le_half {p₀ : CutoffParameters} {Λ δ : ℝ} (hΛ : 0 < Λ)
      (hp : p₀.recenterConstant ≤ Λ) (hδ : δ ≤ (2 * Λ)⁻¹) : p₀.recenterConstant * δ ≤ 1 / 2
  ```
  Proof: if `δ ≤ 0`, the product is `≤ 0` by `mul_nonpos_of_nonneg_of_nonpos` (use
  `recenterConstant_ge_four`). Otherwise `r·δ ≤ Λ·δ ≤ Λ·(2Λ)⁻¹ = 1/2`. Then
  `hH := ⟨⟨hinit⟩, htime, hhor, hclass, hrδ⟩`.
- Delete the old C assembly (Failure 4).

**Projection sites to update** (`hH.2.2.2` becomes `hH.2.2.2.1`):
`CanonicalNeighborhoodContinuationLeaves.lean:261`, `PinchingThroughSurgery.lean:20`,
`ReducedVolumeTruncation.lean:286` (check 340/355 too).
`DeepContinuation.lean` uses only `hH.2.1` and is unaffected.

## (ii) `ρmax` (and `δmax εcap`) after `qcan`

**Only `CapWindowContinuation` changes.**
- `CanonicalNeighborhoodContinuation` already binds `qcan` and `ρmax` in the same `∃` block.
- The strong C already binds `qcan … ρmax` in one `∃` block.
- The strong S takes all C constants universally. It consumes the constants unchanged, and the
  hext assembly (`exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong`) is
  unchanged.
- Deep and Crossing may keep `ρmax` before `qcan`; that is stronger, and the assembly handles either.

**Current** (quote of the constant block):
```lean
  ∃ (Rcap q₀ δmax ρmax εcap : ℝ) (mcap : ℕ),
    Dcap + 1 < Rcap ∧ 0 < q₀ ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ), …
```
**Proposed** (the rest of the statement is verbatim, apart from `InCutoffClass` gaining its clause):
```lean
  ∃ (Rcap q₀ : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → …
```
`Rcap` stays before `qcan` because it is `D*` in (v) and `εcap` depends on it. `δmax` and `εcap` move
as well. They are combined by `min` anyway, and moving them costs the assembly nothing.

**Assembly change** in `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing` (the
full sketch, together with (iii), is below). Obtain `⟨Rw, qw, mw, hRw, hqw, hWq⟩` before
`qcan`. After choosing `qcan`, run
`obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hWstep⟩ := hWq qcan hqle`. Then
`hw := hWstep p₀ δbound ρbound …` without the `qcan` argument.

## (i) Small-scale leaf takes the age-free spatial clause

**Current:** `SmallScaleNoncollapsingThroughSurgery` (`NoncollapsingThroughSurgeryLeaves.lean:163`)
takes only the age-restricted `EventSlabsCanonical` and `CanonicalBefore`.

**Proposed** (probe-checked; shown with the new `InCutoffClass`):
```lean
def SmallScaleNoncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    Prop :=
  ∀ (B ε C1 C2 C1s C2s τmin : ℝ) (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ) (κ₁ : ℝ),
    0 < B → 0 < ε → ε < 1 / 11 → 1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < τmin →
    Perelman.AdmissiblePinchingFunction phi → 0 < κ₁ →
  ∃ κ : ℝ, 0 < κ ∧
  ∀ qcan qs : ℝ, 0 < qcan → qcan ≤ qs →
  ∃ (r₀ δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    0 < r₀ ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory P₀) (hH : H.InCutoffClass g₀ B p₀ δbound ρbound),
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ioc (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedAboveBefore κ₁ r₀ ε t₀ →
          H.NoncollapsedBefore κ r₀ t₀) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        ∀ t₀ : ℝ, t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ → G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedAboveBefore hH.2.1 G hG.2 κ₁ r₀ ε t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ r₀ t₀
```
Why (review D items 5 and 6): the age filter misses old high-curvature points after a distant
reset, so the trichotomy needs a spatial witness at the point of curvature `≈ ρ⁻² > qs`. `κ`
depends on `C1s C2s` (the volume clause `C2s⁻¹`) but not on `qs`. `r₀` is chosen after `qs`, with
`r₀ ≲ qs^{-1/2}`.

`NoncollapsingThroughSurgery` (`CanonicalNeighborhoodInduction.lean:193`) changes identically:
- binders become `(B ε C1 C2 C1s C2s τmin …)` with `1 ≤ C1s → 1 ≤ C2s`;
- `∀ qcan : ℝ, 0 < qcan →` becomes `∀ qcan qs : ℝ, 0 < qcan → qcan ≤ qs →`;
- the same two spatial hypotheses are added in both branches.

`HistoryReducedVolumeInitialLowerBound` is unchanged.

Assembly `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale`:
```
intro B ε C1 C2 C1s C2s τmin Ctime Cgrad phi hB hε hε' hC1 hC2 hC1s hC2s hτ hphi
obtain ⟨κ₂, hκ₂, hS⟩ := hsmall B ε C1 C2 C1s C2s τmin Ctime Cgrad phi _ hB hε hε' hC1 hC2 hC1s hC2s hτ hphi hκ₁
intro qcan qs hqcan hqs
obtain ⟨r₀, …, hSstep⟩ := hS qcan qs hqcan hqs      -- hL qcan r₀ unchanged
event:    intro j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb
          habove from hl.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb (spatial not passed)
          exact … (hs.1 j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb habove)
terminal: same with hspat / hsb inserted before habove
```

**Does the strong induction carry C4's output into C2?** Yes, and the predicate does not change.
- `hstage` in `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` already carries
  `H.EventSlabsSpatiallyCanonical ε C1s C2s qs k`, which gives `hspatP` and `hspatL`.
- The `hN` callback of `canonicalBefore_end_of_continuation_spatial` already receives the
  current-slab spatial clause, which is presently discarded as `_`.
- Only pass-through changes are needed (the sketch is under (iii)). The final terminal clause uses
  `G.spatiallyCanonicalBefore_mono ht₀.2.le hcl.2.2.2`.

## (iii) Crossing receives the spatial clause (joint induction), with C4 amended

**Proposed `CrossingContinuation`** (probe-checked). It adds
`∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →` after the `C1 … Cgrad` bounds and before `κ`.
It adds `∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →` right after `∀ qcan : ℝ, q₀ ≤ qcan →`. It then
adds the same two spatial hypotheses as in (i):
- event branch: `H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →` after the gradient
  slabs, and `(H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →` after
  `GradientBoundBefore`;
- terminal branch: `…SpatiallyCanonical … (Fin.last H.eventCount) →` and
  `G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →`.

The conclusions are unchanged. The current-slab clause is included because the joint continuation
provides it for free.

**Proposed `SpatialCanonicalContinuation`** (Failure 1). Its head becomes
```lean
  ∃ C1s C2s Cs : ℝ, 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∃ q₄ : ℝ, 0 < q₄ ∧
  ∀ qcan : ℝ, q₄ ≤ qcan →
  ∃ (qs δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    qcan ≤ qs ∧ qs ≤ Cs * qcan ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧ …
```
The body is unchanged.

**Proposed `CanonicalNeighborhoodContinuation`** (C3 aggregate). Its head becomes
```lean
  ∃ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < τmin ∧
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi →
  ∀ qfloor : ℝ,
  ∃ (qcan δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    qfloor ≤ qcan ∧ 0 < qcan ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ …) …
```
The body gains the same two spatial hypotheses in each branch. All four definitions were compiled
in the probe.

**C3 assembly** `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing`:
```
intro B ε hB hε hε'                               -- deep/cap/cross constant blocks as today
refine ⟨maxes…, ?_⟩
intro C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi qfloor
obtain ⟨θ, qd, δd, ρd, εd, Dd, md, …, hDstep⟩ := hD … κ phi hκ hphi
obtain ⟨Dx, θcap, qx, δx, ρx, εx, mx, …, hXstep⟩ := hX … C1s C2s Cs hC1s hC2s hCs κ phi θ hκ hphi hθ
obtain ⟨Rw, qw, mw, hRw, hqw, hWq⟩ := hW … κ phi θ Dx θcap hκ hphi hθ hDx hθcap
set qcan := max qfloor (max qd (max qw qx))
obtain ⟨δw, ρw, εw, hδw, hρw, hεw, hWstep⟩ := hWq qcan (…le_max…)
refine ⟨qcan, min δd (min δw δx), min ρd (min ρw ρx), min εd (min εw εx), max Dd Rw,
  max md (max mw mx), le_max_left _ _, hqd.trans_le (…), …, ?_⟩
intro qs hqs hqsC p₀ δbound ρbound hacc hDc hm hδ hρ H hH hpinch
obtain ⟨p, records, hrec⟩ := (…iff…).mp hH.2.2.2.1
hd := hDstep qcan _ p₀ …;  hw := hWstep p₀ …;  hx := hXstep qcan _ qs hqs hqsC p₀ …
event:    intro j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb hnc
          h₁ ← hd.1 j hcan hder hgrad t₀ ht₀ hcb hdb hgb hnc
          h₂ ← hw.1 (same arguments)
          h₃ ← hx.1 j hcan hder hgrad hspat t₀ ht₀ hcb hdb hgb hsb hnc
          then the cover argument, unchanged
terminal: analogous
```
`DeepContinuation` and its proof are untouched.

**Strong assembly** `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (covers (i), (iii), (iv)):
```
intro B ε Λ hB hε hε' hΛ
obtain pinch; obtain ⟨C1, C2, τmin, Ctime, Cgrad, …, hF⟩ := hcont …
obtain ⟨C1s, C2s, Cs, hC1s, hC2s, hCs, hS⟩ := hspat B ε … C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
obtain ⟨κ, hκ, hN⟩ := hnon B ε C1 C2 C1s C2s τmin Ctime Cgrad phi … hC1s hC2s hτ hphi
obtain ⟨q₄, hq₄, hS₄⟩ := hS κ phi hκ hphi
obtain ⟨qcan, δF, ρF, εF, DF, mF, hq₄c, hqcan, …, hstep⟩ := hF C1s C2s Cs hC1s hC2s hCs κ phi hκ hphi q₄
obtain ⟨qs, δS, …, hqs, hqsC, …, hsp⟩ := hS₄ qcan hq₄c
obtain ⟨δN, …, hball⟩ := hN qcan qs hqcan hqs
refine ⟨C1, C2, C1s, C2s, qs, τmin, min δP (min δF (min δS (min δN (2 * Λ)⁻¹))), …⟩
intro p₀ δbound ρbound hacc hD hm hδ hρ hΛp H hinit htime hhor hclass
hH := ⟨⟨hinit⟩, htime, hhor, hclass, recenterConstant_mul_le_half hΛ hΛp hδ.…⟩
hF' := hstep qs hqs hqsC p₀ …;  hS', hN' as today
hstage (predicate unchanged):
  hN callback:    fun t₀ ht₀ hc hd hg hs => hN'.1 j hcanP hderP hgradP hspatP t₀ ⟨…⟩ hc hd hg hs
  hcont callback: … (hF'.1 j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn) (hS'.1 … as today)
  last conjunct:  hN'.1 j … hspatP (H.time j.succ) ⟨…⟩ hcl.1 hcl.2.1 hcl.2.2.1 hcl.2.2.2
terminal: hN'.2 … hspatL … hsp; hF'.2 … hspatL … hsp hn;
  final: … (G.spatiallyCanonicalBefore_mono ht₀.2.le hcl.2.2.2)
```
Consumers: `Skeleton/PoincareEndgame.lean` keeps the same names and needs no edit.
`canonicalNeighborhoodsThroughSurgeryOfRecenter_of_strong`, the strong S and the hext assembly are
unchanged.

## (v) Accuracy through a fixed core `D*`

No statement changes. Add to `Surgery/Topology/CanonicalCapScalar.lean`:
```lean
theorem exists_presented_cap_scalar_lower_bound_of_canonical_window_core
    (Dstar : ℝ) (hD : StandardCap.transitionEnd < Dstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}, Dstar ≤ D → ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ z : ThreeBall,
            S.neck.scale / 2 ≤ metricScalarAt S.witness.metric (S.witness.cap z)
```
Proof route: restrict `w` to the `Dstar` window (`CanonicalStaticInsertionWitness.restrictWindow`,
already used in `CapWindowStandardComparison.lean`). Use `metricDerivENormSupOn_mono` on
`{‖y‖ ≤ transitionEnd} ⊆ {‖y‖ < Dstar}`, then follow the existing proof with
`exists_uniform_window_scalar_bounds_of_metric_close Dstar`. This is about 50 lines.

Fixing `D*`: in the cap leaf take `Rcap := max R (StandardCap.transitionEnd + 1)`. Here `R` is the
comparison lemma's `R > Dcap + 1`, and `D* := Rcap` gives
`transitionEnd < D* ≤ Rcap ≤ p.modelRadius`. Take `εcap ≤ min ζ₀ ε₀(D*)`, chosen after `Rcap` as
the statement already allows. `D*` is a leaf-internal constant: not a `CutoffParameters` field, and
not derived from the class.

## (vi) `Contract/PreparedHistoryCutoff.lean` switched to the variable threshold

Switch the private `exists_uniform_selected_neck_retained_append_backward` (line 156) from
`exists_uniform_selected_neck_append_backward` to
`exists_threshold_uniform_selected_neck_append_backward`. Its shape changes:
- from `∀ (a q₀), … ∀ phi, ∃ ηstar mstar Qmin, … Qmin ≤ O.scale`
- to `∀ a, 0 < a → ∀ phi, Admissible phi → ∃ ηstar mstar Λq, … 0 < Λq ∧ ∀ q₀, 0 < q₀ → … Λq * max q₀ 1 ≤ O.scale`.

The downstream statements that change are listed below. In each, `q0` moves from before the
`∃ δ ε₀ …` block to after it, and `∃ … Qmin` becomes `∃ … Λq` with `Qmin ≤ Q` replaced by
`Λq * max q0 1 ≤ Q`. `ε₀ = min εfactory (ηstar/2) (mstar+1)⁻¹` then no longer depends on `q0`,
which is the early-accuracy gain.
1. `exists_horn_cutoff_record_at_scale_of_prepared_history` (237):
   `∀ a phi, ∃ δ ε₀ Λq, …, ∀ q0 {P₀ g₀} H …`.
2. `exists_horn_cutoff_record_at_scale_of_initialIdentification` (458).
3. `…_above_scale_of_initialIdentification_and_core_radius_lower_bound` (633).
4. `…_of_initialIdentification_and_core_radius_lower_bound` (785).
5. `…_of_initialIdentification_and_canonical_neighborhoods_and_canonical_records` (922): `q0` goes
   after `∃ εcan`, next to `qcan`.
6. The factory `exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods`
   (`Contract/PoincareHornCutoffRecord.lean` ~461): the head becomes
   `∀ m accuracy ηrecord, ∃ δ ε₀ Λq, … ∃ εcan, ∀ C1 C2, ∃ C Λ, ∀ q0 qcan coreFloor protectedFloor, 0 < q0 → … ∃ Q v, Λq * max q0 1 ≤ Q ∧ …`.
   Pass `max (Λq * max q0 1) …` as the floor to `hmake`.

The strong S and hext statements are unchanged. S can then take `q0 := max q₀ q₁` (the two-C-call
thresholds) after `ε`. `Ctime` remains coupled, as expected (review E item 6).

## Implementation plan (dependency order)

1. Add the `InCutoffClass` clause, the lemmas `recenterConstant_mul_le_half` and
   `IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale`, and fix the three `.2.2.2`
   sites. Build `…Surgery.Topology.CanonicalNeighborhoodContinuationLeaves`,
   `…PinchingThroughSurgery` and `…ReducedVolumeTruncation`.
2. `SpatialCanonicalContinuation.lean`: add `Cs` and `q₄`.
3. `CanonicalNeighborhoodInduction.lean`: C3 aggregate and C2 aggregate definitions. Delete the old
   C assembly.
4. `CanonicalNeighborhoodContinuationLeaves.lean`: Cap (ii) and Crossing (iii) definitions, and the
   C3 assembly.
5. `NoncollapsingThroughSurgeryLeaves.lean`: small-scale definition and C2 assembly.
6. `CanonicalNeighborhoodsThroughSurgeryStrong.lean`: strong assembly.
7. `CanonicalCapScalar.lean`: the core lemma (v). This step is independent and can run in parallel.
8. `Contract/PreparedHistoryCutoff.lean` and then `Contract/PoincareHornCutoffRecord.lean` (vi).
   This is independent of steps 1–6.

Build all changed modules plus `…Surgery.Topology.DeepContinuation` and
`…Surgery.Skeleton.PoincareEndgame` in one lake call, then `lake build DifferentialGeometry`.
Check the axioms of the strong assembly: the only expected sorries are the skeleton leaves.

Line estimate, net:
| Items | Lines |
|---|---|
| (iv) | +60 |
| (i) | +30 |
| (ii) + (iii) definitions and assemblies | +80 |
| C4 | +6 |
| Old assembly removed | −85 |
| (v) | +50 |
| (vi), mostly statement motion across 6 theorems plus proof re-threading | +150 to +250 |
| **Total** | **≈ +300 to +400** |

## Items not to do

- A `D*` field in `CutoffParameters` (v): it is unnecessary, and `Rcap` already serves.
- Routing `qcan ≤ Cbirth·scale` through the factory's `Q` or `Qmin` (iv): S does not know
  `Cbirth`, and the static scale is not `Q`.
- Moving `ρmax` in Deep or Crossing: it is not needed.
- Keeping the old C assembly (Failure 4).
