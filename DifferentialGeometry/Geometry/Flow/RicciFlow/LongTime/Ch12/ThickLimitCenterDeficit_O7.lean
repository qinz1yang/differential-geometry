import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeLateHist_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeLateMain_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeUnconditional_S10

/-!
# CH12-O7 / C1, group D: the normalised-volume deficit is summable

For a Ricci flow with surgery and `R ≥ -3/(2(t+c))`, put `V̄(t) = V(t)(t+c)^{-3/2}` and the
*deficit* `𝒟(t) = ∫ R dV + 3/(2(t+c)) V(t) ≥ 0`.  On smooth stages `V̄' = -(t+c)^{-3/2} 𝒟`, and
surgery only decreases `V̄`.  Hence on a window where `𝒟 ≥ d`,
`φ(t) = V̄(t) - 2 d (t+c)^{-1/2}` is non-increasing, and summing over disjoint windows the total
deficit is bounded by a fixed constant (`V̄ ≥ 0`, `V̄(1) ≤` LTF01a).

* `flowVolume_deficit_antitone_O7` (smooth stage);
* `event_step_deficit_O7`, `closed_slab_step_deficit_O7` (one event / final slab);
* `history_chain_deficit_O7` (one observed history, from a start time to the horizon);
* `sliceDeficit_O7`, `deficit_windows_bounded_O7` (D1).
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {P Q : OrientedThreeStage.{u}} {D : RealTimeInterval}

/-- The deficit of a compact stage metric at time `t`: `∫ R + 3/(2(t+c)) · vol`. -/
def metricDeficit_O7 {X : OrientedThreeStage.{u}} (m : X.Metric) (c t : ℝ) : ℝ :=
  (∫ x, metricScalarAt m x ∂(riemannianVolumeMeasure ThreeModel X.Carrier m)) +
    3 / (2 * (t + c)) * (riemannianVolumeMeasure ThreeModel X.Carrier m univ).toReal

/-- `φ_d(t) = V(t)(t+c)^{-3/2} - 2 d (t+c)^{-1/2}` for the volume `V` of a metric. -/
def phiDeficit_O7 (V c d t : ℝ) : ℝ :=
  V / (t + c) ^ (3 / 2 : ℝ) - 2 * d / (t + c) ^ (1 / 2 : ℝ)

/-- **Smooth stage.** If the deficit is at least `d` on the interior of a convex set `J` of
regular times, `φ_d` is antitone on `J`. -/
theorem flowVolume_deficit_antitone_O7 (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn S) {c d : ℝ} {J : Set ℝ} (hJconv : Convex ℝ J) (hJ : J ⊆ D.carrier)
    (hint : interior J ⊆ D.regular) (hpos : ∀ t ∈ J, 0 < t + c)
    (hdef : ∀ t ∈ interior J, d ≤ metricDeficit_O7 (S.base.metric t) c t) :
    AntitoneOn (fun t => phiDeficit_O7 (flowVolume_S10 S t) c d t) J := by
  have hcont : ContinuousOn (flowVolume_S10 S) J := (S.continuousOn_volume hS).mono hJ
  have hderiv : ∀ t ∈ interior J,
      HasDerivAt (fun t => phiDeficit_O7 (flowVolume_S10 S t) c d t)
        ((∫ x, - S.scalar t x ∂(riemannianVolumeMeasure ThreeModel P.Carrier (S.family.metric t))) *
            (t + c) ^ (-(3 / 2 : ℝ)) +
          flowVolume_S10 S t * ((-(3 / 2 : ℝ)) * (t + c) ^ (-(3 / 2 : ℝ) - 1)) -
          2 * d * ((-(1 / 2 : ℝ)) * (t + c) ^ (-(1 / 2 : ℝ) - 1))) t := by
    intro t ht
    have h1 := flowVolume_hasDerivAt_S10 S hS (hint ht)
    have hp : 0 < t + c := hpos t (interior_subset ht)
    have h2 : HasDerivAt (fun t => (t + c) ^ (-(3 / 2 : ℝ)))
        ((-(3 / 2 : ℝ)) * (t + c) ^ (-(3 / 2 : ℝ) - 1)) t := by
      have := ((hasDerivAt_id t).add_const c).rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hp.ne')
      simpa using this
    have h3 : HasDerivAt (fun t => (t + c) ^ (-(1 / 2 : ℝ)))
        ((-(1 / 2 : ℝ)) * (t + c) ^ (-(1 / 2 : ℝ) - 1)) t := by
      have := ((hasDerivAt_id t).add_const c).rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hp.ne')
      simpa using this
    have h := (h1.mul h2).sub (h3.const_mul (2 * d))
    apply h.congr_of_eventuallyEq
    filter_upwards [(isOpen_interior.mem_nhds ht)] with r hr
    have hrp : 0 < r + c := hpos r (interior_subset hr)
    simp only [phiDeficit_O7, Pi.sub_apply, Pi.mul_apply]
    rw [Real.rpow_neg hrp.le, Real.rpow_neg hrp.le]
    ring
  refine antitoneOn_of_deriv_nonpos hJconv ?_ ?_ ?_
  · apply ContinuousOn.sub
    · apply hcont.div (ContinuousOn.rpow_const (continuousOn_id.add continuousOn_const)
        (fun t ht => Or.inl (hpos t ht).ne'))
      intro t ht; exact (Real.rpow_pos_of_pos (hpos t ht) _).ne'
    · apply continuousOn_const.div (ContinuousOn.rpow_const (continuousOn_id.add continuousOn_const)
        (fun t ht => Or.inl (hpos t ht).ne'))
      intro t ht; exact (Real.rpow_pos_of_pos (hpos t ht) _).ne'
  · intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hderiv t ht).deriv]
    have hp : 0 < t + c := hpos t (interior_subset ht)
    have hd := hdef t ht
    unfold metricDeficit_O7 at hd
    rw [integral_neg]
    have hscal : (∫ x, S.scalar t x ∂(riemannianVolumeMeasure ThreeModel P.Carrier
        (S.family.metric t))) =
        ∫ x, metricScalarAt (S.base.metric t) x ∂(riemannianVolumeMeasure ThreeModel P.Carrier
          (S.base.metric t)) := rfl
    have hV : flowVolume_S10 S t =
        (riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric t) univ).toReal := rfl
    rw [hscal, hV]
    set A := ∫ x, metricScalarAt (S.base.metric t) x ∂(riemannianVolumeMeasure ThreeModel P.Carrier
          (S.base.metric t))
    set W := (riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric t) univ).toReal
    have hq : 0 < (t + c) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hp _
    have hs1 : (t + c) ^ (-(3 / 2 : ℝ) - 1) = (t + c) ^ (-(3 / 2 : ℝ)) / (t + c) := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    have hs2 : (t + c) ^ (-(1 / 2 : ℝ) - 1) = (t + c) ^ (-(3 / 2 : ℝ)) := by
      norm_num
    rw [hs1, hs2]
    have : -A * (t + c) ^ (-(3 / 2 : ℝ)) + W * (-(3 / 2) * ((t + c) ^ (-(3 / 2 : ℝ)) / (t + c))) -
        2 * d * (-(1 / 2) * (t + c) ^ (-(3 / 2 : ℝ))) =
        -((A + 3 / (2 * (t + c)) * W) - d) * (t + c) ^ (-(3 / 2 : ℝ)) := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ (A + 3 / (2 * (t + c)) * W) - d := by linarith
    nlinarith

/-- The deficit is nonnegative under `R ≥ -3/(2(t+c))`. -/
theorem metricDeficit_nonneg_O7 {X : OrientedThreeStage.{u}} (m : X.Metric) {c t : ℝ}
    (hp : 0 < t + c) (hR : ∀ x, -(3 / (2 * (t + c))) ≤ metricScalarAt m x) :
    0 ≤ metricDeficit_O7 m c t := by
  set μ := riemannianVolumeMeasure ThreeModel X.Carrier m with hμ
  have : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel) (M := X.Carrier) _
  have hk : (0 : ℝ) ≤ 3 / (2 * (t + c)) := by positivity
  unfold metricDeficit_O7
  rw [← hμ]
  by_cases hint : Integrable (fun x => metricScalarAt m x) μ
  · have h1 : 0 ≤ ∫ x, (metricScalarAt m x + 3 / (2 * (t + c))) ∂μ :=
      integral_nonneg (fun x => by simp only [Pi.zero_apply]; linarith [hR x])
    rw [integral_add hint (integrable_const _)] at h1
    simpa [integral_const, smul_eq_mul, Measure.real_def, mul_comm] using h1
  · rw [integral_undef hint]
    have : 0 ≤ (μ univ).toReal := ENNReal.toReal_nonneg
    positivity

theorem phiDeficit_mul_O7 (V c d t : ℝ) (hp : 0 < t + c) :
    V = phiDeficit_O7 V c d t * (t + c) ^ (3 / 2 : ℝ) + 2 * d * (t + c) := by
  have h32 : (t + c) ^ (3 / 2 : ℝ) = (t + c) * (t + c) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one]
  have hsq : (t + c) ^ (1 / 2 : ℝ) * (t + c) ^ (1 / 2 : ℝ) = t + c := by
    rw [← Real.rpow_add hp]; norm_num
  have hr : 0 < (t + c) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp _
  unfold phiDeficit_O7
  rw [h32]
  field_simp
  nlinarith [hsq]

theorem phiDeficit_le_iff_O7 (V c d t φ : ℝ) (hp : 0 < t + c) :
    phiDeficit_O7 V c d t ≤ φ ↔ V ≤ φ * (t + c) ^ (3 / 2 : ℝ) + 2 * d * (t + c) := by
  have hq : 0 < (t + c) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hp _
  conv_rhs => rw [phiDeficit_mul_O7 V c d t hp]
  constructor
  · intro h; nlinarith
  · intro h
    have : phiDeficit_O7 V c d t * (t + c) ^ (3 / 2 : ℝ) ≤ φ * (t + c) ^ (3 / 2 : ℝ) := by linarith
    exact le_of_mul_le_mul_right this hq

private local instance sigmaCompactTRO_O7 {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- **Event step.** Across one event, from any start `a' ∈ [a, s)` of the incoming slab with
deficit `≥ d` on `(a', s)`: `φ_d(out, s) ≤ φ_d(g(a'), a')`. -/
theorem event_step_deficit_O7 {a s : ℝ} (E : MetricCutCapEvent P Q a s) {c d : ℝ} (hc : 0 < c)
    (ha : 0 ≤ a) (a' : ℝ) (haa : a ≤ a') (has' : a' < s)
    (hdef : ∀ t ∈ Ioo a' s, d ≤ metricDeficit_O7 (E.incoming.flow.base.metric t) c t)
    (hB : ∃ K : Set E.incoming.terminalRegularOpen, IsCompact K ∧
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric K) :
    phiDeficit_O7 (riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ).toReal c d s ≤
      phiDeficit_O7 (riemannianVolumeMeasure ThreeModel P.Carrier
        (E.incoming.flow.base.metric a') univ).toReal c d a' := by
  obtain ⟨K, hK, hKle⟩ := hB
  let S := E.incoming.flow
  have hanti := flowVolume_deficit_antitone_O7 S E.incoming.equation (c := c) (d := d)
    (J := Ico a' s) (convex_Ico a' s) (fun t ht => ⟨haa.trans ht.1, ht.2⟩)
    (by
      rw [interior_Ico]
      intro t ht
      exact ⟨lt_of_le_of_lt haa ht.1, ht.2⟩)
    (fun t ht => by have := ht.1; linarith)
    (fun t ht => by rw [interior_Ico] at ht; exact hdef t ht)
  have hspos : 0 < s + c := by linarith
  set φ0 := phiDeficit_O7 (flowVolume_S10 S a') c d a' with hφ0
  let B : ℝ → ℝ := fun t => φ0 * (t + c) ^ (3 / 2 : ℝ) + 2 * d * (t + c)
  have hBcont : ContinuousAt B s := by
    apply ContinuousAt.add
    · exact continuousAt_const.mul ((continuousAt_id.add continuousAt_const).rpow_const
        (Or.inl hspos.ne'))
    · fun_prop
  have hvolB : ∀ t ∈ Ioo a' s, flowVolume_S10 S t ≤ B t := by
    intro t ht
    have htpos : 0 < t + c := by linarith [ht.1]
    have h1 := hanti (show a' ∈ Ico a' s from ⟨le_rfl, has'⟩) ⟨ht.1.le, ht.2⟩ ht.1.le
    exact (phiDeficit_le_iff_O7 _ c d t φ0 htpos).1 h1
  have hBs : 0 ≤ B s := by
    have hlim : Tendsto B (𝓝[<] s) (𝓝 (B s)) := hBcont.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT has'] with t ht
    exact (ENNReal.toReal_nonneg).trans (hvolB t ht)
  have hout : ∀ ε > 0, (riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ).toReal ≤
      B s + ε := by
    intro ε hε
    have hev : ∀ᶠ t in 𝓝[<] s, riemannianVolumeMeasure (I := ThreeModel) (M := P.Carrier)
        (E.incoming.flow.base.metric t) univ ≤ ENNReal.ofReal (B s + ε) := by
      have h1 : ∀ᶠ t in 𝓝[<] s, B t < B s + ε :=
        (hBcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by linarith))
      filter_upwards [h1, Ioo_mem_nhdsLT has'] with t h1t ht
      have hfin : riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric t)
          univ ≠ ⊤ :=
        (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel)
          (M := P.Carrier) _).measure_univ_lt_top.ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal ((hvolB t ht).trans h1t.le)
    have hLK := E.terminal.volume_compact_le_of_eventually_volume_le hK hev
    have hle := hKle.trans hLK
    have hfin2 : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ ≠ ⊤ :=
      (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel)
        (M := Q.Carrier) _).measure_univ_lt_top.ne
    have := (ENNReal.toReal_le_toReal hfin2 ENNReal.ofReal_ne_top).mpr hle
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hout' : (riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ).toReal ≤ B s :=
    le_of_forall_pos_le_add fun ε hε => hout ε hε
  change phiDeficit_O7 _ c d s ≤ φ0
  exact (phiDeficit_le_iff_O7 _ c d s φ0 hspos).2 hout'

/-- **Final slab step.** -/
theorem closed_slab_step_deficit_O7 {a b : ℝ} (G : P.ClosedSlab a b) {c d : ℝ} (hc : 0 < c)
    (ha : 0 ≤ a) (a' : ℝ) (haa : a ≤ a') (hab' : a' ≤ b)
    (hdef : ∀ t ∈ Ioo a' b, d ≤ metricDeficit_O7 (G.flow.base.metric t) c t) :
    phiDeficit_O7 (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric b) univ).toReal
        c d b ≤
      phiDeficit_O7 (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a') univ).toReal
        c d a' := by
  have hanti := flowVolume_deficit_antitone_O7 G.flow G.equation (c := c) (d := d)
    (J := Icc a' b) (convex_Icc a' b) (fun t ht => ⟨haa.trans ht.1, ht.2⟩)
    (by
      rw [interior_Icc]
      intro t ht
      exact ⟨lt_of_le_of_lt haa ht.1, ht.2⟩)
    (fun t ht => by have := ht.1; linarith)
    (fun t ht => by rw [interior_Icc] at ht; exact hdef t ht)
  exact hanti ⟨le_rfl, hab'⟩ ⟨hab', le_rfl⟩ hab'

/-- **History chain.** On one observed history with a final slab, starting at time `T0` in stage
`k0`, with deficit `≥ d` at all smooth times after `T0`: `φ_d(horizon) ≤ φ_d(T0)`. -/
theorem history_chain_deficit_O7 (H : ObservedHistory.{u}) {c d : ℝ} (hc : 0 < c)
    (hlt : H.time (Fin.last H.eventCount) < H.horizon)
    (T0 : ℝ) (hT0 : T0 ≤ H.horizon) (k0 : Fin (H.eventCount + 1)) (hk0 : H.time k0 ≤ T0)
    (hmax : ∀ k, H.time k ≤ T0 → k ≤ k0)
    (hdefEv : ∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), T0 < t →
      d ≤ metricDeficit_O7 ((H.event i).incoming.flow.base.metric t) c t)
    (hdefFin : ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon, T0 < t →
      d ≤ metricDeficit_O7 ((H.finalSlab hlt).flow.base.metric t) c t)
    (hB : ∀ i : Fin H.eventCount, T0 < H.time i.succ →
      ∃ K : Set (H.event i).incoming.terminalRegularOpen, IsCompact K ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric K) :
    phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
        ((H.finalSlab hlt).flow.base.metric H.horizon) univ).toReal c d H.horizon ≤
      phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage k0).Carrier
        (H.stageMetric k0 T0) univ).toReal c d T0 := by
  have hnext : ∀ i : Fin H.eventCount, k0 = i.castSucc → T0 < H.time i.succ := by
    intro i hi
    by_contra hn
    have : i.succ ≤ k0 := hmax _ (not_lt.mp hn)
    rw [hi] at this
    exact absurd this (by simp [Fin.le_def])
  by_cases hl : k0 = Fin.last H.eventCount
  · subst hl
    have h := closed_slab_step_deficit_O7 (H.finalSlab hlt) hc (H.time_nonneg _) T0 hk0 hT0
      (fun t ht => hdefFin t ⟨lt_of_le_of_lt hk0 ht.1, ht.2⟩ ht.1)
    rw [ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt) T0]
    exact h
  · have hstep0 : ∀ i : Fin H.eventCount, k0 = i.castSucc →
        phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
            (H.initialMetric i.succ) univ).toReal c d (H.time i.succ) ≤
          phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage i.castSucc).Carrier
            (H.stageMetric i.castSucc T0) univ).toReal c d T0 := by
      intro i hi
      subst hi
      have hnx := hnext i rfl
      have h := event_step_deficit_O7 (H.event i) hc (H.time_nonneg _) T0 hk0 hnx
        (fun t ht => hdefEv i t ⟨lt_of_le_of_lt hk0 ht.1, ht.2⟩ ht.1) (hB i hnx)
      rw [H.event_output i, stageMetric_castSucc_S10] at *
      exact h
    let Vb : ℝ := phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage k0).Carrier
        (H.stageMetric k0 T0) univ).toReal c d T0
    let w : Fin (H.eventCount + 1) → ℝ := fun j =>
      if j ≤ k0 then Vb else
        phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage j).Carrier
          (H.initialMetric j) univ).toReal c d (H.time j)
    have hw : Antitone w := by
      rw [Fin.antitone_iff_succ_le]
      intro i
      by_cases h1 : i.succ ≤ k0
      · have h2 : i.castSucc ≤ k0 := le_trans (Fin.castSucc_le_succ i) h1
        simp [w, h1, h2]
      · by_cases h2 : i.castSucc ≤ k0
        · have hk : k0 = i.castSucc := by
            apply le_antisymm _ h2
            rw [Fin.le_def] at h1 ⊢
            simp only [Fin.val_succ, Fin.val_castSucc] at h1 ⊢
            omega
          have h := hstep0 i hk
          simp only [w, h1, h2, if_true, if_false]
          subst hk
          exact h
        · have h3 : T0 < H.time i.castSucc := by
            by_contra hn
            exact h2 (hmax _ (not_lt.mp hn))
          have hnx : T0 < H.time i.succ := h3.trans (H.time_strictMono (Fin.castSucc_lt_succ))
          have h := event_step_deficit_O7 (H.event i) hc (H.time_nonneg _) (H.time i.castSucc)
            le_rfl (H.time_strictMono (Fin.castSucc_lt_succ))
            (fun t ht => hdefEv i t ht (h3.trans ht.1)) (hB i hnx)
          rw [H.event_output i, H.event_initial i] at h
          simp only [w, h1, h2, if_false]
          exact h
    have h0 : w (Fin.last H.eventCount) ≤ w 0 := hw (Fin.zero_le _)
    have hz : w 0 = Vb := by simp [w, Fin.zero_le]
    have hlast : ¬ Fin.last H.eventCount ≤ k0 := fun h => hl (le_antisymm (Fin.le_last _) h)
    have hT0l : T0 < H.time (Fin.last H.eventCount) := by
      by_contra hn
      exact hlast (hmax _ (not_lt.mp hn))
    have hfin := closed_slab_step_deficit_O7 (H.finalSlab hlt) hc (H.time_nonneg _)
      (H.time (Fin.last H.eventCount)) le_rfl hlt.le
      (fun t ht => hdefFin t ht (hT0l.trans ht.1))
    rw [H.final_initial hlt] at hfin
    have hul : w (Fin.last H.eventCount) =
        phiDeficit_O7 (riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
          (H.initialMetric (Fin.last H.eventCount)) univ).toReal c d
          (H.time (Fin.last H.eventCount)) := by simp [w, hlast]
    rw [hz, hul] at h0
    exact hfin.trans h0

section Slices

variable {g : P.Metric}

theorem metricDeficit_transport_O7 {A B : OrientedThreeStage.{u}} (h : A = B) {m1 : A.Metric}
    {m2 : B.Metric} (hm : HEq m1 m2) (c t : ℝ) :
    metricDeficit_O7 m1 c t = metricDeficit_O7 m2 c t := by
  subst h
  cases eq_of_heq hm
  rfl

/-- The deficit of the post-surgery slice at time `t ∈ (0, B]` is the deficit read in the
active stage of `observe B`. -/
theorem metricDeficit_postMetric_eq_O7 (O : ObservationTower P g) (B : ℝ) (hB : 0 ≤ B)
    (t : ℝ) (ht : 0 < t) (htB : t ≤ B) (c : ℝ) :
    metricDeficit_O7 (GC.LongTime.postMetric O t) c t =
      metricDeficit_O7 ((O.observe B hB).stageMetric
        ((O.observe B hB).activeStage ⟨t, ht.le, htB⟩) t) c t := by
  have key : ∀ (b : ℝ) (hb : 0 ≤ b), b = t →
      metricDeficit_O7 ((O.observe b hb).stageMetric (Fin.last (O.observe b hb).eventCount) b) c t =
        metricDeficit_O7 ((O.observe t ht.le).stageMetric
          (Fin.last (O.observe t ht.le).eventCount) t) c t := by
    intro b hb hbt
    subst hbt
    rfl
  have h1 : metricDeficit_O7 (GC.LongTime.postMetric O t) c t =
      metricDeficit_O7 ((O.observe t ht.le).stageMetric
        (Fin.last (O.observe t ht.le).eventCount) t) c t :=
    key (max t 0) (le_max_right t 0) (max_eq_left ht.le)
  rw [h1]
  let t' : Icc (0 : ℝ) t := ⟨t, ht.le, le_rfl⟩
  have hst := O.observe_slice_stage t B ht.le hB htB t'
  have hme := O.observe_slice_metric t B ht.le hB htB t'
  have hact : (O.observe t ht.le).activeStage t' = Fin.last (O.observe t ht.le).eventCount :=
    (O.observe t ht.le).activeStage_at_horizon
  have hst' : (O.observe t ht.le).stage (Fin.last (O.observe t ht.le).eventCount) =
      (O.observe B hB).stage ((O.observe B hB).activeStage ⟨t, ht.le, htB⟩) := by
    rw [← hact]; exact hst
  have hme' : HEq ((O.observe t ht.le).stageMetric (Fin.last (O.observe t ht.le).eventCount) t)
      ((O.observe B hB).stageMetric ((O.observe B hB).activeStage ⟨t, ht.le, htB⟩) t) := by
    rw [← hact]; exact hme
  exact metricDeficit_transport_O7 hst' hme' c t

end Slices

section SliceStep

variable {g : P.Metric}

/-- A time strictly between two consecutive event times of `observe B` is not an event time. -/
theorem not_mem_eventTimes_of_between_O7 (O : ObservationTower P g) (B : ℝ) (hB : 0 ≤ B)
    {t : ℝ} (ht0 : 0 < t) (htB : t ≤ B)
    (hgap : ∀ j : Fin ((O.observe B hB).eventCount), (O.observe B hB).time j.succ ≠ t) :
    t ∉ O.eventTimes := by
  intro hmem
  have : t ∈ O.eventTimes ∩ Ioc 0 B := ⟨hmem, ht0, htB⟩
  rw [O.eventTimes_inter B hB] at this
  obtain ⟨j, hj⟩ := this
  exact hgap j hj

/-- **Slice step.** For regular slices `s₁, s₂` with `s₁.time ≤ s₂.time` and deficit `≥ d` at all
non-event times between them, `φ_d(s₂) ≤ φ_d(s₁)`. -/
theorem slice_step_deficit_O7 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (s1 s2 : GC.LongTime.RegularSlice F.observation)
    (h12 : s1.time ≤ s2.time) {d : ℝ}
    (hdef : ∀ t ∈ Ioo s1.time s2.time, t ∉ F.observation.eventTimes →
      d ≤ metricDeficit_O7 (GC.LongTime.postMetric F.observation t) Hp.scalarShift t) :
    phiDeficit_O7 (riemannianVolumeMeasure ThreeModel s2.stage.Carrier s2.metric univ).toReal
        Hp.scalarShift d s2.time ≤
      phiDeficit_O7 (riemannianVolumeMeasure ThreeModel s1.stage.Carrier s1.metric univ).toReal
        Hp.scalarShift d s1.time := by
  set c := Hp.scalarShift with hcdef
  have hc : 0 < c := Hp.scalarShift_pos
  let H := s2.history
  have hlt : H.time (Fin.last H.eventCount) < H.horizon := s2.preceding
  have hT0 : s1.time ≤ H.horizon := h12
  let T0i : Icc (0 : ℝ) H.horizon := ⟨s1.time, s1.positive.le, hT0⟩
  let k0 := H.activeStage T0i
  have hk0 : H.time k0 ≤ s1.time := H.activeStage_time_le T0i
  have hmax : ∀ k, H.time k ≤ s1.time → k ≤ k0 := fun k hk => H.le_activeStage T0i k hk
  have hpos : ∀ t, s1.time < t → 0 < t := fun t ht => s1.positive.trans ht
  -- the deficit inside the smooth intervals of `H`
  have hgapEv : ∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      ∀ j : Fin H.eventCount, H.time j.succ ≠ t := by
    intro i t ht j hj
    rw [← hj] at ht
    rcases lt_trichotomy j.succ i.succ with h | h | h
    · have h1 : j.succ ≤ i.castSucc := by
        rw [Fin.le_def]; rw [Fin.lt_def] at h; simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
        omega
      have := H.time_strictMono.monotone h1
      linarith [ht.1]
    · rw [h] at ht; exact lt_irrefl _ ht.2
    · have := H.time_strictMono h
      linarith [ht.2]
  have hdefEv : ∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      s1.time < t → d ≤ metricDeficit_O7 ((H.event i).incoming.flow.base.metric t) c t := by
    intro i t ht hT0t
    have htB : t ≤ H.horizon := ht.2.le.trans (H.time_le_horizon_at i.succ)
    have ht0 : 0 < t := hpos t hT0t
    have hne := not_mem_eventTimes_of_between_O7 F.observation s2.time s2.positive.le ht0 htB
      (hgapEv i t ht)
    have h1 := hdef t ⟨hT0t, lt_of_lt_of_le ht.2 (H.time_le_horizon_at i.succ)⟩ hne
    rw [metricDeficit_postMetric_eq_O7 F.observation s2.time s2.positive.le t ht0 htB c] at h1
    have hact : H.activeStage ⟨t, ht0.le, htB⟩ = i.castSucc := by
      apply H.activeStage_eq_of_maximal _ _ ht.1.le
      intro k hk
      by_contra hlt'
      have h1 : i.castSucc < k := by simpa using hlt'
      have h2 : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp h1
      have := H.time_strictMono.monotone h2
      linarith [ht.2, hk]
    change d ≤ metricDeficit_O7 (H.stageMetric (H.activeStage ⟨t, ht0.le, htB⟩) t) c t at h1
    generalize hj : H.activeStage ⟨t, ht0.le, htB⟩ = j at h1
    rw [hj] at hact
    subst hact
    rw [stageMetric_castSucc_S10] at h1
    exact h1
  have hdefFin : ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon, s1.time < t →
      d ≤ metricDeficit_O7 ((H.finalSlab hlt).flow.base.metric t) c t := by
    intro t ht hT0t
    have htB : t ≤ H.horizon := ht.2.le
    have ht0 : 0 < t := hpos t hT0t
    have hgap : ∀ j : Fin H.eventCount, H.time j.succ ≠ t := by
      intro j hj
      have := H.time_strictMono.monotone (Fin.le_last j.succ)
      linarith [ht.1]
    have hne := not_mem_eventTimes_of_between_O7 F.observation s2.time s2.positive.le ht0 htB hgap
    have h1 := hdef t ⟨hT0t, ht.2⟩ hne
    rw [metricDeficit_postMetric_eq_O7 F.observation s2.time s2.positive.le t ht0 htB c] at h1
    have hact : H.activeStage ⟨t, ht0.le, htB⟩ = Fin.last H.eventCount := by
      apply le_antisymm (Fin.le_last _)
      exact H.le_activeStage _ _ ht.1.le
    change d ≤ metricDeficit_O7 (H.stageMetric (H.activeStage ⟨t, ht0.le, htB⟩) t) c t at h1
    generalize hj : H.activeStage ⟨t, ht0.le, htB⟩ = j at h1
    rw [hj] at hact
    subst hact
    rw [ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt) t] at h1
    exact h1
  have hBt : ∀ n (i : Fin (F.tower.history n).eventCount),
      ∃ K : Set ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen, IsCompact K ∧
        riemannianVolumeMeasure ThreeModel ((F.tower.history n).toHistory.stage i.succ).Carrier
            ((F.tower.history n).toHistory.event i).outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel
            ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen
            ((F.tower.history n).toHistory.event i).terminal.metric K :=
    fun n i => event_volume_le_compact_S14 (Hp.records n i)
  have hB : ∀ i : Fin H.eventCount, ∃ K : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact K ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric K :=
    fun i => hBt (Nat.ceil s2.time) (Fin.castLE (Nat.le_of_lt_succ
      ((F.tower.history (Nat.ceil s2.time)).toHistory.activeStage ⟨s2.time, s2.positive.le,
        by have := F.observation.horizon_eq (Nat.ceil s2.time); exact this ▸ Nat.le_ceil _⟩).isLt) i)
  have hchain := history_chain_deficit_O7 H hc hlt s1.time hT0 k0 hk0 hmax hdefEv hdefFin
    (fun i _ => hB i)
  have hvol1 := slice_vol_eq_S10 F.observation s1.time s2.time s1.positive.le s2.positive.le h12
  have hmet2 : s2.metric = (H.finalSlab hlt).flow.base.metric s2.time :=
    ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt) s2.time
  change phiDeficit_O7 (riemannianVolumeMeasure ThreeModel s2.stage.Carrier s2.metric univ).toReal
      c d s2.time ≤ phiDeficit_O7 (riemannianVolumeMeasure ThreeModel
        ((F.observation.observe s1.time s1.positive.le).stage
          (Fin.last (F.observation.observe s1.time s1.positive.le).eventCount)).Carrier
        ((F.observation.observe s1.time s1.positive.le).stageMetric
          (Fin.last (F.observation.observe s1.time s1.positive.le).eventCount) s1.time) univ).toReal
        c d s1.time
  rw [hvol1, hmet2]
  exact hchain

end SliceStep

section Windows

variable {g : P.Metric}

/-- **D1 (sequence form).** There is no infinite ordered sequence of disjoint windows
`[(sa j).time, (sb j).time]` on each of which the deficit is at least `d j ≥ 0`, with a fixed
positive lower bound `δ₀` for the window weights `2 d (α+c)^{-1/2} - 2 d (β+c)^{-1/2}`. -/
theorem deficit_windows_impossible_O7 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (sa sb : ℕ → GC.LongTime.RegularSlice F.observation) (d : ℕ → ℝ)
    (hab : ∀ j, (sa j).time ≤ (sb j).time) (hba : ∀ j, (sb j).time ≤ (sa (j + 1)).time)
    (hdef : ∀ j, ∀ t ∈ Ioo (sa j).time (sb j).time, t ∉ F.observation.eventTimes →
      d j ≤ metricDeficit_O7 (GC.LongTime.postMetric F.observation t) Hp.scalarShift t)
    (hW : ∀ j, δ₀ ≤ 2 * d j / ((sa j).time + Hp.scalarShift) ^ (1 / 2 : ℝ) -
      2 * d j / ((sb j).time + Hp.scalarShift) ^ (1 / 2 : ℝ)) : False := by
  set c := Hp.scalarShift with hcdef
  have hc : 0 < c := Hp.scalarShift_pos
  let f : GC.LongTime.RegularSlice F.observation → ℝ := fun s =>
    phiDeficit_O7 (riemannianVolumeMeasure ThreeModel s.stage.Carrier s.metric univ).toReal c 0 s.time
  have hf0 : ∀ s : GC.LongTime.RegularSlice F.observation, 0 ≤ f s := by
    intro s
    simp only [f, phiDeficit_O7, mul_zero, zero_div, sub_zero]
    have : 0 < s.time + c := by linarith [s.positive]
    positivity
  -- the window step
  have hwin : ∀ j, f (sb j) + δ₀ ≤ f (sa j) := by
    intro j
    have h := slice_step_deficit_O7 Hp (sa j) (sb j) (hab j) (hdef j)
    have hW' := hW j
    simp only [f, phiDeficit_O7, mul_zero, zero_div, sub_zero] at h ⊢
    linarith
  -- between windows: deficit ≥ 0
  have hgap : ∀ j, f (sa (j + 1)) ≤ f (sb j) := by
    intro j
    apply slice_step_deficit_O7 Hp (sb j) (sa (j + 1)) (hba j)
    intro t ht _
    have ht0 : 0 < t := (sb j).positive.trans ht.1
    apply metricDeficit_nonneg_O7 _ (by linarith)
    intro x
    have := Hp.scalar_lower t ht0.le x
    rw [neg_div] at this
    exact this
  have hind : ∀ k : ℕ, ((k : ℝ) + 1) * δ₀ + f (sb k) ≤ f (sa 0) := by
    intro k
    induction k with
    | zero => have := hwin 0; simp; linarith
    | succ k ih =>
      have h1 := hwin (k + 1)
      have h2 := hgap k
      push_cast
      nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt (f (sa 0) / δ₀)
  have h := hind k
  have := hf0 (sb k)
  rw [div_lt_iff₀ hδ₀] at hk
  nlinarith

end Windows

end GC.LongTime.Ch12
