import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeEvent_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeInit_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeScalar_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeAssembly_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
open scoped ENNReal
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

private local instance sigmaCompactTRO_S10' {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G : Q.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- Scalar lower bound on every smooth interval of the observed history `observe b`. -/
theorem observed_history_scalar_lower_S10 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (b : ℝ) (hb : 0 ≤ b) :
    let H := F.observation.observe b hb
    (∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), ∀ x,
      -(3 / (2 * (t + Hp.scalarShift))) ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x) ∧
    (∀ hlt : H.time (Fin.last H.eventCount) < H.horizon,
      ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon, ∀ x,
      -(3 / (2 * (t + Hp.scalarShift))) ≤ metricScalarAt ((H.finalSlab hlt).flow.base.metric t) x) := by
  intro H
  have hlow := postMetric_lower_on_observe_S10 F.observation (fun t => -(3 / (2 * (t + Hp.scalarShift))))
    (fun t ht x => by rw [← neg_div]; exact Hp.scalar_lower t ht x) b hb
  constructor
  · intro i t ht x
    have htb : t ≤ b := by
      have := H.time_le_horizon_at i.succ
      exact ht.2.le.trans this
    have ht0 : 0 ≤ t := (H.time_nonneg _).trans ht.1.le
    have hact : H.activeStage ⟨t, ht0, htb⟩ = i.castSucc := by
      apply H.activeStage_eq_of_maximal _ _ ht.1.le
      intro k hk
      by_contra hlt
      have h1 : i.castSucc < k := by simpa using hlt
      have h2 : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp h1
      have := H.time_strictMono.monotone h2
      linarith [ht.2, hk]
    have := hlow ⟨t, ht0, htb⟩
    generalize hj : H.activeStage ⟨t, ht0, htb⟩ = j at this
    rw [hj] at hact
    subst hact
    have e : H.stageMetric i.castSucc = (H.event i).incoming.flow.base.metric := by
      unfold ObservedHistory.stageMetric
      rw [Fin.lastCases_castSucc]
    have h3 := this x
    rw [e] at h3
    exact h3
  · intro hlt t ht x
    have htb : t ≤ b := ht.2.le
    have ht0 : 0 ≤ t := (H.time_nonneg _).trans ht.1.le
    have hact : H.activeStage ⟨t, ht0, htb⟩ = Fin.last H.eventCount := by
      apply le_antisymm (Fin.le_last _)
      exact H.le_activeStage _ _ ht.1.le
    have := hlow ⟨t, ht0, htb⟩
    generalize hj : H.activeStage ⟨t, ht0, htb⟩ = j at this
    rw [hj] at hact
    subst hact
    have e := ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt) t
    have := this x
    rw [e] at this
    exact this

/-- VB-D final assembly: with the explicit per-event input `hB` (VB-B: every actual event of every
retained history has `vol(output) ≤ vol_L(K)` for a compact `K` of the terminal regular open set),
the normalised total volume is bounded on slices `t ≥ 1`. -/
theorem normalized_volume_bounded_of_eventBound_S10 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ)
    (hB : ∀ n (i : Fin (F.tower.history n).eventCount),
      ∃ K : Set ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen, IsCompact K ∧
        riemannianVolumeMeasure ThreeModel ((F.tower.history n).toHistory.stage i.succ).Carrier
            ((F.tower.history n).toHistory.event i).outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel
            ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen
            ((F.tower.history n).toHistory.event i).terminal.metric K) :
    ∃ V : ℝ, 0 < V ∧ ∀ s : RegularSlice F.observation, 1 ≤ s.time →
      normalizedTotalVolume s ≤ ENNReal.ofReal V := by
  set c := Hp.scalarShift with hcdef
  have hc : 0 < c := Hp.scalarShift_pos
  set V0 := (riemannianVolumeMeasure ThreeModel P.Carrier g univ).toReal with hV0
  set V : ℝ := V0 / c ^ (3 / 2 : ℝ) * (1 + c) ^ (3 / 2 : ℝ) + 1 with hVdef
  have hV0nn : 0 ≤ V0 := ENNReal.toReal_nonneg
  have hVnn : 0 ≤ V0 / c ^ (3 / 2 : ℝ) * (1 + c) ^ (3 / 2 : ℝ) := by positivity
  refine ⟨V, by rw [hVdef]; linarith, ?_⟩
  intro s hs
  have hlt : s.history.time (Fin.last s.history.eventCount) < s.history.horizon := s.preceding
  obtain ⟨hRev, hRfin⟩ := observed_history_scalar_lower_S10 Hp s.time s.positive.le
  have hbound := history_volume_bound_S10 s.history hc hlt hRev (hRfin hlt)
    (fun i => hB (Nat.ceil s.time) (Fin.castLE (Nat.le_of_lt_succ
      ((F.tower.history (Nat.ceil s.time)).toHistory.activeStage ⟨s.time, s.positive.le,
        by have := F.observation.horizon_eq (Nat.ceil s.time); exact this ▸ Nat.le_ceil _⟩).isLt) i))
  have hp : ∀ x : ℝ, 0 ≤ x → x ^ (3 / 2 : ℝ) = (Real.sqrt x) ^ 3 := by
    intro x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hvol0 : (riemannianVolumeMeasure ThreeModel (s.history.stage 0).Carrier
      (s.history.initialMetric 0) univ).toReal = V0 := by
    rw [initial_volume_eq_S10 s.initial]
  have hmet : s.metric = (s.history.finalSlab hlt).flow.base.metric s.time :=
    ObservedHistory.stageMetric_last_of_lt (H := s.history) (h := hlt) s.time
  have hvolS : sliceTotalVolume_S10 s =
      riemannianVolumeMeasure ThreeModel (s.history.stage (Fin.last s.history.eventCount)).Carrier
        ((s.history.finalSlab hlt).flow.base.metric s.time) univ := by
    unfold sliceTotalVolume_S10
    rw [hmet]
  have hfin : sliceTotalVolume_S10 s ≠ ⊤ := by
    unfold sliceTotalVolume_S10
    exact (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel)
      (M := s.stage.Carrier) _).measure_univ_lt_top.ne
  have ht : 0 < s.time := s.positive
  have hb1 : (sliceTotalVolume_S10 s).toReal ≤ V0 / c ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ) := by
    rw [hvolS]
    have := hbound
    rw [hvol0] at this
    exact this
  -- real inequality
  have hreal : (Real.sqrt s.time⁻¹) ^ 3 * (V0 / c ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ)) ≤
      V0 / c ^ (3 / 2 : ℝ) * (1 + c) ^ (3 / 2 : ℝ) := by
    rw [hp (s.time + c) (by linarith), hp (1 + c) (by linarith)]
    have h1 : (Real.sqrt s.time⁻¹) ^ 3 * (Real.sqrt (s.time + c)) ^ 3 ≤ (Real.sqrt (1 + c)) ^ 3 := by
      rw [← mul_pow, ← Real.sqrt_mul (inv_pos.mpr ht).le]
      apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_sqrt
      rw [inv_mul_le_iff₀ ht]
      nlinarith
    have h0 : 0 ≤ V0 / c ^ (3 / 2 : ℝ) := by positivity
    calc _ = V0 / c ^ (3 / 2 : ℝ) * ((Real.sqrt s.time⁻¹) ^ 3 * (Real.sqrt (s.time + c)) ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h0
  rw [normalizedTotalVolume_eq_S10]
  have hle : sliceTotalVolume_S10 s ≤ ENNReal.ofReal (V0 / c ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hb1
  calc ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 * sliceTotalVolume_S10 s
      ≤ ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 *
        ENNReal.ofReal (V0 / c ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal ((Real.sqrt s.time⁻¹) ^ 3 * (V0 / c ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ))) := by
        rw [ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) _), ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
    _ ≤ ENNReal.ofReal V := ENNReal.ofReal_le_ofReal (by rw [hVdef]; linarith)

end GC.LongTime.Ch12
