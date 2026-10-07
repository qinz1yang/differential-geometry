import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeEarly_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeMain_S10

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
open scoped ENNReal
universe u
namespace GC.LongTime.Ch12

private local instance sigmaCompactTRO_LM {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G : Q.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem vol_transport_S10 {A B : OrientedThreeStage.{u}} (h : A = B) {m1 : A.Metric}
    {m2 : B.Metric} (hm : HEq m1 m2) :
    riemannianVolumeMeasure ThreeModel A.Carrier m1 univ =
      riemannianVolumeMeasure ThreeModel B.Carrier m2 univ := by
  subst h
  cases eq_of_heq hm
  rfl

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- Volume at time `a` is the same whether read in `observe a` or in `observe b`, `a ≤ b`. -/
theorem slice_vol_eq_S10 (O : ObservationTower P g) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    (riemannianVolumeMeasure ThreeModel ((O.observe a ha).stage (Fin.last (O.observe a ha).eventCount)).Carrier
      ((O.observe a ha).stageMetric (Fin.last (O.observe a ha).eventCount) a) univ).toReal =
    (riemannianVolumeMeasure ThreeModel
      ((O.observe b hb).stage ((O.observe b hb).activeStage ⟨a, ha, hab⟩)).Carrier
      ((O.observe b hb).stageMetric ((O.observe b hb).activeStage ⟨a, ha, hab⟩) a) univ).toReal := by
  let t' : Icc (0 : ℝ) a := ⟨a, ha, le_rfl⟩
  have hst := O.observe_slice_stage a b ha hb hab t'
  have hme := O.observe_slice_metric a b ha hb hab t'
  have hact : (O.observe a ha).activeStage t' = Fin.last (O.observe a ha).eventCount :=
    (O.observe a ha).activeStage_at_horizon
  have hst' : (O.observe a ha).stage (Fin.last (O.observe a ha).eventCount) =
      (O.observe b hb).stage ((O.observe b hb).activeStage ⟨a, ha, hab⟩) := by
    rw [← hact]
    exact hst
  have hme' : HEq ((O.observe a ha).stageMetric (Fin.last (O.observe a ha).eventCount) a)
      ((O.observe b hb).stageMetric ((O.observe b hb).activeStage ⟨a, ha, hab⟩) a) := by
    rw [← hact]
    exact hme
  rw [vol_transport_S10 hst' hme']

/-- `hBLate` (VB-B for late events only): all events at time `≥ T` have the volume input. -/
theorem normalized_volume_bounded_of_lateEventBound_S10 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ)
    (hBLate : ∃ T : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
      T ≤ (F.tower.history n).toHistory.time i.succ →
      ∃ K : Set ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen, IsCompact K ∧
        riemannianVolumeMeasure ThreeModel ((F.tower.history n).toHistory.stage i.succ).Carrier
            ((F.tower.history n).toHistory.event i).outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel
            ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen
            ((F.tower.history n).toHistory.event i).terminal.metric K) :
    ∃ V : ℝ, 0 < V ∧ ∀ s : RegularSlice F.observation, 1 ≤ s.time →
      normalizedTotalVolume s ≤ ENNReal.ofReal V := by
  obtain ⟨T, hT⟩ := hBLate
  set c := Hp.scalarShift with hcdef
  have hc : 0 < c := Hp.scalarShift_pos
  obtain ⟨B1, hB1pos, hB1gt, -, hpre, -⟩ := F.regular_prefix (max T 1)
  have hB1T : T < B1 := lt_of_le_of_lt (le_max_left _ _) hB1gt
  have hB11 : 1 < B1 := lt_of_le_of_lt (le_max_right _ _) hB1gt
  let HS := F.observation.observe B1 hB1pos.le
  have hltS : HS.time (Fin.last HS.eventCount) < HS.horizon := hpre
  obtain ⟨hRevS, hRfinS⟩ := observed_history_scalar_lower_S10 Hp B1 hB1pos.le
  set M1 : ℝ := (∑ k : Fin (HS.eventCount + 1),
        (riemannianVolumeMeasure ThreeModel (HS.stage k).Carrier (HS.initialMetric k) univ).toReal) *
        ((HS.horizon + c) ^ (3 / 2 : ℝ) / c ^ (3 / 2 : ℝ)) with hM1
  set W0 : ℝ := (riemannianVolumeMeasure ThreeModel (HS.stage (Fin.last HS.eventCount)).Carrier
      (HS.stageMetric (Fin.last HS.eventCount) B1) univ).toReal with hW0
  have hM1nn : 0 ≤ M1 := by
    rw [hM1]
    have : 0 ≤ HS.horizon := HS.horizon_nonneg
    have h1 : 0 ≤ ∑ k : Fin (HS.eventCount + 1),
        (riemannianVolumeMeasure ThreeModel (HS.stage k).Carrier (HS.initialMetric k) univ).toReal :=
      Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    exact mul_nonneg h1 (div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hc.le _))
  have hW0nn : 0 ≤ W0 := ENNReal.toReal_nonneg
  set D : ℝ := W0 / (B1 + c) ^ (3 / 2 : ℝ) * (1 + c) ^ (3 / 2 : ℝ) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (div_nonneg hW0nn (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _)
  refine ⟨M1 + D + 1, by linarith, ?_⟩
  intro s hs
  have ht : 0 < s.time := s.positive
  have hp : ∀ x : ℝ, 0 ≤ x → x ^ (3 / 2 : ℝ) = (Real.sqrt x) ^ 3 := by
    intro x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hfin : sliceTotalVolume_S10 s ≠ ⊤ := by
    unfold sliceTotalVolume_S10
    exact (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel)
      (M := s.stage.Carrier) _).measure_univ_lt_top.ne
  have hsq : (Real.sqrt s.time⁻¹) ^ 3 ≤ 1 := by
    apply pow_le_one₀ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_one]
    exact inv_le_one_of_one_le₀ hs
  rw [normalizedTotalVolume_eq_S10]
  by_cases hcase : s.time ≤ B1
  · -- early slice: bound inside the single history `HS`
    have hbound : (sliceTotalVolume_S10 s).toReal ≤ M1 := by
      have h1 := slice_vol_eq_S10 F.observation s.time B1 ht.le hB1pos.le hcase
      have h2 := history_slice_bound_S10 HS hc hltS hRevS (hRfinS hltS) s.time
        (HS.activeStage ⟨s.time, ht.le, hcase⟩) (HS.activeStage_time_le _) hcase
        (fun i hi => by
          have := HS.activeStage_before_next ⟨s.time, ht.le, hcase⟩
          have hv : (HS.activeStage ⟨s.time, ht.le, hcase⟩).val < HS.eventCount := by
            rw [hi]; exact i.isLt
          have h3 := this hv
          have : (⟨(HS.activeStage ⟨s.time, ht.le, hcase⟩).val + 1, by omega⟩ : Fin (HS.eventCount + 1)) = i.succ := by
            apply Fin.ext
            simp [hi]
          rw [this] at h3
          exact h3)
      exact h1 ▸ h2
    have hle : sliceTotalVolume_S10 s ≤ ENNReal.ofReal M1 := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hbound
    calc ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 * sliceTotalVolume_S10 s
        ≤ ENNReal.ofReal 1 * ENNReal.ofReal M1 := by
          gcongr
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hsq
      _ ≤ ENNReal.ofReal (M1 + D + 1) := by
          rw [← ENNReal.ofReal_mul zero_le_one]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- late slice: chain from time `B1`
    have hlt : s.history.time (Fin.last s.history.eventCount) < s.history.horizon := s.preceding
    obtain ⟨hRev, hRfin⟩ := observed_history_scalar_lower_S10 Hp s.time ht.le
    have hBs : B1 < s.time := not_le.mp hcase
    have hchain := history_late_chain_S10 s.history hc hlt hRev (hRfin hlt) B1 hBs
      (s.history.activeStage ⟨B1, hB1pos.le, hBs.le⟩)
      (s.history.activeStage_time_le _)
      (fun k hk => s.history.le_activeStage _ k hk)
      (fun i hi => hT (Nat.ceil s.time) (Fin.castLE (Nat.le_of_lt_succ
        ((F.tower.history (Nat.ceil s.time)).toHistory.activeStage ⟨s.time, s.positive.le,
          by have := F.observation.horizon_eq (Nat.ceil s.time); exact this ▸ Nat.le_ceil _⟩).isLt) i)
        (le_of_lt (hB1T.trans hi)))
    have h1 := slice_vol_eq_S10 F.observation B1 s.time hB1pos.le ht.le hBs.le
    have hmet : s.metric = (s.history.finalSlab hlt).flow.base.metric s.time :=
      ObservedHistory.stageMetric_last_of_lt (H := s.history) (h := hlt) s.time
    have hvolS : (sliceTotalVolume_S10 s).toReal =
        (riemannianVolumeMeasure ThreeModel (s.history.stage (Fin.last s.history.eventCount)).Carrier
          ((s.history.finalSlab hlt).flow.base.metric s.history.horizon) univ).toReal := by
      unfold sliceTotalVolume_S10
      rw [hmet]
      rfl
    rw [← hvolS, ← h1] at hchain
    have hpt : 0 < (s.time + c) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hb1 : (sliceTotalVolume_S10 s).toReal ≤ W0 / (B1 + c) ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ) := by
      have := (div_le_iff₀ hpt).mp hchain
      exact this
    have hreal : (Real.sqrt s.time⁻¹) ^ 3 * (W0 / (B1 + c) ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ)) ≤ D := by
      rw [hD, hp (s.time + c) (by linarith), hp (1 + c) (by linarith)]
      have h1 : (Real.sqrt s.time⁻¹) ^ 3 * (Real.sqrt (s.time + c)) ^ 3 ≤ (Real.sqrt (1 + c)) ^ 3 := by
        rw [← mul_pow, ← Real.sqrt_mul (inv_pos.mpr ht).le]
        apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
        apply Real.sqrt_le_sqrt
        rw [inv_mul_le_iff₀ ht]
        nlinarith
      have h0 : 0 ≤ W0 / (B1 + c) ^ (3 / 2 : ℝ) := div_nonneg hW0nn (Real.rpow_nonneg (by linarith) _)
      calc _ = W0 / (B1 + c) ^ (3 / 2 : ℝ) * ((Real.sqrt s.time⁻¹) ^ 3 * (Real.sqrt (s.time + c)) ^ 3) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 h0
    have hle : sliceTotalVolume_S10 s ≤ ENNReal.ofReal (W0 / (B1 + c) ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hb1
    calc ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 * sliceTotalVolume_S10 s
        ≤ ENNReal.ofReal (Real.sqrt s.time⁻¹) ^ 3 *
          ENNReal.ofReal (W0 / (B1 + c) ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal ((Real.sqrt s.time⁻¹) ^ 3 * (W0 / (B1 + c) ^ (3 / 2 : ℝ) * (s.time + c) ^ (3 / 2 : ℝ))) := by
          rw [ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) _), ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
      _ ≤ ENNReal.ofReal (M1 + D + 1) := ENNReal.ofReal_le_ofReal (by linarith)

end GC.LongTime.Ch12
