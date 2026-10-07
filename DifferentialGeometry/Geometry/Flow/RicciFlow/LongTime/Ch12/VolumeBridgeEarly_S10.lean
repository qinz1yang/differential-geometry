import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeLateHist_S10

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ENNReal
universe u
namespace GC.LongTime.Ch12

/-- From `V(t)/(t+c)^p ≤ V(a)/(a+c)^p` to a bound by `V(a) ((T+c)/c)^p`. -/
theorem vol_le_of_normalized_S10 {V₁ V₀ a t T c : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hat : a ≤ t)
    (htT : t ≤ T) (hV₀ : 0 ≤ V₀) (hV₁ : 0 ≤ V₁)
    (h : V₁ / (t + c) ^ (3 / 2 : ℝ) ≤ V₀ / (a + c) ^ (3 / 2 : ℝ)) :
    V₁ ≤ V₀ * ((T + c) ^ (3 / 2 : ℝ) / c ^ (3 / 2 : ℝ)) := by
  have htp : 0 < (t + c) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hap : 0 < (a + c) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hcp : 0 < c ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hc _
  rw [div_le_div_iff₀ htp hap] at h
  have h1 : c ^ (3 / 2 : ℝ) ≤ (a + c) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hc.le (by linarith) (by norm_num)
  have h2 : (t + c) ^ (3 / 2 : ℝ) ≤ (T + c) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  rw [mul_div_assoc', le_div_iff₀ hcp]
  have : V₁ * (a + c) ^ (3 / 2 : ℝ) ≤ V₀ * (t + c) ^ (3 / 2 : ℝ) := h
  have hV1 : V₁ * c ^ (3 / 2 : ℝ) ≤ V₁ * (a + c) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left h1 hV₁
  have hV2 : V₀ * (t + c) ^ (3 / 2 : ℝ) ≤ V₀ * (T + c) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left h2 hV₀
  linarith

theorem flowVolume_le_of_anti_S10 {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) {c a t T : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (hat : a ≤ t) (htT : t ≤ T)
    (hanti : AntitoneOn (fun t => flowVolume_S10 S t * (t + c) ^ (-(3 / 2 : ℝ))) D.carrier)
    (haD : a ∈ D.carrier) (htD : t ∈ D.carrier) :
    flowVolume_S10 S t ≤ flowVolume_S10 S a * ((T + c) ^ (3 / 2 : ℝ) / c ^ (3 / 2 : ℝ)) := by
  have h := hanti haD htD hat
  have hp1 : 0 < t + c := by linarith
  have hp2 : 0 < a + c := by linarith
  simp only [Real.rpow_neg hp1.le, Real.rpow_neg hp2.le] at h
  have hd : flowVolume_S10 S t / (t + c) ^ (3 / 2 : ℝ) ≤ flowVolume_S10 S a / (a + c) ^ (3 / 2 : ℝ) := by
    simpa [div_eq_mul_inv] using h
  exact vol_le_of_normalized_S10 hc ha hat htT ENNReal.toReal_nonneg ENNReal.toReal_nonneg hd

/-- Early bound inside one observed history: every slice volume is at most
`(Σ_j vol(g_j(init))) ((T+c)/c)^{3/2}`. -/
theorem history_slice_bound_S10 (H : ObservedHistory.{u}) {c : ℝ} (hc : 0 < c)
    (hlt : H.time (Fin.last H.eventCount) < H.horizon)
    (hRev : ∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), ∀ x,
      -(3 / (2 * (t + c))) ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hRfin : ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon, ∀ x,
      -(3 / (2 * (t + c))) ≤ metricScalarAt ((H.finalSlab hlt).flow.base.metric t) x)
    (t : ℝ) (j : Fin (H.eventCount + 1)) (hj : H.time j ≤ t) (hth : t ≤ H.horizon)
    (hnext : ∀ i : Fin H.eventCount, j = i.castSucc → t < H.time i.succ) :
    (riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.stageMetric j t) univ).toReal ≤
      (∑ k : Fin (H.eventCount + 1),
        (riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.initialMetric k) univ).toReal) *
        ((H.horizon + c) ^ (3 / 2 : ℝ) / c ^ (3 / 2 : ℝ)) := by
  have hnn : ∀ k : Fin (H.eventCount + 1),
      0 ≤ (riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.initialMetric k) univ).toReal :=
    fun k => ENNReal.toReal_nonneg
  have hsum : ∀ k : Fin (H.eventCount + 1),
      (riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.initialMetric k) univ).toReal ≤
      ∑ k : Fin (H.eventCount + 1),
        (riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.initialMetric k) univ).toReal :=
    fun k => Finset.single_le_sum (f := fun k => (riemannianVolumeMeasure ThreeModel (H.stage k).Carrier
      (H.initialMetric k) univ).toReal) (fun k _ => hnn k) (Finset.mem_univ k)
  have hK : 0 ≤ (H.horizon + c) ^ (3 / 2 : ℝ) / c ^ (3 / 2 : ℝ) := by
    have : 0 ≤ H.horizon := H.horizon_nonneg
    positivity
  have hfin_nn : ∀ {Q : OrientedThreeStage.{u}} (m : Q.Metric),
      0 ≤ (riemannianVolumeMeasure ThreeModel Q.Carrier m univ).toReal := fun _ => ENNReal.toReal_nonneg
  refine Fin.lastCases ?_ ?_ j hj hnext
  · intro hj hnext
    rw [ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt) t]
    have ha := H.time_nonneg (Fin.last H.eventCount)
    have hanti := flowVolume_normalized_antitone_S10 (H.finalSlab hlt).flow (H.finalSlab hlt).equation
      (c := c) (convex_Icc _ _) (by
        change interior (Icc _ _) ⊆ Ioo _ _
        rw [interior_Icc])
      (fun s hs => by have := hs.1; linarith)
      (fun s hs x => by rw [solution_scalar_eq_S10]; exact hRfin s hs x)
    have h := flowVolume_le_of_anti_S10 (H.finalSlab hlt).flow hc ha hj hth hanti
      (show H.time (Fin.last H.eventCount) ∈ Icc _ _ from ⟨le_rfl, hlt.le⟩)
      (show t ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from ⟨hj, hth⟩)
    have hi := H.final_initial hlt
    change (riemannianVolumeMeasure ThreeModel _ ((H.finalSlab hlt).flow.base.metric t) univ).toReal ≤ _ at h
    change _ ≤ (riemannianVolumeMeasure ThreeModel _ ((H.finalSlab hlt).flow.base.metric (H.time (Fin.last H.eventCount))) univ).toReal * _ at h
    rw [hi] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hsum _) hK)
  · intro i hj hnext
    have hti := hnext i rfl
    rw [stageMetric_castSucc_S10]
    have ha := H.time_nonneg i.castSucc
    have hanti := flowVolume_normalized_antitone_S10 (H.event i).incoming.flow (H.event i).incoming.equation
      (c := c) (convex_Ico _ _) (by
        change interior (Ico _ _) ⊆ Ioo _ _
        rw [interior_Ico])
      (fun s hs => by have := hs.1; linarith)
      (fun s hs x => by rw [solution_scalar_eq_S10]; exact hRev i s hs x)
    have h := flowVolume_le_of_anti_S10 (H.event i).incoming.flow hc ha hj hth hanti
      (show H.time i.castSucc ∈ Ico _ _ from ⟨le_rfl, (H.event i).incoming.lt⟩)
      (show t ∈ Ico (H.time i.castSucc) (H.time i.succ) from ⟨hj, hti⟩)
    have hi := H.event_initial i
    change (riemannianVolumeMeasure ThreeModel _ ((H.event i).incoming.flow.base.metric t) univ).toReal ≤ _ at h
    change _ ≤ (riemannianVolumeMeasure ThreeModel _ ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) univ).toReal * _ at h
    rw [hi] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hsum _) hK)

end GC.LongTime.Ch12
