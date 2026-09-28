import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedVolumeTruncation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem scalar_ge_of_initial_scalar_ge_on_slab
    {P : OrientedThreeStage.{u}} {D : RealTimeInterval} {a s c : ℝ} (hc : 0 < c)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn (I := ThreeModel) (M := P.Carrier) S)
    (hcarrier : Ico a s ⊆ D.carrier) (hregD : Ioo a s ⊆ D.regular)
    (hinit : ∀ x : P.Carrier, -3 / (2 * c) ≤ metricScalarAt (S.base.metric a) x)
    {t : ℝ} (ht : t ∈ Ico a s) (x : P.Carrier) :
    -3 / (2 * c) ≤ metricScalarAt (S.base.metric t) x := by
  have hb := scalarLowerBarrier_le_on_slab (D := D.timeShift a) (a := 0) (s := s - a) le_rfl hc
    (S.timeShift a) (isSolutionOn_timeShift hS a)
    (fun u hu => hcarrier ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => hregD ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun y => by
      change -3 / (2 * (0 + c)) ≤ metricScalarAt (S.base.metric (0 + a)) y
      rw [zero_add, zero_add]
      exact hinit y)
    (t := t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x
  change -3 / (2 * (t - a + c)) ≤ metricScalarAt (S.base.metric (t - a + a)) x at hb
  rw [sub_add_cancel] at hb
  have hd : 3 / (2 * (t - a + c)) ≤ 3 / (2 * c) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [ht.1])
  rw [neg_div] at hb ⊢
  linarith

theorem scalar_ge_of_initial_scalar_ge_on_closed_slab
    {P : OrientedThreeStage.{u}} {D : RealTimeInterval} {a s c : ℝ} (has : a < s) (hc : 0 < c)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hS : IsSolutionOn (I := ThreeModel) (M := P.Carrier) S)
    (hcarrier : Icc a s ⊆ D.carrier) (hregD : Ioo a s ⊆ D.regular)
    (hinit : ∀ x : P.Carrier, -3 / (2 * c) ≤ metricScalarAt (S.base.metric a) x)
    {t : ℝ} (ht : t ∈ Icc a s) (x : P.Carrier) :
    -3 / (2 * c) ≤ metricScalarAt (S.base.metric t) x := by
  have hIco : ∀ u ∈ Ico a s, -3 / (2 * c) ≤ metricScalarAt (S.base.metric u) x := fun u hu =>
    scalar_ge_of_initial_scalar_ge_on_slab hc S hS (Ico_subset_Icc_self.trans hcarrier) hregD
      hinit hu x
  rcases eq_or_lt_of_le ht.2 with hts | hts
  · have hcont : ContinuousOn (fun u : ℝ => S.scalar u x) (Icc a s) := by
      have h := hS.scalarCont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨hcarrier hu, mem_univ x⟩)
      exact h
    have hclosure : closure (Ioo a s) = Icc a s := closure_Ioo has.ne
    have hmem : s ∈ closure (Ioo a s) := by
      rw [hclosure]
      exact ⟨has.le, le_rfl⟩
    have hs := le_on_closure (f := fun _ : ℝ => -3 / (2 * c)) (g := fun u => S.scalar u x)
      (fun u hu => hIco u ⟨hu.1.le, hu.2⟩)
      (by rw [hclosure]; exact continuousOn_const) (by rw [hclosure]; exact hcont) hmem
    rw [hts]
    exact hs
  · exact hIco t ⟨ht.1, hts⟩

namespace ObservedHistory

variable (H : ObservedHistory.{u})

theorem exists_stageMetric_scalar_ge :
    ∃ b : ℝ, 0 < b ∧ ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.stageMetric j t) x := by
  have hc : ∀ i : Fin (H.eventCount + 1), ∃ c : ℝ, 0 < c ∧
      ∀ y : (H.stage i).Carrier, -3 / (2 * c) ≤ metricScalarAt (H.initialMetric i) y := by
    intro i
    by_cases hne : Nonempty (H.stage i).Carrier
    · exact exists_initialScalarBarrier_of_compact (H.initialMetric i)
    · exact ⟨1, one_pos, fun y => (hne ⟨y⟩).elim⟩
  choose c hcpos hcinit using hc
  have hstage : ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -3 / (2 * c j) ≤ metricScalarAt (H.stageMetric j t) x := by
    intro j t ht x
    cases j using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last] at ht
      by_cases hfin : H.time (Fin.last H.eventCount) < H.horizon
      · have hmetric : H.stageMetric (Fin.last H.eventCount) t =
            (H.finalSlab hfin).flow.base.metric t := by
          simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfin]
        rw [hmetric]
        exact scalar_ge_of_initial_scalar_ge_on_closed_slab hfin (hcpos _)
          (H.finalSlab hfin).flow (H.finalSlab hfin).equation (fun _ hu => hu) (fun _ hu => hu)
          (fun z => by rw [H.final_initial hfin]; exact hcinit _ z) ht x
      · have ht' : t = H.time (Fin.last H.eventCount) :=
          le_antisymm (ht.2.trans (le_of_not_gt hfin)) ht.1
        have hmetric : H.stageMetric (Fin.last H.eventCount) t =
            H.initialMetric (Fin.last H.eventCount) := by
          simp only [stageMetric, Fin.lastCases_last, dite_eq_right hfin]
        rw [hmetric]
        exact hcinit _ x
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc] at ht
      have hmetric : H.stageMetric i.castSucc t = (H.event i).incoming.flow.base.metric t := by
        simp only [stageMetric, Fin.lastCases_castSucc]
      rw [hmetric]
      exact scalar_ge_of_initial_scalar_ge_on_slab (hcpos _) (H.event i).incoming.flow
        (H.event i).incoming.equation (fun _ hu => hu) (fun _ hu => hu)
        (fun z => by rw [H.event_initial i]; exact hcinit _ z) ht x
  have hterm : ∀ i : Fin (H.eventCount + 1), 0 ≤ 3 / (2 * c i) := fun i =>
    (div_pos (by norm_num) (by linarith [hcpos i])).le
  have hsum : 0 ≤ ∑ i, 3 / (2 * c i) := Finset.sum_nonneg fun i _ => hterm i
  refine ⟨1 + ∑ i, 3 / (2 * c i), by linarith, fun j t ht x => ?_⟩
  have hle : 3 / (2 * c j) ≤ 1 + ∑ i, 3 / (2 * c i) := by
    have := Finset.single_le_sum (f := fun i => 3 / (2 * c i)) (fun i _ => hterm i)
      (Finset.mem_univ j)
    linarith
  have h := hstage j t ht x
  rw [neg_div] at h
  linarith

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

theorem exists_stageMetric_scalar_lower_bound :
    ∃ b : ℝ, 0 < b ∧ ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.toHistory.stageDomain j,
      ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.toHistory.stageMetric j t) x :=
  H.toHistory.exists_stageMetric_scalar_ge

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

theorem exists_reducedVolume_eq_lintegral :
    ∃ b : ℝ, ∀ B₀ : ℝ, b ≤ B₀ → ∀ (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) (T v : ℝ)
      (hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k),
      H.reducedVolume k p T v =
        ∫⁻ q in H.toHistory.regularMinimizerEndpoints _ k hle T B₀ v p,
          H.toHistory.regularizedDensity _ k hle T B₀ v p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.toHistory.activeStage
              (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
            (H.toHistory.stageMetric _ (T - v ^ 2)) := by
  obtain ⟨b, -, hfloor⟩ := H.exists_stageMetric_scalar_lower_bound
  exact ⟨b, fun _ hB₀ k p T v hle =>
    reducedVolume_eq_of_scalar_lower_bound_le hfloor k p T v hB₀ hle⟩

theorem reducedVolume_lt_top (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) (T : ℝ)
    {v : ℝ} (hv : 0 < v) : H.reducedVolume k p T v < ⊤ := by
  obtain ⟨b, -, hfloor⟩ := H.exists_stageMetric_scalar_lower_bound
  exact reducedVolume_lt_top_of_scalar_lower_bound hfloor k p T hv

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
