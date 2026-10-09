import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedEndExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

variable (H : RetainedCoreHistory.{u})

theorem mem_Icc_zero_horizon_of_mem_stageDomain {k : Fin (H.eventCount + 1)} {T : ℝ}
    (hT : T ∈ H.toHistory.stageDomain k) : T ∈ Icc 0 H.horizon :=
  ⟨(H.toHistory.time_nonneg k).trans (H.toHistory.time_le_of_mem_stageDomain hT),
    (H.toHistory.le_stageEndTime_of_mem_stageDomain hT).trans
      (H.toHistory.stageEndTime_le_horizon k)⟩

theorem stageDomain_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (k : Fin (H.eventCount + 1)) :
    H.toHistory.stageDomain k ⊆ (H.extendHorizon T' hT' G hG).toHistory.stageDomain k := by
  intro τ hτ
  cases k using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hτ
    unfold ObservedHistory.stageDomain
    erw [Fin.lastCases_last]
    exact ⟨hτ.1, hτ.2.trans hT'⟩
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hτ
    unfold ObservedHistory.stageDomain
    erw [Fin.lastCases_castSucc]
    exact hτ

theorem stageEndTime_extendHorizon_last {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T' hT' G hG).toHistory.stageEndTime (Fin.last H.eventCount) = T' := by
  unfold ObservedHistory.stageEndTime
  erw [Fin.lastCases_last]
  rfl

theorem stageEndTime_extendHorizon_castSucc {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin H.eventCount) :
    (H.extendHorizon T' hT' G hG).toHistory.stageEndTime i.castSucc =
      H.toHistory.stageEndTime i.castSucc := by
  unfold ObservedHistory.stageEndTime
  erw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
  rfl

theorem activeStage_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (s : Icc (0 : ℝ) T') (t : Icc (0 : ℝ) H.horizon)
    (hst : (s : ℝ) = t) :
    (H.extendHorizon T' hT' G hG).toHistory.activeStage s = H.toHistory.activeStage t := by
  have hs : s = ⟨t.1, t.2.1, t.2.2.trans hT'⟩ := Subtype.ext hst
  subst hs
  rfl

theorem stageMetric_extendHorizon_last_of_mem_Icc {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {τ : ℝ}
    (hτ : τ ∈ Icc (H.time (Fin.last H.eventCount)) T') :
    (H.extendHorizon T' hT' G hG).toHistory.stageMetric (Fin.last H.eventCount) τ =
      G.flow.base.metric τ := by
  unfold ObservedHistory.stageMetric
  erw [Fin.lastCases_last]
  split_ifs with hlt
  · rfl
  · have he : τ = H.time (Fin.last H.eventCount) :=
      le_antisymm (hτ.2.trans (not_lt.mp hlt)) hτ.1
    subst he
    exact hG.symm

theorem stageMetric_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (j : Fin (H.eventCount + 1)) {τ : ℝ} (hτ : τ ∈ H.toHistory.stageDomain j) :
    (H.extendHorizon T' hT' G hG).toHistory.stageMetric j τ = H.toHistory.stageMetric j τ := by
  cases j using Fin.lastCases with
  | last =>
    rw [← hagree τ hτ]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hτ
    exact H.stageMetric_extendHorizon_last_of_mem_Icc hT' G hG ⟨hτ.1, hτ.2.trans hT'⟩
  | cast i =>
    unfold ObservedHistory.stageMetric
    erw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    rfl

theorem lt_stageEndTime_extendHorizon {T' : ℝ} (hT' : H.horizon < T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (t : Icc (0 : ℝ) H.horizon) :
    (t : ℝ) < (H.extendHorizon T' hT'.le G hG).toHistory.stageEndTime
      (H.toHistory.activeStage t) := by
  have hmem := H.toHistory.activeStage_mem t
  generalize H.toHistory.activeStage t = k at hmem ⊢
  cases k using Fin.lastCases with
  | last =>
    rw [H.stageEndTime_extendHorizon_last hT'.le G hG]
    exact t.2.2.trans_lt hT'
  | cast i =>
    rw [H.stageEndTime_extendHorizon_castSucc hT'.le G hG, H.toHistory.stageEndTime_castSucc]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
    exact hmem.2

theorem mem_Ico_extendHorizon_of_mem_stageDomain {T' : ℝ} (hT' : H.horizon < T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {k : Fin (H.eventCount + 1)} {T : ℝ}
    (hT : T ∈ H.toHistory.stageDomain k) :
    T ∈ Ico ((H.extendHorizon T' hT'.le G hG).toHistory.time k)
      ((H.extendHorizon T' hT'.le G hG).toHistory.stageEndTime k) := by
  cases k using Fin.lastCases with
  | last =>
    rw [H.stageEndTime_extendHorizon_last hT'.le G hG]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hT
    exact ⟨hT.1, hT.2.trans_lt hT'⟩
  | cast i =>
    rw [H.stageEndTime_extendHorizon_castSucc hT'.le G hG, H.toHistory.stageEndTime_castSucc]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hT
    exact hT

theorem exists_extendHorizon_gt :
    ∃ (T' : ℝ) (_ : H.horizon < T')
      (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
      (_ : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
      ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
        G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ := by
  by_cases hlt : H.time (Fin.last H.eventCount) < H.horizon
  · let S := H.finalSlab hlt
    obtain ⟨d, hbd, S', hS', heq, hjoint⟩ :=
      exists_isSolutionOn_extension_past_right_endpoint S.lt S.flow S.equation
        S.smoothUpTo.jointContMDiffOn
    obtain ⟨T', h1, h2⟩ := exists_between hbd
    have ha : H.time (Fin.last H.eventCount) < T' := hlt.trans h1
    let G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T' :=
      ⟨ha, S'.timeRestrict (Geometry.Curvature.RealTimeInterval.closed _ T' ha.le),
        isSolutionOn_timeRestrict hS' (fun _ ht => ⟨ht.1, ht.2.trans h2.le⟩)
          (fun _ ht => ⟨ht.1, ht.2.trans h2⟩),
        OrientedThreeStage.MetricSmoothUpTo.of_contMDiffOn_Ico _ S'.base.metric ha h2
          (hjoint.mono (prod_mono Ico_subset_Icc_self subset_rfl))⟩
    have hmet : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
        H.toHistory.stageMetric (Fin.last H.eventCount) τ = S.flow.base.metric τ := by
      intro τ _
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hlt]
      rfl
    refine ⟨T', h1, G, ?_, ?_⟩
    · change S'.base.metric _ = _
      rw [heq _ hlt.le]
      exact H.final_initial hlt
    · intro τ hτ
      change S'.base.metric τ = _
      rw [hmet τ hτ]
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hτ
      exact heq τ hτ.2
  · have hend : H.time (Fin.last H.eventCount) = H.horizon :=
      le_antisymm H.time_le_horizon (not_lt.mp hlt)
    obtain ⟨T', hT', G, hG⟩ :=
      exists_closedSlab_of_metric _ (H.initialMetric (Fin.last H.eventCount))
        (H.time (Fin.last H.eventCount))
    refine ⟨T', hend ▸ hT', G, hG, fun τ hτ => ?_⟩
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hτ
    have he : τ = H.time (Fin.last H.eventCount) := le_antisymm (hτ.2.trans hend.ge) hτ.1
    subst he
    rw [hG]
    simp only [ObservedHistory.stageMetric, Fin.lastCases_last]
    rw [dite_eq_right hlt]

section ReducedVolume

variable {T' : ℝ} (hT' : H.horizon ≤ T')
  (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
  (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount))

theorem regularizedStageStart_extendHorizon {T : ℝ} (hT : T ≤ H.horizon) (u : ℝ)
    (j : Fin (H.eventCount + 1)) :
    (H.extendHorizon T' hT' G hG).toHistory.regularizedStageStart T u j =
      H.toHistory.regularizedStageStart T u j := by
  have hu : T - u ^ 2 ≤ T := sub_le_self _ (sq_nonneg u)
  cases j using Fin.lastCases with
  | last =>
    unfold ObservedHistory.regularizedStageStart
    rw [H.stageEndTime_extendHorizon_last hT' G hG, H.toHistory.stageEndTime_last,
      min_eq_left (hu.trans (hT.trans hT')), min_eq_left (hu.trans hT)]
  | cast i =>
    unfold ObservedHistory.regularizedStageStart
    rw [H.stageEndTime_extendHorizon_castSucc hT' G hG]

theorem stageRegularizedExtendedAction_extendHorizon
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    {T : ℝ} (hT : T ≤ H.horizon) (B u v : ℝ) (j : Fin (H.eventCount + 1))
    (α : ℝ → (H.stage j).Carrier) :
    (H.extendHorizon T' hT' G hG).toHistory.stageRegularizedExtendedAction j T B α
        ((H.extendHorizon T' hT' G hG).toHistory.regularizedStageStart T u j)
        ((H.extendHorizon T' hT' G hG).toHistory.regularizedStageEnd T v j) =
      H.toHistory.stageRegularizedExtendedAction j T B α
        (H.toHistory.regularizedStageStart T u j) (H.toHistory.regularizedStageEnd T v j) := by
  rw [H.regularizedStageStart_extendHorizon hT' G hG hT]
  unfold ObservedHistory.stageRegularizedExtendedAction
  apply DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  unfold ObservedHistory.stageRegularizedLagrangian
  rw [H.stageMetric_extendHorizon hT' G hG hagree j
    (H.toHistory.mapsTo_regularizedStage_Ioo T u v j ht)]
  rfl

theorem regularizedExtendedAction_extendHorizon
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (first last : Fin (H.eventCount + 1)) {T : ℝ} (hT : T ≤ H.horizon) (B u v : ℝ)
    (α : (j : H.toHistory.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    (H.extendHorizon T' hT' G hG).toHistory.regularizedExtendedAction first last T B u v α =
      H.toHistory.regularizedExtendedAction first last T B u v α :=
  Finset.sum_congr rfl fun j _ =>
    H.stageRegularizedExtendedAction_extendHorizon hT' G hG hagree hT B u v j.val (α j)

theorem regularizedActionValues_extendHorizon
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T : ℝ} (hT : T ≤ H.horizon)
    (B u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon T' hT' G hG).toHistory.regularizedActionValues first last hle T B u v p q =
      H.toHistory.regularizedActionValues first last hle T B u v p q := by
  have hu : T - u ^ 2 ≤ T := sub_le_self _ (sq_nonneg u)
  have hv : T - v ^ 2 ≤ T := sub_le_self _ (sq_nonneg v)
  have hupper : T - u ^ 2 ∈ Icc ((H.extendHorizon T' hT' G hG).toHistory.time last)
      ((H.extendHorizon T' hT' G hG).toHistory.stageEndTime last) ↔
      T - u ^ 2 ∈ Icc (H.toHistory.time last) (H.toHistory.stageEndTime last) := by
    cases last using Fin.lastCases with
    | last =>
      rw [H.stageEndTime_extendHorizon_last hT' G hG, H.toHistory.stageEndTime_last]
      exact ⟨fun h => ⟨h.1, hu.trans hT⟩, fun h => ⟨h.1, hu.trans (hT.trans hT')⟩⟩
    | cast i =>
      rw [H.stageEndTime_extendHorizon_castSucc hT' G hG]
      rfl
  have hlower : T - v ^ 2 ∈ (H.extendHorizon T' hT' G hG).toHistory.stageDomain first ↔
      T - v ^ 2 ∈ H.toHistory.stageDomain first := by
    refine ⟨fun h => ?_, fun h => H.stageDomain_extendHorizon hT' G hG first h⟩
    cases first using Fin.lastCases with
    | last =>
      unfold ObservedHistory.stageDomain at h
      erw [Fin.lastCases_last] at h
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc]
      exact ⟨h.1, hv.trans hT⟩
    | cast i =>
      unfold ObservedHistory.stageDomain at h
      erw [Fin.lastCases_castSucc] at h
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
      exact h
  ext A
  constructor
  · rintro ⟨h1, h2, h3, h4, α, hα, hp, hq, hcross, hA⟩
    refine ⟨h1, h2, hupper.mp h3, hlower.mp h4, α, fun j => ?_, hp, hq, hcross, ?_⟩
    · exact H.regularizedStageStart_extendHorizon hT' G hG hT u j.val ▸ hα j
    · exact (H.regularizedExtendedAction_extendHorizon hT' G hG hagree first last hT B u v
        α).symm.trans hA
  · rintro ⟨h1, h2, h3, h4, α, hα, hp, hq, hcross, hA⟩
    refine ⟨h1, h2, hupper.mpr h3, hlower.mpr h4, α, fun j => ?_, hp, hq, hcross, ?_⟩
    · exact (H.regularizedStageStart_extendHorizon hT' G hG hT u j.val).symm ▸ hα j
    · exact (H.regularizedExtendedAction_extendHorizon hT' G hG hagree first last hT B u v
        α).trans hA

theorem regularizedCost_extendHorizon
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T : ℝ} (hT : T ≤ H.horizon)
    (B u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon T' hT' G hG).toHistory.regularizedCost first last hle T B u v p q =
      H.toHistory.regularizedCost first last hle T B u v p q := by
  unfold ObservedHistory.regularizedCost
  rw [H.regularizedActionValues_extendHorizon hT' G hG hagree first last hle hT]

theorem regularizedDensity_extendHorizon
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T : ℝ} (hT : T ≤ H.horizon)
    (B v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon T' hT' G hG).toHistory.regularizedDensity first last hle T B v p q =
      H.toHistory.regularizedDensity first last hle T B v p q := by
  unfold ObservedHistory.regularizedDensity
  rw [H.regularizedActionValues_extendHorizon hT' G hG hagree first last hle hT]

theorem regularMinimizerEndpoints_extendHorizon
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T : ℝ} (hT : T ≤ H.horizon)
    (B v : ℝ) (p : (H.stage last).Carrier) :
    (H.extendHorizon T' hT' G hG).toHistory.regularMinimizerEndpoints first last hle T B v p =
      H.toHistory.regularMinimizerEndpoints first last hle T B v p := by
  ext q
  constructor
  · rintro ⟨α, hα, hp, hq, hcross, hA⟩
    refine ⟨α, fun j => ?_, hp, hq, hcross, ?_⟩
    · exact H.regularizedStageStart_extendHorizon hT' G hG hT 0 j.val ▸ hα j
    · exact (H.regularizedExtendedAction_extendHorizon hT' G hG hagree first last hT B 0 v
        α).symm.trans (hA.trans
          (H.regularizedCost_extendHorizon hT' G hG hagree first last hle hT B 0 v p q))
  · rintro ⟨α, hα, hp, hq, hcross, hA⟩
    refine ⟨α, fun j => ?_, hp, hq, hcross, ?_⟩
    · exact (H.regularizedStageStart_extendHorizon hT' G hG hT 0 j.val).symm ▸ hα j
    · exact (H.regularizedExtendedAction_extendHorizon hT' G hG hagree first last hT B 0 v
        α).trans (hA.trans
          (H.regularizedCost_extendHorizon hT' G hG hagree first last hle hT B 0 v p q).symm)

private theorem regularizedDensity_eq_zero_of_not_mem_stageDomain
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T v : ℝ}
    (hdom : T - v ^ 2 ∉ H.toHistory.stageDomain first) (B : ℝ) (p : (H.stage last).Carrier)
    (q : (H.stage first).Carrier) :
    H.toHistory.regularizedDensity first last hle T B v p q = 0 :=
  nonpos_iff_eq_zero.mp (iSup₂_le fun _ hA => absurd hA.2.2.2.1 hdom)

end ReducedVolume

private theorem reducedVolume_eq_limsup (K : RetainedCoreHistory.{u})
    (k : Fin (K.eventCount + 1)) (p : (K.stage k).Carrier) (T v : ℝ)
    (first : Fin (K.eventCount + 1))
    (hfirst : K.toHistory.activeStage (projIcc 0 K.horizon K.horizon_nonneg (T - v ^ 2)) = first)
    (hle : first ≤ k) :
    K.reducedVolume k p T v =
      Filter.limsup (fun B : ℝ =>
        ∫⁻ q in K.toHistory.regularMinimizerEndpoints first k hle T B v p,
          K.toHistory.regularizedDensity first k hle T B v p q
          ∂Integral.Measure.riemannianVolumeMeasure ThreeModel (K.stage first).Carrier
            (K.toHistory.stageMetric first (T - v ^ 2))) Filter.atTop := by
  subst hfirst
  exact dite_eq_left hle

private theorem reducedVolume_eq_zero (K : RetainedCoreHistory.{u})
    (k : Fin (K.eventCount + 1)) (p : (K.stage k).Carrier) (T v : ℝ)
    (first : Fin (K.eventCount + 1))
    (hfirst : K.toHistory.activeStage (projIcc 0 K.horizon K.horizon_nonneg (T - v ^ 2)) = first)
    (hle : ¬ first ≤ k) : K.reducedVolume k p T v = 0 := by
  subst hfirst
  exact dite_eq_right hle

theorem reducedVolume_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) {T v : ℝ} (hT : T ≤ H.horizon) :
    (H.extendHorizon T' hT' G hG).reducedVolume k p T v = H.reducedVolume k p T v := by
  have hlow : T - v ^ 2 ≤ H.horizon := (sub_le_self _ (sq_nonneg v)).trans hT
  set first := H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))
  have hfirst : (H.extendHorizon T' hT' G hG).toHistory.activeStage
      (projIcc 0 (H.extendHorizon T' hT' G hG).horizon
        (H.extendHorizon T' hT' G hG).horizon_nonneg (T - v ^ 2)) = first := by
    apply H.activeStage_extendHorizon hT' G hG
    change max 0 (min T' (T - v ^ 2)) = max 0 (min H.horizon (T - v ^ 2))
    rw [min_eq_right (hlow.trans hT'), min_eq_right hlow]
  by_cases hle : first ≤ k
  · rw [reducedVolume_eq_limsup (H.extendHorizon T' hT' G hG) k p T v first hfirst hle,
      reducedVolume_eq_limsup H k p T v first rfl hle]
    refine congrArg (fun f : ℝ → ENNReal => Filter.limsup f Filter.atTop) (funext fun B => ?_)
    rw [H.regularMinimizerEndpoints_extendHorizon hT' G hG hagree first k hle hT B v p]
    erw [funext (H.regularizedDensity_extendHorizon hT' G hG hagree first k hle hT B v p)]
    by_cases hdom : T - v ^ 2 ∈ H.toHistory.stageDomain first
    · rw [H.stageMetric_extendHorizon hT' G hG hagree first hdom]
      rfl
    · erw [funext (H.regularizedDensity_eq_zero_of_not_mem_stageDomain first k hle hdom B p)]
      exact lintegral_zero.trans lintegral_zero.symm
  · rw [reducedVolume_eq_zero (H.extendHorizon T' hT' G hG) k p T v first hfirst hle,
      reducedVolume_eq_zero H k p T v first rfl hle]

theorem isParabolicallyRmControlledBall_extendHorizon {T' : ℝ} (hT' : H.horizon ≤ T')
    (G : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      G.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ)
    (hball : H.toHistory.isParabolicallyRmControlledBall t p r) :
    (H.extendHorizon T' hT' G hG).toHistory.isParabolicallyRmControlledBall
      ⟨t.1, t.2.1, t.2.2.trans hT'⟩ p r := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := hball
  refine ⟨hr, ⟨a.1, a.2.1, a.2.2.trans hT'⟩, hat, ha, fun x hx => ?_⟩
  have hmt : (H.extendHorizon T' hT' G hG).toHistory.stageMetric
      ((H.extendHorizon T' hT' G hG).toHistory.activeStage ⟨t.1, t.2.1, t.2.2.trans hT'⟩) t =
      H.toHistory.stageMetric (H.toHistory.activeStage t) t :=
    H.stageMetric_extendHorizon hT' G hG hagree _ (H.toHistory.activeStage_mem t)
  rw [hmt] at hx
  obtain ⟨A, hA1, hA2⟩ := htrace x hx
  refine ⟨⟨A.point, A.endpoint_eq, A.crossing⟩, fun s has hst => ?_, hA2⟩
  let s₀ : Icc (0 : ℝ) H.horizon := ⟨s.1, s.2.1, (show (s : ℝ) ≤ t from hst).trans t.2.2⟩
  have hms : (H.extendHorizon T' hT' G hG).toHistory.stageMetric
      ((H.extendHorizon T' hT' G hG).toHistory.activeStage s) s =
      H.toHistory.stageMetric (H.toHistory.activeStage s₀) s₀ :=
    H.stageMetric_extendHorizon hT' G hG hagree _ (H.toHistory.activeStage_mem s₀)
  rw [hms]
  exact hA1 s₀ has hst

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
