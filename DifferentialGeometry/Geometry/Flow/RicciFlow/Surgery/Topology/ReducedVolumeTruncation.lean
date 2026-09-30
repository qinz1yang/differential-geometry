import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionExistenceReduction

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

variable (H : ObservedHistory.{u})

theorem stageMetric_scalar_ge_of_stageInitial {c : ℝ} (hc : 0 < c)
    (hstage : ∀ (i : Fin (H.eventCount + 1)) (y : (H.stage i).Carrier),
      -3 / (2 * (H.time i + c)) ≤ metricScalarAt (H.initialMetric i) y)
    (j : Fin (H.eventCount + 1)) {t : ℝ} (ht : t ∈ H.stageDomain j)
    (x : (H.stage j).Carrier) :
    -(3 / (2 * c)) ≤ metricScalarAt (H.stageMetric j t) x := by
  have ht0 : 0 ≤ t := (H.time_nonneg j).trans (H.time_le_of_mem_stageDomain ht)
  have hbar : -3 / (2 * (t + c)) ≤ metricScalarAt (H.stageMetric j t) x := by
    cases j using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last] at ht
      by_cases hfin : H.time (Fin.last H.eventCount) < H.horizon
      · have hmetric : H.stageMetric (Fin.last H.eventCount) t =
            (H.finalSlab hfin).flow.base.metric t := by
          simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfin]
        rw [hmetric]
        exact closedSlab_scalarLowerBarrier_le hfin (H.time_nonneg _) hc (H.finalSlab hfin)
          (fun z => by rw [H.final_initial hfin]; exact hstage _ z) ht x
      · have ht' : t = H.time (Fin.last H.eventCount) :=
          le_antisymm (ht.2.trans (le_of_not_gt hfin)) ht.1
        have hmetric : H.stageMetric (Fin.last H.eventCount) t =
            H.initialMetric (Fin.last H.eventCount) := by
          simp only [stageMetric, Fin.lastCases_last, dite_eq_right hfin]
        rw [hmetric, ht']
        exact hstage _ x
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc] at ht
      have hmetric : H.stageMetric i.castSucc t = (H.event i).incoming.flow.base.metric t := by
        simp only [stageMetric, Fin.lastCases_castSucc]
      rw [hmetric]
      exact incomingSlab_scalarLowerBarrier_le (H.time_nonneg _) hc (H.event i).incoming
        (fun z => by rw [H.event_initial i]; exact hstage _ z) ht x
  have hd : 3 / (2 * (t + c)) ≤ 3 / (2 * c) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hneg : -(3 / (2 * c)) ≤ -3 / (2 * (t + c)) := by
    rw [neg_div]
    exact neg_le_neg hd
  exact hneg.trans hbar

theorem exists_stageMetric_scalar_lower_bound {parameters : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters) :
    ∃ b : ℝ, 0 < b ∧ ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.stageMetric j t) x := by
  obtain ⟨c, hc, h0⟩ : ∃ c : ℝ, 0 < c ∧ ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) y := by
    by_cases hne : Nonempty (H.stage 0).Carrier
    · obtain ⟨c, hc, hbar⟩ := exists_initialScalarBarrier_of_compact (H.initialMetric 0)
      exact ⟨c, hc, fun y => by rw [H.time_zero, zero_add]; exact hbar y⟩
    · exact ⟨1, one_pos, fun y => (hne ⟨y⟩).elim⟩
  exact ⟨3 / (2 * c), by positivity, fun j t ht x => H.stageMetric_scalar_ge_of_stageInitial hc
    (stageInitial_scalarLowerBound_of_history cutoff hc h0) j ht x⟩

variable {H}

theorem regularizedStage_scalar_ge_of_stageMetric_scalar_ge {b B : ℝ}
    (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.stageMetric j t) x)
    (hB : b ≤ B) (first last : Fin (H.eventCount + 1)) (T u v : ℝ) :
    ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x :=
  fun j _ ht x => (neg_le_neg hB).trans
    (hfloor j.val _ (H.mapsTo_regularizedStage_Ioo T u v j.val ht) x)

variable {b : ℝ}
  (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.stageDomain j,
    ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.stageMetric j t) x)
include hfloor

theorem regularizedCost_eq_of_scalar_lower_bound_le (first last : Fin (H.eventCount + 1))
    (hle : first ≤ last) (T : ℝ) {B C : ℝ} (hB : b ≤ B) (hC : b ≤ C) (u v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedCost first last hle T B u v p q = H.regularizedCost first last hle T C u v p q :=
  H.regularizedCost_congr_scalar_lower_bound first last hle T B C u v
    (regularizedStage_scalar_ge_of_stageMetric_scalar_ge hfloor hB first last T u v)
    (regularizedStage_scalar_ge_of_stageMetric_scalar_ge hfloor hC first last T u v) p q

theorem regularizedDensity_eq_of_scalar_lower_bound_le (first last : Fin (H.eventCount + 1))
    (hle : first ≤ last) (T : ℝ) {B C : ℝ} (hB : b ≤ B) (hC : b ≤ C) (v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedDensity first last hle T B v p q =
      H.regularizedDensity first last hle T C v p q := by
  unfold regularizedDensity
  rw [H.regularizedActionValues_congr_scalar_lower_bound first last hle T B C 0 v
    (regularizedStage_scalar_ge_of_stageMetric_scalar_ge hfloor hB first last T 0 v)
    (regularizedStage_scalar_ge_of_stageMetric_scalar_ge hfloor hC first last T 0 v) p q]

theorem regularMinimizerEndpoints_eq_of_scalar_lower_bound_le
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T : ℝ) {B C : ℝ}
    (hB : b ≤ B) (hC : b ≤ C) (v : ℝ) (p : (H.stage last).Carrier) :
    H.regularMinimizerEndpoints first last hle T B v p =
      H.regularMinimizerEndpoints first last hle T C v p := by
  have hscalar {D : ℝ} (hD : b ≤ D)
      (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) (j) :
      ∀ᵐ t ∂volume.restrict
        (Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)),
        -D ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact regularizedStage_scalar_ge_of_stageMetric_scalar_ge hfloor hD first last T 0 v j t ht _
  have hcost := H.regularizedCost_eq_of_scalar_lower_bound_le hfloor first last hle T hB hC 0 v p
  ext q
  constructor
  · rintro ⟨α, hα, hp, hq, hcross, hact⟩
    refine ⟨α, hα, hp, hq, hcross, ?_⟩
    rw [← H.regularizedExtendedAction_congr_scalar_lower_bound first last T B C 0 v α hα
      (hscalar hB α) (hscalar hC α), hact, hcost]
  · rintro ⟨α, hα, hp, hq, hcross, hact⟩
    refine ⟨α, hα, hp, hq, hcross, ?_⟩
    rw [H.regularizedExtendedAction_congr_scalar_lower_bound first last T B C 0 v α hα
      (hscalar hB α) (hscalar hC α), hact, hcost]

omit hfloor in
theorem regularizedDensity_le_exp (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v : ℝ} (hv : 0 < v) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedDensity first last hle T B v p q ≤
      ENNReal.ofReal (Real.exp (B * v ^ 2 / 3 - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  have hlow := WithTop.coe_le_coe.mp (H.regularizedActionValues_ge first last hle T B 0 v p q hA)
  simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), sub_zero] at hlow
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hdiv : -A / (2 * v) ≤ B * v ^ 2 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * v)).mpr
    nlinarith
  linarith

omit hfloor in
theorem regularizedDensity_eq_zero_of_regularizedCost_eq_top
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hcost : H.regularizedCost first last hle T B 0 v p q = ⊤) :
    H.regularizedDensity first last hle T B v p q = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  exact absurd ((H.regularizedCost_eq_top_iff first last hle T B 0 v p q).mp hcost _ hA)
    WithTop.coe_ne_top

omit hfloor in
theorem regularizedDensity_eq_exp_of_regularizedCost_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B : ℝ) {v A : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hcost : H.regularizedCost first last hle T B 0 v p q = (A : WithTop ℝ)) :
    H.regularizedDensity first last hle T B v p q =
      ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  set R : Set ℝ := {a | (a : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B 0 v p q}
  have hRne : R.Nonempty := by
    by_contra hn
    have htop : H.regularizedCost first last hle T B 0 v p q = ⊤ := by
      refine (H.regularizedCost_eq_top_iff first last hle T B 0 v p q).mpr fun a ha => ?_
      by_contra hne
      obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
      exact hn ⟨r, ha⟩
    exact WithTop.coe_ne_top (hcost.symm.trans htop)
  have hRbdd : BddBelow R := ⟨-(2 * B / 3) * (v ^ 3 - 0 ^ 3), fun a ha =>
    WithTop.coe_le_coe.mp (H.regularizedActionValues_ge first last hle T B 0 v p q ha)⟩
  have hcostR :
      H.regularizedCost first last hle T B 0 v p q = ((sInf R : ℝ) : WithTop ℝ) := by
    apply le_antisymm
    · rw [WithTop.coe_sInf' hRne hRbdd]
      apply le_csInf (hRne.image _)
      rintro _ ⟨a, ha, rfl⟩
      exact H.regularizedCost_le_of_competitor first last hle T B 0 v p q ha
    · obtain ⟨a₀, ha₀⟩ := hRne
      unfold regularizedCost
      refine le_csInf ⟨_, ha₀⟩ fun a ha => ?_
      by_cases htop : a = ⊤
      · rw [htop]
        exact le_top
      · obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.mp htop
        exact WithTop.coe_le_coe.mpr (csInf_le hRbdd ha)
  have hA : sInf R = A := WithTop.coe_injective (hcostR.symm.trans hcost)
  let f : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp (-a / (2 * v) -
    (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hf : Continuous f := ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (((continuous_id.neg.div_const _).sub continuous_const).sub continuous_const))
  have hanti : Antitone f := by
    intro a c hac
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right (neg_le_neg hac) (by positivity : 0 ≤ 2 * v)
    linarith
  have heq := hanti.map_csInf_of_continuousAt hf.continuousAt hRne hRbdd
  rw [← hA]
  have h2 := heq.symm
  rw [sSup_image] at h2
  exact h2

omit hfloor in
theorem measurable_regularizedDensity_of_isClosed_regularizedCost_le
    [∀ j : Fin (H.eventCount + 1), MeasurableSpace (H.stage j).Carrier]
    [∀ j : Fin (H.eventCount + 1), BorelSpace (H.stage j).Carrier]
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B : ℝ) {v : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier)
    (hclosed : ∀ c : ℝ,
      IsClosed {q | H.regularizedCost first last hle T B 0 v p q ≤ (c : WithTop ℝ)}) :
    Measurable (H.regularizedDensity first last hle T B v p) := by
  classical
  set cost : (H.stage first).Carrier → WithTop ℝ :=
    fun q => H.regularizedCost first last hle T B 0 v p q with hcost_def
  have htop : MeasurableSet {q | cost q = ⊤} := by
    have hset : {q | cost q = ⊤} = ⋂ n : ℕ, {q | cost q ≤ ((n : ℝ) : WithTop ℝ)}ᶜ := by
      ext q
      simp only [mem_iInter, mem_compl_iff]
      refine ⟨fun h n hn => ?_, fun h => ?_⟩
      · have h' : cost q = ⊤ := h
        have hn' : cost q ≤ ((n : ℝ) : WithTop ℝ) := hn
        rw [h'] at hn'
        exact WithTop.coe_ne_top (top_le_iff.mp hn')
      · by_contra hne
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
        obtain ⟨n, hn⟩ := exists_nat_ge r
        exact h n (show cost q ≤ _ by rw [← hr]; exact WithTop.coe_le_coe.mpr hn)
    rw [hset]
    exact MeasurableSet.iInter fun n => (hclosed n).measurableSet.compl
  have hreal : Measurable fun q => WithTop.untopD 0 (cost q) := by
    apply measurable_of_Iic
    intro c
    have hset : (fun q => WithTop.untopD 0 (cost q)) ⁻¹' Iic c =
        {q | cost q ≤ (c : WithTop ℝ)} ∪ ({q | cost q = ⊤} ∩ {_q | 0 ≤ c}) := by
      ext q
      change WithTop.untopD 0 (cost q) ≤ c ↔ cost q ≤ (c : WithTop ℝ) ∨ (cost q = ⊤ ∧ 0 ≤ c)
      by_cases h : cost q = ⊤
      · simp [h]
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
        rw [← hr]
        simp
    rw [hset]
    exact (hclosed c).measurableSet.union (htop.inter (MeasurableSet.const _))
  have hform : H.regularizedDensity first last hle T B v p = fun q =>
      if cost q = ⊤ then 0 else
        ENNReal.ofReal (Real.exp (-WithTop.untopD 0 (cost q) / (2 * v) -
          (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
    funext q
    by_cases h : cost q = ⊤
    · rw [ite_eq_left h]
      exact H.regularizedDensity_eq_zero_of_regularizedCost_eq_top first last hle T B v p q h
    · rw [ite_eq_right h]
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
      rw [← hr, WithTop.untopD_coe]
      exact H.regularizedDensity_eq_exp_of_regularizedCost_eq first last hle T B hv p q
        hr.symm
  rw [hform]
  exact Measurable.ite htop measurable_const (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (((hreal.neg.div_const _).sub_const _).sub_const _)))

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u})

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

theorem exists_stageMetric_scalar_lower_bound_of_inCutoffClass {g₀ : P₀.Metric} {B : ℝ}
    {p₀ : CutoffParameters} {δbound ρbound : ℝ} (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound) :
    ∃ b : ℝ, 0 < b ∧ ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.toHistory.stageDomain j,
      ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.toHistory.stageMetric j t) x := by
  obtain ⟨_, -, -, -, -, -, records, -⟩ := hH.2.2.2.1
  exact H.toHistory.exists_stageMetric_scalar_lower_bound records

variable {H} {b : ℝ}
  (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ t ∈ H.toHistory.stageDomain j,
    ∀ x : (H.stage j).Carrier, -b ≤ metricScalarAt (H.toHistory.stageMetric j t) x)
include hfloor

theorem reducedVolume_eq_of_scalar_lower_bound_le (k : Fin (H.eventCount + 1))
    (p : (H.stage k).Carrier) (T v : ℝ) {B₀ : ℝ} (hB₀ : b ≤ B₀)
    (hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k) :
    H.reducedVolume k p T v =
      ∫⁻ q in H.toHistory.regularMinimizerEndpoints _ k hle T B₀ v p,
        H.toHistory.regularizedDensity _ k hle T B₀ v p q
        ∂riemannianVolumeMeasure ThreeModel
          (H.stage (H.toHistory.activeStage
            (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
          (H.toHistory.stageMetric _ (T - v ^ 2)) := by
  simp only [reducedVolume, dite_eq_left hle]
  refine (Filter.limsup_congr (Filter.eventually_atTop.2 ⟨B₀, fun B hB => ?_⟩)).trans
    (Filter.limsup_const _)
  rw [ObservedHistory.regularMinimizerEndpoints_eq_of_scalar_lower_bound_le (H := H.toHistory)
    hfloor _ k hle T (hB₀.trans hB) hB₀ v p]
  simp_rw [ObservedHistory.regularizedDensity_eq_of_scalar_lower_bound_le (H := H.toHistory)
    hfloor _ k hle T (hB₀.trans hB) hB₀ v p]

theorem reducedVolume_le_of_scalar_lower_bound (k : Fin (H.eventCount + 1))
    (p : (H.stage k).Carrier) (T : ℝ) {v : ℝ} (hv : 0 < v) :
    H.reducedVolume k p T v ≤
      ENNReal.ofReal (Real.exp (b * v ^ 2 / 3 - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) *
      riemannianVolumeMeasure ThreeModel
        (H.stage (H.toHistory.activeStage
          (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
        (H.toHistory.stageMetric _ (T - v ^ 2)) univ := by
  by_cases hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k
  · rw [H.reducedVolume_eq_of_scalar_lower_bound_le hfloor k p T v le_rfl hle]
    refine (lintegral_mono fun q =>
      H.toHistory.regularizedDensity_le_exp _ k hle T b hv p q).trans ?_
    rw [setLIntegral_const]
    exact mul_le_mul' le_rfl (measure_mono (subset_univ _))
  · simp only [reducedVolume, dite_eq_right hle]
    exact bot_le

theorem reducedVolume_lt_top_of_scalar_lower_bound (k : Fin (H.eventCount + 1))
    (p : (H.stage k).Carrier) (T : ℝ) {v : ℝ} (hv : 0 < v) : H.reducedVolume k p T v < ⊤ := by
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel)
    (H.toHistory.stageMetric
      (H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2))) (T - v ^ 2))
  exact (H.reducedVolume_le_of_scalar_lower_bound hfloor k p T hv).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))

omit hfloor in
theorem exists_reducedVolume_eq_lintegral_of_inCutoffClass {g₀ : P₀.Metric} {B : ℝ}
    {p₀ : CutoffParameters} {δbound ρbound : ℝ} (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound) :
    ∃ B₀ : ℝ, ∀ (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) (T v : ℝ)
      (hle : H.toHistory.activeStage (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)) ≤ k),
      H.reducedVolume k p T v =
        ∫⁻ q in H.toHistory.regularMinimizerEndpoints _ k hle T B₀ v p,
          H.toHistory.regularizedDensity _ k hle T B₀ v p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.toHistory.activeStage
              (projIcc 0 H.horizon H.horizon_nonneg (T - v ^ 2)))).Carrier
            (H.toHistory.stageMetric _ (T - v ^ 2)) := by
  obtain ⟨b, -, hfloor⟩ := H.exists_stageMetric_scalar_lower_bound_of_inCutoffClass (P₀ := P₀) hH
  exact ⟨b, fun k p T v hle => reducedVolume_eq_of_scalar_lower_bound_le hfloor k p T v le_rfl hle⟩

omit hfloor in
theorem reducedVolume_lt_top_of_inCutoffClass {g₀ : P₀.Metric} {B : ℝ}
    {p₀ : CutoffParameters} {δbound ρbound : ℝ} (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
    (k : Fin (H.eventCount + 1)) (p : (H.stage k).Carrier) (T : ℝ) {v : ℝ} (hv : 0 < v) :
    H.reducedVolume k p T v < ⊤ := by
  obtain ⟨b, -, hfloor⟩ := H.exists_stageMetric_scalar_lower_bound_of_inCutoffClass (P₀ := P₀) hH
  exact reducedVolume_lt_top_of_scalar_lower_bound hfloor k p T hv

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
