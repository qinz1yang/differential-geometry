import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity
import Mathlib.Topology.Order.Monotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventReducedDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def regularizedC1Density (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) : ℝ≥0∞ :=
  ⨆ A ∈ H.regularizedC1ActionValues first last hle T 0 v p q,
    ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi)))

theorem regularizedC1Density_eq_zero_of_no_competitor
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (h : H.regularizedC1ActionValues first last hle T 0 v p q = ∅) :
    H.regularizedC1Density first last hle T v p q = 0 := by
  simp [regularizedC1Density, h]

theorem le_regularizedC1Density_of_action_le
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T : ℝ) {v L A : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T 0 v p q) (hAL : A ≤ L) :
    ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
        H.regularizedC1Density first last hle T v p q := by
  apply le_trans _ (le_iSup_of_le A (le_iSup_of_le hA le_rfl))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right (neg_le_neg hAL) (by positivity : 0 ≤ 2 * v)
  linarith

theorem regularizedC1Density_eq_of_minimum
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T : ℝ) {v A : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T 0 v p q)
    (hmin : ∀ L ∈ H.regularizedC1ActionValues first last hle T 0 v p q, A ≤ L) :
    H.regularizedC1Density first last hle T v p q =
      ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  apply le_antisymm
  · apply iSup_le
    intro L
    apply iSup_le
    intro hL
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right (neg_le_neg (hmin L hL)) (by positivity : 0 ≤ 2 * v)
    linarith
  · exact H.le_regularizedC1Density_of_action_le first last hle T hv p q hA le_rfl

private local instance (j : Fin (H.eventCount + 1)) :
    MeasurableSpace (H.stage j).Carrier := borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) :
    BorelSpace (H.stage j).Carrier := ⟨rfl⟩

theorem volume_mul_exp_le_lintegral_regularizedC1Density
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T : ℝ) {v L : ℝ} (hv : 0 < v) (p : (H.stage last).Carrier)
    {U : Set (H.stage first).Carrier} (hU : MeasurableSet U)
    (haccess : ∀ q ∈ U,
      ∃ A ∈ H.regularizedC1ActionValues first last hle T 0 v p q, A ≤ L) :
    riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (T - v ^ 2)) U *
      ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
      ∫⁻ q in U, H.regularizedC1Density first last hle T v p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first (T - v ^ 2)) := by
  let μ := riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
    (H.stageMetric first (T - v ^ 2))
  let c := ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
    (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hh : (∫⁻ _q in U, c ∂μ) ≤
      ∫⁻ q in U, H.regularizedC1Density first last hle T v p q ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hU] with q hq
    obtain ⟨A, hA, hAL⟩ := haccess q hq
    exact H.le_regularizedC1Density_of_action_le first last hle T hv p q hA hAL
  simpa only [lintegral_const, Measure.restrict_apply_univ, mul_comm, μ, c] using hh

theorem regularizedC1Density_eq_eventRegularizedC1Density
    (i : Fin H.eventCount) {b : ℝ} (G : (H.stage i.succ).IncomingSlab (H.time i.succ) b)
    {T d v : ℝ} (hd : 0 ≤ d) (hdv : d ≤ v) (hclock : T - d ^ 2 = H.time i.succ)
    (hT : T ∈ H.stageDomain i.succ) (hpast : T - v ^ 2 ∈ H.stageDomain i.castSucc)
    (htimePlus : ∀ t ∈ Icc 0 d,
      T - t ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.succ) b G.lt).carrier)
    (hmetric : ∀ t ∈ Ioo 0 d, H.stageMetric i.succ (T - t ^ 2) = G.flow.base.metric (T - t ^ 2))
    (p : (H.stage i.succ).Carrier) (q : (H.stage i.castSucc).Carrier) :
    H.regularizedC1Density i.castSucc i.succ i.castSucc_le_succ T v p q =
      (H.event i).eventRegularizedC1Density G T d v p q := by
  unfold regularizedC1Density MetricCutCapEvent.eventRegularizedC1Density
  rw [H.regularizedC1ActionValues_eq_eventRegularizedC1ActionValues
    i G hd hdv hclock hT hpast htimePlus hmetric p q]

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_pos_regularizedC1Density_mass_of_survivor_seed
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing
        (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (T : ℝ) {v L : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hcarrier : ∀ t ∈ Icc 0 v, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hseed : lRegularizedAction S T η 0 v < L) :
    ∃ U : Set (H.stage first).Carrier, IsOpen U ∧ f ⟨first, le_rfl, hle⟩ (η v) ∈ U ∧
      U ⊆ range (f ⟨first, le_rfl, hle⟩) ∧
      0 < riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (T - v ^ 2)) U ∧
      riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first (T - v ^ 2)) U *
        ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
          (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
        ∫⁻ q in U, H.regularizedC1Density first last hle T v (f ⟨last, hle, le_rfl⟩ (η 0)) q
          ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
            (H.stageMetric first (T - v ^ 2)) := by
  obtain ⟨V, hV, hηV, α, hα, hstart, hend, _, hact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T hv hcarrier η hη hseed
  have hopen : IsOpen (f ⟨first, le_rfl, hle⟩ '' V) := (hf _).isOpenMap V hV
  refine ⟨f ⟨first, le_rfl, hle⟩ '' V, hopen, ⟨η v, hηV, rfl⟩, image_subset_range _ _, ?_, ?_⟩
  · let _ : (riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (T - v ^ 2))).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure _
    exact hopen.measure_pos _ ⟨_, ⟨η v, hηV, rfl⟩⟩
  · apply H.volume_mul_exp_le_lintegral_regularizedC1Density first last hle T hv
      (f ⟨last, hle, le_rfl⟩ (η 0)) hopen.measurableSet
    rintro y ⟨z, hz, rfl⟩
    refine ⟨lRegularizedAction S T (α z) 0 v, ?_, (hact z hz).le⟩
    have hmem := H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross
      S hS T le_rfl hv.le (by simpa only [zero_pow two_ne_zero, sub_zero] using hupper)
      hlower hcarrier hmetric (α z) (hα z hz)
    simpa only [hstart z hz, hend z hz] using hmem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

private local instance (j : Fin (H.eventCount + 1)) :
    MeasurableSpace (H.stage j).Carrier := borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) :
    BorelSpace (H.stage j).Carrier := ⟨rfl⟩

theorem lintegral_regularizedC1Density_pos_of_backwardSurvivor
    (first last : Fin (H.eventCount + 1)) (hlt : first < last)
    (p : H.backwardSurvivorDomain first last hlt.le) :
    0 < ∫⁻ q, H.regularizedC1Density first last hlt.le (H.time last)
        (Real.sqrt (H.time last - H.time first)) p.val q
      ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (H.time first)) := by
  obtain ⟨S, hS, _, _, hmem⟩ :=
    H.exists_backwardSurvivor_isSolutionOn_action_mem_history first last hlt
  let v := Real.sqrt (H.time last - H.time first)
  have hv : 0 < v := Real.sqrt_pos.mpr (sub_pos.mpr (H.time_strictMono hlt))
  have hv2 : v ^ 2 = H.time last - H.time first :=
    Real.sq_sqrt (sub_nonneg.mpr (H.time_strictMono hlt).le)
  have ht : H.time last - v ^ 2 = H.time first := by rw [hv2, sub_sub_cancel]
  have hcarrier : ∀ t ∈ Icc 0 v, H.time last - t ^ 2 ∈
      (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le).carrier := by
    intro t ht
    change H.time first ≤ H.time last - t ^ 2 ∧ H.time last - t ^ 2 ≤ H.time last
    have hsq := (sq_le_sq₀ ht.1 hv.le).mpr ht.2
    rw [hv2] at hsq
    constructor <;> nlinarith [sq_nonneg t]
  let L := lRegularizedAction S (H.time last) (fun _ => p) 0 v + 1
  obtain ⟨V, hV, hpV, α, hα, hstart, hend, _, hact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS (H.time last) hv hcarrier
      (fun _ => p) contMDiff_const (show lRegularizedAction S (H.time last) (fun _ => p) 0 v < L by
        dsimp only [L]
        linarith)
  let f := H.backwardSurvivorMap first last hlt.le first le_rfl hlt.le
  have hopen : IsOpen (f '' V) :=
    (H.backwardSurvivorMap_isLocalDiffeomorph first last hlt.le first le_rfl hlt.le).isOpenMap V hV
  have hmass := H.volume_mul_exp_le_lintegral_regularizedC1Density first last hlt.le
    (H.time last) hv p.val hopen.measurableSet (L := L) (by
      rintro q ⟨z, hz, rfl⟩
      refine ⟨lRegularizedAction S (H.time last) (α z) 0 v, ?_, (hact z hz).le⟩
      have hm := hmem (α z) (hα z hz)
      change lRegularizedAction S (H.time last) (α z) 0 v ∈
        H.regularizedC1ActionValues first last hlt.le (H.time last) 0 v (α z 0).val (f (α z v)) at hm
      simpa only [hstart z hz, hend z hz] using hm)
  rw [ht] at hmass
  let μ := riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
    (H.stageMetric first (H.time first))
  have hvol : 0 < μ (f '' V) := by
    let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure _
    exact hopen.measure_pos _ ⟨f p, ⟨p, hpV, rfl⟩⟩
  have hpos := ENNReal.mul_pos_iff.mpr ⟨hvol, ENNReal.ofReal_pos.mpr
    (Real.exp_pos (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi)))⟩
  exact (hpos.trans_le hmass).trans_le (MeasureTheory.setLIntegral_le_lintegral _ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

theorem regularizedC1Density_eq_exp_sInf_of_bddBelow
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T : ℝ) {v : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hne : (H.regularizedC1ActionValues first last hle T 0 v p q).Nonempty)
    (hbdd : BddBelow (H.regularizedC1ActionValues first last hle T 0 v p q)) :
    H.regularizedC1Density first last hle T v p q =
      ENNReal.ofReal (Real.exp (-sInf (H.regularizedC1ActionValues first last hle T 0 v p q) /
        (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  let f : ℝ → ℝ≥0∞ := fun A => ENNReal.ofReal (Real.exp (-A / (2 * v) -
    (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hf : Continuous f := ENNReal.continuous_ofReal.comp
    (Real.continuous_exp.comp (((continuous_id.neg.div_const _).sub continuous_const).sub continuous_const))
  have hanti : Antitone f := by
    intro A B hAB
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right (neg_le_neg hAB) (by positivity : 0 ≤ 2 * v)
    linarith
  have heq := hanti.map_csInf_of_continuousAt hf.continuousAt hne hbdd
  simpa only [sSup_image, f, regularizedC1Density] using heq.symm

theorem regularizedC1Density_eq_exp_of_cost_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T : ℝ) {v A : ℝ} (hv : 0 < v)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hbdd : BddBelow (H.regularizedC1ActionValues first last hle T 0 v p q))
    (hcost : H.regularizedC1Cost first last hle T 0 v p q = (A : WithTop ℝ)) :
    H.regularizedC1Density first last hle T v p q =
      ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  have hne : (H.regularizedC1ActionValues first last hle T 0 v p q).Nonempty := by
    by_contra hn
    have he := H.regularizedC1Cost_eq_top_of_no_competitor first last hle T 0 v p q
      (not_nonempty_iff_eq_empty.mp hn)
    exact WithTop.coe_ne_top (hcost.symm.trans he)
  have hInf : sInf (H.regularizedC1ActionValues first last hle T 0 v p q) = A := by
    apply WithTop.coe_injective
    rw [WithTop.coe_sInf' hne hbdd]
    exact hcost
  rw [H.regularizedC1Density_eq_exp_sInf_of_bddBelow first last hle T hv p q hne hbdd, hInf]

theorem regularizedC1Density_le_exp_of_scalar_lower
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v : ℝ} (hv : 0 < v)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedC1Density first last hle T v p q ≤
      ENNReal.ofReal (Real.exp (B * v ^ 2 / 3 - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  have hlow := H.regularizedC1ActionValues_ge_of_scalar_lower first last hle T 0 v B hscalar p q hA
  simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), sub_zero] at hlow
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hdiv : -A / (2 * v) ≤ B * v ^ 2 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * v)).mpr
    nlinarith
  linarith

private local instance (j : Fin (H.eventCount + 1)) :
    MeasurableSpace (H.stage j).Carrier := borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) :
    BorelSpace (H.stage j).Carrier := ⟨rfl⟩

theorem lintegral_regularizedC1Density_lt_top_of_scalar_lower
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v : ℝ} (hv : 0 < v)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) :
    (∫⁻ q, H.regularizedC1Density first last hle T v p q
      ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
        (H.stageMetric first (T - v ^ 2))) < ⊤ := by
  let μ := riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
    (H.stageMetric first (T - v ^ 2))
  let _ : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hbound := lintegral_mono (μ := μ)
    (H.regularizedC1Density_le_exp_of_scalar_lower first last hle T B hv hscalar p)
  exact hbound.trans_lt (by simp only [lintegral_const]; finiteness)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

def regularizedDensity (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) : ℝ≥0∞ :=
  ⨆ A : ℝ, ⨆ (_ : (A : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B 0 v p q),
    ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi)))

theorem regularizedDensity_eq_zero_iff
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedDensity first last hle T B v p q = 0 ↔
      H.regularizedCost first last hle T B 0 v p q = ⊤ := by
  rw [H.regularizedCost_eq_top_iff]
  constructor
  · intro hzero A hA
    by_contra hne
    obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
    have hle : ENNReal.ofReal (Real.exp (-a / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
        H.regularizedDensity first last hle T B v p q :=
      le_iSup_of_le a (le_iSup_of_le hA le_rfl)
    rw [hzero] at hle
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).not_ge hle
  · intro htop
    apply le_antisymm ?_ zero_le
    apply iSup_le
    intro A
    apply iSup_le
    intro hA
    exact (WithTop.coe_ne_top (htop A hA)).elim

theorem regularizedDensity_pos_iff
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    0 < H.regularizedDensity first last hle T B v p q ↔
      H.regularizedCost first last hle T B 0 v p q ≠ ⊤ := by
  rw [pos_iff_ne_zero]
  exact not_congr (H.regularizedDensity_eq_zero_iff first last hle T B v p q)

theorem regularizedDensity_eq_regularizedC1Density
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedDensity first last hle T B v p q =
      H.regularizedC1Density first last hle T v p q := by
  apply le_antisymm
  · apply iSup_le
    intro A
    apply iSup_le
    intro hA
    let F : ℝ → ℝ≥0∞ := fun ε => ENNReal.ofReal
      (Real.exp (-(A + ε) / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
    have hF : Continuous F := ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (((continuous_const.add continuous_id).neg.div_const _).sub
        continuous_const |>.sub continuous_const))
    have hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
      hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        F ε ≤ H.regularizedC1Density first last hle T v p q := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      obtain ⟨C, hC, hCA⟩ :=
        H.exists_mem_regularizedC1ActionValues_lt_of_mem_regularizedActionValues
          first last hle (by simpa using hupper) hscalar p q hA hε
      exact H.le_regularizedC1Density_of_action_le first last hle T hv p q hC hCA.le
    simpa only [F, add_zero] using le_of_tendsto hlim hbound
  · apply iSup_le
    intro A
    apply iSup_le
    intro hA
    have hAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      first last hle hscalar p q hA
    exact le_iSup_of_le A (le_iSup_of_le hAC le_rfl)

theorem regularizedDensity_eq_exp_of_cost_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v A : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hcost : H.regularizedCost first last hle T B 0 v p q = (A : WithTop ℝ)) :
    H.regularizedDensity first last hle T B v p q =
      ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  rw [H.regularizedDensity_eq_regularizedC1Density first last hle T B hv hupper hscalar p q]
  apply H.regularizedC1Density_eq_exp_of_cost_eq first last hle T hv p q
    (H.regularizedC1ActionValues_bddBelow_of_scalar_lower first last hle T 0 v B hscalar p q)
  rw [← H.regularizedCost_eq_regularizedC1Cost first last hle T B 0 v
    (by simpa using hupper) hscalar p q]
  exact hcost

private local instance (j : Fin (H.eventCount + 1)) :
    MeasurableSpace (H.stage j).Carrier := borel (H.stage j).Carrier
private local instance (j : Fin (H.eventCount + 1)) :
    BorelSpace (H.stage j).Carrier := ⟨rfl⟩

theorem measurable_regularizedDensity
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B : ℝ) {v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) :
    Measurable (H.regularizedDensity first last hle T B v p) := by
  classical
  have hmeas : Measurable (H.regularizedCost first last hle T B 0 v p) :=
    (H.lowerSemicontinuous_regularizedCost first last hle T B 0 v
      (by simpa only [zero_pow two_ne_zero, sub_zero] using hupper) hscalar p).measurable
  let f : WithTop ℝ → ℝ≥0∞ := fun C =>
    if C = ⊤ then 0 else ENNReal.ofReal (Real.exp (-C.untopD 0 / (2 * v) -
      (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hf : Measurable f := by
    apply WithTop.measurable_of_measurable_comp_coe
    have hcont : Continuous (fun C : ℝ => ENNReal.ofReal (Real.exp (-C / (2 * v) -
        (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (((continuous_id.neg.div_const _).sub continuous_const).sub continuous_const))
    simpa only [f, WithTop.coe_ne_top, ↓reduceIte, WithTop.untopD_coe] using hcont.measurable
  have heq : H.regularizedDensity first last hle T B v p =
      f ∘ (fun q => H.regularizedCost first last hle T B 0 v p q) := by
    funext q
    by_cases htop : H.regularizedCost first last hle T B 0 v p q = ⊤
    · simp only [Function.comp_apply, f, htop, ↓reduceIte]
      exact (H.regularizedDensity_eq_zero_iff first last hle T B v p q).mpr htop
    · obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp htop
      have hd := H.regularizedDensity_eq_exp_of_cost_eq first last hle T B hv hupper hscalar p q hA.symm
      simpa only [Function.comp_apply, f, ← hA, WithTop.coe_ne_top, ↓reduceIte,
        WithTop.untopD_coe] using hd
  rw [heq]
  exact hf.comp hmeas

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
