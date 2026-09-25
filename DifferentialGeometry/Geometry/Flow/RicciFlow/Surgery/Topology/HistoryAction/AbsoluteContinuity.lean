import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Measurable
import DifferentialGeometry.Analysis.Integration.Integral.LowerBounded
import DifferentialGeometry.Topology.Order.InfimumAddition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.WithTop

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval
    (j : Fin (H.eventCount + 1)) (T u v : ℝ) (α : ℝ → (H.stage j).Carrier)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α
      (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)) :
    AEStronglyMeasurable (H.stageRegularizedLagrangian j T α)
      (volume.restrict (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))) := by
  cases j using Fin.lastCases with
  | last =>
    by_cases hlast : H.time (Fin.last H.eventCount) < H.horizon
    · have hh := aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval
        (H.finalSlab hlast).flow (H.finalSlab hlast).equation.smoothMetric
        ⟨(H.finalSlab hlast).equation.scalarCont⟩ T α hα (fun t ht => by
          change t ∈ Ioo _ _ at ht
          change T - t ^ 2 ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon
          simpa only [stageDomain, Fin.lastCases_last] using
            H.mapsTo_regularizedStage_Ioo T u v (Fin.last H.eventCount) ht)
      have heq : H.stageRegularizedLagrangian (Fin.last H.eventCount) T α =
          lRegularizedLagrangian (H.finalSlab hlast).flow T α :=
        funext (H.stageRegularizedLagrangian_last hlast T α)
      rw [heq]
      exact hh
    · have hcollapsed : H.stageEndTime (Fin.last H.eventCount) ≤ H.time (Fin.last H.eventCount) := by
        simpa only [H.stageEndTime_last] using le_of_not_gt hlast
      have horder : H.regularizedStageEnd T v (Fin.last H.eventCount) ≤
          H.regularizedStageStart T u (Fin.last H.eventCount) := by
        apply Real.sqrt_le_sqrt
        apply sub_le_sub_left
        exact (min_le_right _ _).trans (hcollapsed.trans (le_max_right _ _))
      rw [Ioo_eq_empty_of_le horder, Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure _
  | cast i =>
    have hh := aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval
      (H.event i).incoming.flow (H.event i).incoming.equation.smoothMetric
      ⟨(H.event i).incoming.equation.scalarCont⟩ T α hα (fun t ht => by
        change T - t ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ)
        simpa only [stageDomain, Fin.lastCases_castSucc] using
          H.mapsTo_regularizedStage_Ioo T u v i.castSucc ht)
    have heq : H.stageRegularizedLagrangian i.castSucc T α =
        lRegularizedLagrangian (H.event i).incoming.flow T α :=
      funext (H.stageRegularizedLagrangian_castSucc i T α)
    rw [heq]
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

private theorem integrable_stage_scalar_floor (B a b : ℝ) :
    Integrable (fun t : ℝ => -2 * B * t ^ 2) (volume.restrict (Ioo a b)) :=
  (continuous_const.mul (continuous_id.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem scalar_floor_le_stageRegularizedLagrangian
    (j : Fin (H.eventCount + 1)) (T B a b : ℝ) (α : ℝ → (H.stage j).Carrier)
    (hscalar : ∀ᵐ t ∂volume.restrict (Ioo a b),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    (fun t => -2 * B * t ^ 2) ≤ᵐ[volume.restrict (Ioo a b)]
      H.stageRegularizedLagrangian j T α := by
  filter_upwards [hscalar] with t ht
  have hkin := metric_inner_self_nonneg (H.stageMetric j (T - t ^ 2)) (α t)
    (lVelocity (I := ThreeModel) α t)
  have hs := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * t ^ 2)
  dsimp only [stageRegularizedLagrangian]
  nlinarith

def stageRegularizedExtendedAction
    (j : Fin (H.eventCount + 1)) (T B : ℝ) (α : ℝ → (H.stage j).Carrier)
    (a b : ℝ) : WithTop ℝ :=
  lowerBoundedIntegral (H.stageRegularizedLagrangian j T α) (fun t => -2 * B * t ^ 2)
    (volume.restrict (Ioo a b))

theorem stageRegularizedExtendedAction_eq_action
    (j : Fin (H.eventCount + 1)) (T B : ℝ) (α : ℝ → (H.stage j).Carrier) {a b : ℝ}
    (hab : a ≤ b) (hint : IntervalIntegrable (H.stageRegularizedLagrangian j T α) volume a b)
    (hscalar : ∀ᵐ t ∂volume.restrict (Ioo a b),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α a b = (H.stageRegularizedAction j T α a b : WithTop ℝ) := by
  rw [stageRegularizedExtendedAction, lowerBoundedIntegral_eq_integral
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hint)
    (integrable_stage_scalar_floor B a b) (H.scalar_floor_le_stageRegularizedLagrangian j T B a b α hscalar)]
  rw [stageRegularizedAction, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem stageRegularizedExtendedAction_eq_top_iff
    (j : Fin (H.eventCount + 1)) (T B : ℝ) (α : ℝ → (H.stage j).Carrier) {a b : ℝ}
    (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable (H.stageRegularizedLagrangian j T α) (volume.restrict (Ioo a b)))
    (hscalar : ∀ᵐ t ∂volume.restrict (Ioo a b),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α a b = ⊤ ↔
      ¬ IntervalIntegrable (H.stageRegularizedLagrangian j T α) volume a b := by
  rw [stageRegularizedExtendedAction, lowerBoundedIntegral_eq_top_iff hmeas
    (integrable_stage_scalar_floor B a b) (H.scalar_floor_le_stageRegularizedLagrangian j T B a b α hscalar)]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  rfl

theorem stageRegularizedExtendedAction_congr_scalar_lower_bound
    (j : Fin (H.eventCount + 1)) (T B C : ℝ) (α : ℝ → (H.stage j).Carrier) (a b : ℝ)
    (hmeas : AEStronglyMeasurable (H.stageRegularizedLagrangian j T α) (volume.restrict (Ioo a b)))
    (hB : ∀ᵐ t ∂volume.restrict (Ioo a b),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t))
    (hC : ∀ᵐ t ∂volume.restrict (Ioo a b),
      -C ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α a b = H.stageRegularizedExtendedAction j T C α a b :=
  lowerBoundedIntegral_congr_lower_bound hmeas
    (integrable_stage_scalar_floor B a b) (integrable_stage_scalar_floor C a b)
    (H.scalar_floor_le_stageRegularizedLagrangian j T B a b α hB)
    (H.scalar_floor_le_stageRegularizedLagrangian j T C a b α hC)

theorem stageRegularizedExtendedAction_eq_top_iff_of_absolutelyContinuousOnInterval
    (j : Fin (H.eventCount + 1)) (T B u v : ℝ) (α : ℝ → (H.stage j).Carrier)
    (hab : H.regularizedStageStart T u j ≤ H.regularizedStageEnd T v j)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α
      (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))
    (hscalar : ∀ᵐ t ∂volume.restrict
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α
        (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j) = ⊤ ↔
      ¬ IntervalIntegrable (H.stageRegularizedLagrangian j T α) volume
        (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j) :=
  H.stageRegularizedExtendedAction_eq_top_iff j T B α hab
    (H.aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval j T u v α hα) hscalar

theorem stageRegularizedExtendedAction_congr_scalar_lower_bound_of_absolutelyContinuousOnInterval
    (j : Fin (H.eventCount + 1)) (T B C u v : ℝ) (α : ℝ → (H.stage j).Carrier)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α
      (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))
    (hB : ∀ᵐ t ∂volume.restrict
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t))
    (hC : ∀ᵐ t ∂volume.restrict
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)),
      -C ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α
        (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j) =
      H.stageRegularizedExtendedAction j T C α
        (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j) :=
  H.stageRegularizedExtendedAction_congr_scalar_lower_bound j T B C α _ _
    (H.aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval j T u v α hα) hB hC

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Filter Set MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem stageRegularizedExtendedAction_congr
    (j : Fin (H.eventCount + 1)) (T B a b : ℝ)
    (α β : ℝ → (H.stage j).Carrier) (heq : EqOn α β (Ioo a b)) :
    H.stageRegularizedExtendedAction j T B α a b = H.stageRegularizedExtendedAction j T B β a b := by
  apply lowerBoundedIntegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hev : α =ᶠ[𝓝 t] β := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact heq hr
  have hval : α t = β t := hev.self_of_nhds
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
  have hvel : lVelocity (I := ThreeModel) α t = lVelocity (I := ThreeModel) β t := by
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  unfold stageRegularizedLagrangian
  rw [hval, hvel]

theorem stageRegularizedExtendedAction_add
    (j : Fin (H.eventCount + 1)) (T B : ℝ) (α : ℝ → (H.stage j).Carrier) {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hmeas : AEStronglyMeasurable (H.stageRegularizedLagrangian j T α) (volume.restrict (Ioo a b)))
    (hscalar : ∀ᵐ t ∂volume.restrict (Ioo a b),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α a b =
      H.stageRegularizedExtendedAction j T B α a c + H.stageRegularizedExtendedAction j T B α c b := by
  apply lowerBoundedIntegral_Ioo_add hac hcb hmeas
  · exact (continuous_const.mul (continuous_id.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · filter_upwards [hscalar] with t ht
    have hkin := metric_inner_self_nonneg (H.stageMetric j (T - t ^ 2)) (α t)
      (lVelocity (I := ThreeModel) α t)
    have hs := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * t ^ 2)
    dsimp only [stageRegularizedLagrangian]
    nlinarith

theorem stageRegularizedExtendedAction_add_of_absolutelyContinuousOnInterval
    (j : Fin (H.eventCount + 1)) (T B u v c : ℝ) (α : ℝ → (H.stage j).Carrier)
    (hac : H.regularizedStageStart T u j ≤ c) (hcb : c ≤ H.regularizedStageEnd T v j)
    (hα : Manifold.absolutelyContinuousOnInterval ThreeModel α
      (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))
    (hscalar : ∀ᵐ t ∂volume.restrict
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)),
      -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) (α t)) :
    H.stageRegularizedExtendedAction j T B α (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j) =
      H.stageRegularizedExtendedAction j T B α (H.regularizedStageStart T u j) c +
        H.stageRegularizedExtendedAction j T B α c (H.regularizedStageEnd T v j) :=
  H.stageRegularizedExtendedAction_add j T B α hac hcb
    (H.aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval j T u v α hα)
    hscalar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def regularizedExtendedAction (first last : Fin (H.eventCount + 1)) (T B u v : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) : WithTop ℝ :=
  ∑ j : H.StageInterval first last, H.stageRegularizedExtendedAction j.val T B (α j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)

def regularizedActionValues (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) : Set (WithTop ℝ) :=
  {A | 0 ≤ u ∧ u ≤ v ∧ T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) ∧
    T - v ^ 2 ∈ H.stageDomain first ∧
    ∃ α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      α ⟨last, hle, le_rfl⟩ u = p ∧ α ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))) ∧
      H.regularizedExtendedAction first last T B u v α = A}

def regularizedCost (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) : WithTop ℝ :=
  sInf (H.regularizedActionValues first last hle T B u v p q)

theorem regularizedCost_eq_top_of_no_competitor
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ) (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (h : H.regularizedActionValues first last hle T B u v p q = ∅) :
    H.regularizedCost first last hle T B u v p q = ⊤ := by
  rw [regularizedCost, h, WithTop.sInf_empty]

theorem regularizedExtendedAction_eq_sum_action
    (first last : Fin (H.eventCount + 1)) {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ j, ∀ᵐ t ∂volume.restrict (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t)) :
    H.regularizedExtendedAction first last T B u v α =
      ((∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) : ℝ) : WithTop ℝ) := by
  unfold regularizedExtendedAction
  simp only [WithTop.coe_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact H.stageRegularizedExtendedAction_eq_action j.val T B (α j)
    (H.regularizedStage_bounds hu huv hupper hlower j).2.1 (hint j) (hscalar j)

theorem regularizedExtendedAction_congr_scalar_lower_bound
    (first last : Fin (H.eventCount + 1)) (T B C u v : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hB : ∀ j, ∀ᵐ t ∂volume.restrict (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t))
    (hC : ∀ j, ∀ᵐ t ∂volume.restrict (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)),
      -C ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t)) :
    H.regularizedExtendedAction first last T B u v α = H.regularizedExtendedAction first last T C u v α := by
  apply Finset.sum_congr rfl
  intro j _
  exact H.stageRegularizedExtendedAction_congr_scalar_lower_bound_of_absolutelyContinuousOnInterval
    j.val T B C u v (α j) (hα j) (hB j) (hC j)

theorem regularizedExtendedAction_eq_top_iff
    (first last : Fin (H.eventCount + 1)) {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ j, ∀ᵐ t ∂volume.restrict (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (α j t)) :
    H.regularizedExtendedAction first last T B u v α = ⊤ ↔
      ∃ j, ¬ IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  simp only [regularizedExtendedAction, WithTop.sum_eq_top, Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  exact H.stageRegularizedExtendedAction_eq_top_iff_of_absolutelyContinuousOnInterval j.val T B u v (α j)
    (H.regularizedStage_bounds hu huv hupper hlower j).2.1 (hα j) (hscalar j)

theorem coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T B u v A : ℝ}
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q) :
    (A : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u v p q := by
  obtain ⟨hu, huv, hupper, hlower, α, hα, hint, hstart, hend, hnode, hsum⟩ := hA
  refine ⟨hu, huv, hupper, hlower, α, ?_, hstart, hend, hnode, ?_⟩
  · intro j
    exact Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hα j).contMDiffOn
  · rw [H.regularizedExtendedAction_eq_sum_action first last hu huv hupper hlower α hint, hsum]
    intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hscalar j t ht (α j t)

theorem regularizedActionValues_congr_scalar_lower_bound
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B C u v : ℝ)
    (hB : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (hC : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -C ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedActionValues first last hle T B u v p q = H.regularizedActionValues first last hle T C u v p q := by
  have heq (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
      (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
      H.regularizedExtendedAction first last T B u v α = H.regularizedExtendedAction first last T C u v α := by
    apply H.regularizedExtendedAction_congr_scalar_lower_bound first last T B C u v α hα
    · intro j
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hB j t ht (α j t)
    · intro j
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hC j t ht (α j t)
  ext A
  constructor
  · rintro ⟨hu, huv, hupper, hlower, α, hα, hstart, hend, hnode, hact⟩
    exact ⟨hu, huv, hupper, hlower, α, hα, hstart, hend, hnode, (heq α hα).symm.trans hact⟩
  · rintro ⟨hu, huv, hupper, hlower, α, hα, hstart, hend, hnode, hact⟩
    exact ⟨hu, huv, hupper, hlower, α, hα, hstart, hend, hnode, (heq α hα).trans hact⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem stageRegularizedExtendedAction_ge
    (j : Fin (H.eventCount + 1)) (T B : ℝ) (α : ℝ → (H.stage j).Carrier) {a b : ℝ}
    (hab : a ≤ b) :
    (↑(-(2 * B / 3) * (b ^ 3 - a ^ 3) : ℝ) : WithTop ℝ) ≤
      H.stageRegularizedExtendedAction j T B α a b := by
  have hh := integral_lower_bound_le_lowerBoundedIntegral
    (H.stageRegularizedLagrangian j T α) (fun t => -2 * B * t ^ 2) (volume.restrict (Ioo a b))
  have hi : ∫ t in Ioo a b, -2 * B * t ^ 2 = -(2 * B / 3) * (b ^ 3 - a ^ 3) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  simpa only [hi, stageRegularizedExtendedAction] using hh

theorem regularizedExtendedAction_ge
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {T B u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    (↑(-(2 * B / 3) * (v ^ 3 - u ^ 3) : ℝ) : WithTop ℝ) ≤
      H.regularizedExtendedAction first last T B u v α := by
  have hh : (∑ j : H.StageInterval first last,
      (↑(-(2 * B / 3) * ((H.regularizedStageEnd T v j.val) ^ 3 -
        (H.regularizedStageStart T u j.val) ^ 3) : ℝ) : WithTop ℝ)) ≤
      H.regularizedExtendedAction first last T B u v α := by
    apply Finset.sum_le_sum
    intro j _
    exact H.stageRegularizedExtendedAction_ge j.val T B (α j)
      (H.regularizedStage_bounds hu huv hupper hlower j).2.1
  simpa only [← WithTop.coe_sum, ← Finset.mul_sum,
    H.sum_regularizedStage_sub (fun t : ℝ => t ^ 3) hle hu huv hupper hlower] using hh

theorem regularizedActionValues_ge
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) {A : WithTop ℝ}
    (hA : A ∈ H.regularizedActionValues first last hle T B u v p q) :
    (↑(-(2 * B / 3) * (v ^ 3 - u ^ 3) : ℝ) : WithTop ℝ) ≤ A := by
  rcases hA with ⟨hu, huv, hupper, hlower, α, _, _, _, _, rfl⟩
  exact H.regularizedExtendedAction_ge first last hle hu huv hupper hlower α

theorem regularizedActionValues_bddBelow
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    BddBelow (H.regularizedActionValues first last hle T B u v p q) :=
  ⟨↑(-(2 * B / 3) * (v ^ 3 - u ^ 3) : ℝ), fun _ hA =>
    H.regularizedActionValues_ge first last hle T B u v p q hA⟩

theorem regularizedCost_ge
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (↑(-(2 * B / 3) * (v ^ 3 - u ^ 3) : ℝ) : WithTop ℝ) ≤
      H.regularizedCost first last hle T B u v p q := by
  by_cases hne : (H.regularizedActionValues first last hle T B u v p q).Nonempty
  · exact le_csInf hne (fun _ hA => H.regularizedActionValues_ge first last hle T B u v p q hA)
  · rw [H.regularizedCost_eq_top_of_no_competitor first last hle T B u v p q
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact le_top

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedCost_le_of_competitor
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) {A : WithTop ℝ}
    (hA : A ∈ H.regularizedActionValues first last hle T B u v p q) :
    H.regularizedCost first last hle T B u v p q ≤ A :=
  csInf_le (H.regularizedActionValues_bddBelow first last hle T B u v p q) hA

theorem regularizedCost_eq_top_iff
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedCost first last hle T B u v p q = ⊤ ↔
      ∀ A ∈ H.regularizedActionValues first last hle T B u v p q, A = ⊤ := by
  constructor
  · intro h A hA
    exact top_unique (h ▸ H.regularizedCost_le_of_competitor first last hle T B u v p q hA)
  · intro h
    by_cases hne : (H.regularizedActionValues first last hle T B u v p q).Nonempty
    · apply top_unique
      apply le_csInf hne
      intro A hA
      rw [h A hA]
    · exact H.regularizedCost_eq_top_of_no_competitor first last hle T B u v p q
        (Set.not_nonempty_iff_eq_empty.mp hne)

theorem regularizedCost_le_regularizedC1Cost
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B u v : ℝ)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedCost first last hle T B u v p q ≤ H.regularizedC1Cost first last hle T u v p q := by
  by_cases hne : (H.regularizedC1ActionValues first last hle T u v p q).Nonempty
  · apply le_csInf (hne.image (fun A : ℝ => (A : WithTop ℝ)))
    rintro A ⟨r, hr, rfl⟩
    exact H.regularizedCost_le_of_competitor first last hle T B u v p q
      (H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues first last hle hscalar p q hr)
  · rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p q
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact le_top

theorem regularizedCost_congr_scalar_lower_bound
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (T B C u v : ℝ)
    (hB : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (hC : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -C ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedCost first last hle T B u v p q = H.regularizedCost first last hle T C u v p q := by
  unfold regularizedCost
  rw [H.regularizedActionValues_congr_scalar_lower_bound first last hle T B C u v hB hC p q]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u})

private theorem sum_stageInterval_split {A : Type v} [AddCommMonoid A]
    {first last : Fin (H.eventCount + 1)} (i : Fin H.eventCount)
    (hf : first ≤ i.succ) (hl : i.castSucc ≤ last)
    (F : H.StageInterval first last → A) :
    ∑ j : H.StageInterval first last, F j =
      (∑ j : H.StageInterval first i.castSucc,
        F ⟨j.val, j.property.1, j.property.2.trans hl⟩) +
      ∑ j : H.StageInterval i.succ last,
        F ⟨j.val, hf.trans j.property.1, j.property.2⟩ := by
  let e₁ : {j : H.StageInterval first last // j.val ≤ i.castSucc} ≃
      H.StageInterval first i.castSucc :=
    { toFun := fun j => ⟨j.val.val, j.val.property.1, j.property⟩
      invFun := fun j =>
        ⟨⟨j.val, j.property.1, j.property.2.trans hl⟩, j.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {j : H.StageInterval first last // ¬ j.val ≤ i.castSucc} ≃
      H.StageInterval i.succ last :=
    { toFun := fun j => ⟨j.val.val, by
          have hj := j.property
          change i.val + 1 ≤ j.val.val.val
          change ¬ j.val.val.val ≤ i.val at hj
          omega, j.val.property.2⟩
      invFun := fun j =>
        ⟨⟨j.val, hf.trans j.property.1, j.property.2⟩, by
          have hj := j.property.1
          change i.val + 1 ≤ j.val.val at hj
          change ¬ j.val.val ≤ i.val
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h₁ := Fintype.sum_equiv e₁ (fun j => F j.val)
    (fun j => F ⟨j.val, j.property.1, j.property.2.trans hl⟩)
    (fun _ => rfl)
  have h₂ := Fintype.sum_equiv e₂ (fun j => F j.val)
    (fun j => F ⟨j.val, hf.trans j.property.1, j.property.2⟩)
    (fun _ => rfl)
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : H.StageInterval first last =>
    j.val ≤ i.castSucc) F, h₁, h₂]

private theorem split_action_values_forward
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T B u v : ℝ} {A : WithTop ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedActionValues first last hle T B u v p q) :
    ∃ z : (H.event i).old, ∃ Aold Anew : WithTop ℝ,
      Aold ∈ H.regularizedActionValues first i.castSucc hf T B
        (Real.sqrt (T - H.time i.succ)) v z.val.val q ∧
      Anew ∈ H.regularizedActionValues i.succ last hl T B
        u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z) ∧
      Aold + Anew = A := by
  classical
  let w := Real.sqrt (T - H.time i.succ)
  have hw := H.event_clock_bounds hu huv hupper hlower i hf hl
  have hw0 : 0 ≤ w := hu.trans hw.1
  have hiT : H.time i.succ ≤ T := by
    have hh := (H.time_strictMono.monotone hl).trans hupper.1
    linarith [sq_nonneg u]
  have huOld : T - w ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [hw.2.2, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  have hvNew : T - w ^ 2 ∈ H.stageDomain i.succ := by
    rw [hw.2.2]
    exact H.time_mem_stageDomain i.succ
  let lo : H.StageInterval first i.castSucc → H.StageInterval first last :=
    fun j => ⟨j.val, j.property.1, j.property.2.trans (i.castSucc_le_succ.trans hl)⟩
  let hi : H.StageInterval i.succ last → H.StageInterval first last :=
    fun j => ⟨j.val, hf.trans (i.castSucc_le_succ.trans j.property.1), j.property.2⟩
  have hstart (j : H.StageInterval first i.castSucc) :
      H.regularizedStageStart T w j.val = H.regularizedStageStart T u j.val :=
    H.regularizedStageStart_eq_at_event_clock hupper i hl j.val j.property.2
  have hend (j : H.StageInterval i.succ last) :
      H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val :=
    H.regularizedStageEnd_eq_at_event_clock hlower i hf hiT j.val j.property.1
  rcases hA with ⟨_, _, _, _, α, hα, hp, hq, hnodes, hsum⟩
  obtain ⟨z, hzold, hznew⟩ := hnodes i hf hl
  let αold : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier := fun j => α (lo j)
  let αnew : (j : H.StageInterval i.succ last) → ℝ → (H.stage j.val).Carrier := fun j => α (hi j)
  let Aold := ∑ j : H.StageInterval first i.castSucc, H.stageRegularizedExtendedAction j.val T B (αold j)
    (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)
  let Anew := ∑ j : H.StageInterval i.succ last, H.stageRegularizedExtendedAction j.val T B (αnew j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
  refine ⟨z, Aold, Anew, ?_, ?_, ?_⟩
  · refine ⟨hw0, hw.2.1, huOld, hlower, αold, ?_, hzold.symm, hq, ?_, rfl⟩
    · intro j
      change Manifold.absolutelyContinuousOnInterval ThreeModel (αold j)
        (H.regularizedStageStart T w j.val) (H.regularizedStageEnd T v j.val)
      rw [hstart j]
      exact hα (lo j)
    · intro k hfk hki
      exact hnodes k hfk (hki.trans (i.castSucc_le_succ.trans hl))
  · refine ⟨hu, hw.1, hupper, hvNew, αnew, ?_, hp, hznew.symm, ?_, rfl⟩
    · intro j
      change Manifold.absolutelyContinuousOnInterval ThreeModel (αnew j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
      rw [hend j]
      exact hα (hi j)
    · intro k hik hkl
      exact hnodes k (hf.trans (i.castSucc_le_succ.trans hik)) hkl
  · have hsplit := H.sum_stageInterval_split i (hf.trans i.castSucc_le_succ)
      (i.castSucc_le_succ.trans hl) (fun j => H.stageRegularizedExtendedAction j.val T B (α j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    change (∑ j : H.StageInterval first last, H.stageRegularizedExtendedAction j.val T B (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) = A at hsum
    rw [hsum] at hsplit
    rw [hsplit]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j _
      simp only [αold, lo, hstart j]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [αnew, hi, hend j]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem split_action_values_backward
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T B u v : ℝ} {A : WithTop ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hsplit : ∃ z : (H.event i).old, ∃ Aold Anew : WithTop ℝ,
      Aold ∈ H.regularizedActionValues first i.castSucc hf T B
        (Real.sqrt (T - H.time i.succ)) v z.val.val q ∧
      Anew ∈ H.regularizedActionValues i.succ last hl T B
        u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z) ∧
      Aold + Anew = A) :
    A ∈ H.regularizedActionValues first last hle T B u v p q := by
  classical
  let w := Real.sqrt (T - H.time i.succ)
  have hw := H.event_clock_bounds hu huv hupper hlower i hf hl
  have hw0 : 0 ≤ w := hu.trans hw.1
  have hiT : H.time i.succ ≤ T := by
    have hh := (H.time_strictMono.monotone hl).trans hupper.1
    linarith [sq_nonneg u]
  have huOld : T - w ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [hw.2.2, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  have hvNew : T - w ^ 2 ∈ H.stageDomain i.succ := by
    rw [hw.2.2]
    exact H.time_mem_stageDomain i.succ
  let lo : H.StageInterval first i.castSucc → H.StageInterval first last :=
    fun j => ⟨j.val, j.property.1, j.property.2.trans (i.castSucc_le_succ.trans hl)⟩
  let hi : H.StageInterval i.succ last → H.StageInterval first last :=
    fun j => ⟨j.val, hf.trans (i.castSucc_le_succ.trans j.property.1), j.property.2⟩
  have hstart (j : H.StageInterval first i.castSucc) :
      H.regularizedStageStart T w j.val = H.regularizedStageStart T u j.val :=
    H.regularizedStageStart_eq_at_event_clock hupper i hl j.val j.property.2
  have hend (j : H.StageInterval i.succ last) :
      H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val :=
    H.regularizedStageEnd_eq_at_event_clock hlower i hf hiT j.val j.property.1
  rcases hsplit with ⟨z, Aold, Anew, hOld, hNew, hsum⟩
  rcases hOld with ⟨_, _, _, _, αold, hold, hpold, hqold, hnold, hsumold⟩
  rcases hNew with ⟨_, _, _, _, αnew, hnew, hpnew, hqnew, hnnew, hsumnew⟩
  let α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    fun j => if hji : j.val ≤ i.castSucc then αold ⟨j.val, j.property.1, hji⟩
      else αnew ⟨j.val, by
        change i.val + 1 ≤ j.val.val
        change ¬ j.val.val ≤ i.val at hji
        omega, j.property.2⟩
  have hlo (j : H.StageInterval first i.castSucc) : α (lo j) = αold j := by
    simp only [α, lo, dif_pos j.property.2]
  have hhi (j : H.StageInterval i.succ last) : α (hi j) = αnew j := by
    have hn : ¬ j.val ≤ i.castSucc := not_le_of_gt (i.castSucc_lt_succ.trans_le j.property.1)
    simp only [α, hi, dif_neg hn]
  have hold_eq (j : H.StageInterval first last) (hj : j.val ≤ i.castSucc) :
      α j = αold ⟨j.val, j.property.1, hj⟩ := by simp only [α, dif_pos hj]
  have hnew_eq (j : H.StageInterval first last) (hj : i.succ ≤ j.val) :
      α j = αnew ⟨j.val, hj, j.property.2⟩ := by
    simp only [α, dif_neg (not_le_of_gt (i.castSucc_lt_succ.trans_le hj))]
  refine ⟨hu, huv, hupper, hlower, α, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val ≤ i.castSucc
    · rw [hold_eq j hj, ← hstart ⟨j.val, j.property.1, hj⟩]
      exact hold ⟨j.val, j.property.1, hj⟩
    · have hj' : i.succ ≤ j.val := by
        change i.val + 1 ≤ j.val.val
        change ¬ j.val.val ≤ i.val at hj
        omega
      rw [hnew_eq j hj', ← hend ⟨j.val, hj', j.property.2⟩]
      exact hnew ⟨j.val, hj', j.property.2⟩
  · rw [hnew_eq ⟨last, hle, le_rfl⟩ hl]
    exact hpnew
  · rw [hold_eq ⟨first, le_rfl, hle⟩ hf]
    exact hqold
  · intro k hfk hkl
    rcases lt_trichotomy k i with hki | rfl | hik
    · have hks : k.succ ≤ i.castSucc := by
        change k.val + 1 ≤ i.val
        change k.val < i.val at hki
        omega
      obtain ⟨z', hz', hz''⟩ := hnold k hfk hks
      refine ⟨z', ?_, ?_⟩
      · rw [hold_eq ⟨k.castSucc, hfk, k.castSucc_le_succ.trans hkl⟩ (k.castSucc_le_succ.trans hks)]
        exact hz'
      · rw [hold_eq ⟨k.succ, hfk.trans k.castSucc_le_succ, hkl⟩ hks]
        exact hz''
    · refine ⟨z, ?_, ?_⟩
      · rw [hold_eq ⟨k.castSucc, hfk, k.castSucc_le_succ.trans hkl⟩ le_rfl]
        exact hpold.symm
      · rw [hnew_eq ⟨k.succ, hfk.trans k.castSucc_le_succ, hkl⟩ le_rfl]
        exact hqnew.symm
    · have his : i.succ ≤ k.castSucc := by
        change i.val + 1 ≤ k.val
        change i.val < k.val at hik
        omega
      obtain ⟨z', hz', hz''⟩ := hnnew k his hkl
      refine ⟨z', ?_, ?_⟩
      · rw [hnew_eq ⟨k.castSucc, hfk, k.castSucc_le_succ.trans hkl⟩ his]
        exact hz'
      · rw [hnew_eq ⟨k.succ, hfk.trans k.castSucc_le_succ, hkl⟩ (his.trans k.castSucc_le_succ)]
        exact hz''
  · unfold regularizedExtendedAction
    rw [H.sum_stageInterval_split i (hf.trans i.castSucc_le_succ) (i.castSucc_le_succ.trans hl)]
    rw [← hsum]
    apply congrArg₂ (· + ·)
    · convert hsumold using 1
      apply Finset.sum_congr rfl
      intro j _
      change H.stageRegularizedExtendedAction j.val T B (α (lo j)) _ _ = _
      rw [hlo j, hstart j]
    · convert hsumnew using 1
      apply Finset.sum_congr rfl
      intro j _
      change H.stageRegularizedExtendedAction j.val T B (α (hi j)) _ _ = _
      rw [hhi j, hend j]

theorem mem_regularizedActionValues_split_at_event
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T B u v : ℝ} {A : WithTop ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    A ∈ H.regularizedActionValues first last hle T B u v p q ↔
      ∃ z : (H.event i).old, ∃ Aold Anew : WithTop ℝ,
        Aold ∈ H.regularizedActionValues first i.castSucc hf T B
          (Real.sqrt (T - H.time i.succ)) v z.val.val q ∧
        Anew ∈ H.regularizedActionValues i.succ last hl T B
          u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z) ∧
        Aold + Anew = A := by
  exact ⟨split_action_values_forward H hle i hf hl hu huv hupper hlower p q,
    split_action_values_backward H hle i hf hl hu huv hupper hlower p q⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedCost_dynamic_programming_at_event
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {T u v B : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    H.regularizedCost first last hle T B u v p q =
      sInf (Set.range fun z : (H.event i).old =>
        H.regularizedCost first i.castSucc hf T B (Real.sqrt (T - H.time i.succ)) v z.val.val q +
        H.regularizedCost i.succ last hl T B u (Real.sqrt (T - H.time i.succ)) p ((H.event i).oldOutput z)) := by
  classical
  let w := Real.sqrt (T - H.time i.succ)
  let A := H.regularizedActionValues first last hle T B u v p q
  let Ao (z : (H.event i).old) := H.regularizedActionValues first i.castSucc hf T B w v z.val.val q
  let An (z : (H.event i).old) := H.regularizedActionValues i.succ last hl T B u w p ((H.event i).oldOutput z)
  let F (z : (H.event i).old) : Set (WithTop ℝ) :=
    Set.image2 (fun a b : WithTop ℝ => a + b) (Ao z) (An z)
  let U : Set (WithTop ℝ) := ⋃ z, F z
  have hsplit : A = ⋃ z, Set.image2 (fun a b : WithTop ℝ => a + b) (Ao z) (An z) := by
    ext r
    rw [H.mem_regularizedActionValues_split_at_event hle i hf hl hu huv hupper hlower p q]
    simp only [Set.mem_iUnion, Set.mem_image2]
    constructor
    · rintro ⟨z, ao, an, ho, hn, heq⟩
      exact ⟨z, ao, ho, an, hn, heq⟩
    · rintro ⟨z, ao, ho, an, hn, heq⟩
      exact ⟨z, ao, an, ho, hn, heq⟩
  have hUeq : U = A := hsplit.symm
  have hUbdd : BddBelow U := by
    rw [hUeq]
    exact H.regularizedActionValues_bddBelow first last hle T B u v p q
  have hFbdd (z : (H.event i).old) : BddBelow (F z) :=
    hUbdd.mono (fun _ hx => Set.mem_iUnion_of_mem z hx)
  have hFglb (z : (H.event i).old) : IsGLB (F z) (sInf (F z)) := WithTop.isGLB_sInf' (hFbdd z)
  have hRangeBdd : BddBelow (Set.range fun z => sInf (F z)) := by
    obtain ⟨c, hc⟩ := hUbdd
    refine ⟨c, ?_⟩
    rintro y ⟨z, rfl⟩
    apply (hFglb z).2
    intro y hy
    exact hc (Set.mem_iUnion_of_mem z hy)
  have hOuter : sInf U = sInf (Set.range fun z => sInf (F z)) :=
    (WithTop.isGLB_sInf' hUbdd).unique
      ((isGLB_iUnion_iff_of_isGLB hFglb _).mp (WithTop.isGLB_sInf' hRangeBdd))
  have hbo (z : (H.event i).old) : BddBelow (Ao z) :=
    H.regularizedActionValues_bddBelow first i.castSucc hf T B w v z.val.val q
  have hbn (z : (H.event i).old) : BddBelow (An z) :=
    H.regularizedActionValues_bddBelow i.succ last hl T B u w p ((H.event i).oldOutput z)
  have hadd (z : (H.event i).old) :
      H.regularizedCost first i.castSucc hf T B w v z.val.val q +
        H.regularizedCost i.succ last hl T B u w p ((H.event i).oldOutput z) = sInf (F z) :=
    WithTop.sInf_add (hbo z) (hbn z)
  change sInf A = _
  rw [← hUeq, hOuter]
  exact congrArg (fun F : (H.event i).old → WithTop ℝ => sInf (Set.range F))
    (funext (fun z => (hadd z).symm))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
