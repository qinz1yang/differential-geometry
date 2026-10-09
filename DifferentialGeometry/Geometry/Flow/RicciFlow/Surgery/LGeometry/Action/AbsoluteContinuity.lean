import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorMetricSeam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
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
    simp only [α, lo, dite_eq_left j.property.2]
  have hhi (j : H.StageInterval i.succ last) : α (hi j) = αnew j := by
    have hn : ¬ j.val ≤ i.castSucc := not_le_of_gt (i.castSucc_lt_succ.trans_le j.property.1)
    simp only [α, hi, dite_eq_right hn]
  have hold_eq (j : H.StageInterval first last) (hj : j.val ≤ i.castSucc) :
      α j = αold ⟨j.val, j.property.1, hj⟩ := by simp only [α, dite_eq_left hj]
  have hnew_eq (j : H.StageInterval first last) (hj : i.succ ≤ j.val) :
      α j = αnew ⟨j.val, hj, j.property.2⟩ := by
    simp only [α, dite_eq_right (not_le_of_gt (i.castSucc_lt_succ.trans_le hj))]
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

section

open Set Filter
open scoped Topology

private theorem exists_finite_action_vector_limit
    {ι : Type*} [Fintype ι] (f : ℕ → ι → ℝ) (lower upper : ι → ℝ) (ell : ℝ)
    (hbound : ∀ n i, lower i ≤ f n i ∧ f n i ≤ upper i)
    (hsum : Tendsto (fun n => ∑ i, f n i) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (values : ι → ℝ), StrictMono phi ∧
      (∀ i, Tendsto (fun n => f (phi n) i) atTop (𝓝 (values i))) ∧
      ∑ i, values i = ell := by
  have hmem (n : ℕ) : f n ∈ Icc lower upper :=
    ⟨fun i => (hbound n i).1, fun i => (hbound n i).2⟩
  obtain ⟨values, _, phi, hphi, hconv⟩ := isCompact_Icc.tendsto_subseq hmem
  have hpoint (i : ι) : Tendsto (fun n => f (phi n) i) atTop (𝓝 (values i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hconv
  have htotal : Tendsto (fun n => ∑ i, f (phi n) i) atTop (𝓝 (∑ i, values i)) :=
    tendsto_finsetSum _ (fun i _ => hpoint i)
  exact ⟨phi, values, hphi, hpoint, tendsto_nhds_unique htotal (hsum.comp hphi.tendsto_atTop)⟩

private theorem exists_finset_subsequence_limits
    {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (s : Finset ι) (f : (i : ι) → ℕ → X i) (R : (i : ι) → X i → Prop)
    (h : ∀ i ∈ s, ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ (psi : ℕ → ℕ) (x : X i), StrictMono psi ∧ R i x ∧
        Tendsto (f i ∘ phi ∘ psi) atTop (𝓝 x)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ i ∈ s,
      ∃ x : X i, R i x ∧ Tendsto (f i ∘ phi) atTop (𝓝 x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨phi, hphi, hlim⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨psi, x, hpsi, hx, hconv⟩ := h i (Finset.mem_insert_self _ _) phi hphi
    refine ⟨phi ∘ psi, hphi.comp hpsi, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨x, hx, hconv⟩
    · obtain ⟨y, hy, hconvj⟩ := hlim j hj
      exact ⟨y, hy, hconvj.comp hpsi.tendsto_atTop⟩

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

private theorem exists_old_of_tendsto
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    {ι : Type*} {l : Filter ι} [NeBot l]
    {alpha : ι → P.Carrier} {beta : ι → Q.Carrier} {p : P.Carrier} {q : Q.Carrier}
    (halpha : Tendsto alpha l (𝓝 p)) (hbeta : Tendsto beta l (𝓝 q))
    (hnode : ∀ᶠ n in l, ∃ z : E.old, z.val.val = alpha n ∧ E.oldOutput z = beta n) :
    ∃ z : E.old, z.val.val = p ∧ E.oldOutput z = q := by
  let : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
  let f : E.old → P.Carrier × Q.Carrier := fun z => (z.val.val, E.oldOutput z)
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).prodMk E.oldOutput.continuous
  have hmem : (p, q) ∈ range f := (isCompact_range hf).isClosed.mem_of_tendsto
    (halpha.prodMk_nhds hbeta) (by
      filter_upwards [hnode] with n hn
      obtain ⟨z, hz1, hz2⟩ := hn
      exact ⟨z, Prod.ext hz1 hz2⟩)
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uOldLimit
variable (H : ObservedHistory.{uOldLimit})

private theorem exists_subsequence_old_stage_action_le_of_tendsto_action
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (j : H.StageInterval first last) (hj : j.val < last)
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier)
    (halpha : ∀ n k, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n k)
      (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)))
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hint : ∀ n, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ n, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ A)
    (haction : Tendsto (fun n => H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → (H.stage j.val).Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T gamma) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      H.stageRegularizedAction j.val T gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ ell := by
  rcases j with ⟨k, hk⟩
  cases k using Fin.lastCases with
  | last => exact False.elim ((not_lt_of_ge (Fin.le_last last)) hj)
  | cast i =>
    have hl : i.succ ≤ last := by
      change i.val + 1 ≤ last.val
      exact hj
    have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
      ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
    have hstart := H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl
    have hclocks := H.regularizedStage_endpoint_clocks hupperIcc huv hu
      (⟨i.castSucc, hk⟩ : H.StageInterval first last)
    have hterminal : T - (H.regularizedStageStart T u i.castSucc) ^ 2 = H.time i.succ := by
      rw [hclocks.1, H.stageEndTime_castSucc]
      exact min_eq_right ((H.time_strictMono.monotone hl).trans hupperIcc.1)
    have hpastlt : T - v ^ 2 < H.time i.succ := by
      let tPast : Icc (0 : ℝ) H.horizon := ⟨T - v ^ 2, H.stageDomain_subset first hpast⟩
      have hactive : H.activeStage tPast = first := (H.mem_stageDomain_iff tPast first).mp hpast
      by_contra hn
      have hle : i.succ ≤ first := by
        simpa only [hactive] using H.le_activeStage tPast i.succ (not_lt.mp hn)
      exact (not_le_of_gt (hk.1.trans_lt i.castSucc_lt_succ)) hle
    have hmaxlt : max (T - v ^ 2) (H.time i.castSucc) < H.time i.succ :=
      max_lt hpastlt (H.time_strictMono i.castSucc_lt_succ)
    have hstart0 : 0 ≤ H.regularizedStageStart T u i.castSucc := Real.sqrt_nonneg _
    have hend0 : 0 ≤ H.regularizedStageEnd T v i.castSucc := Real.sqrt_nonneg _
    have hstrict : H.regularizedStageStart T u i.castSucc <
        H.regularizedStageEnd T v i.castSucc := by
      by_contra hn
      have hsq := (sq_le_sq₀ hend0 hstart0).mpr (not_lt.mp hn)
      nlinarith only [hterminal, hclocks.2, hmaxlt, hsq]
    have hphysicalPast : H.time i.castSucc ≤ T - (H.regularizedStageEnd T v i.castSucc) ^ 2 := by
      rw [hclocks.2]
      exact le_max_right _ _
    let E := H.event i
    let : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
    let K : Set E.incoming.terminalRegularOpen := range E.oldTerminal
    have hK : IsCompact K := isCompact_range E.oldTerminal.continuous
    have hstartK (n : ℕ) : alpha n ⟨i.castSucc, hk⟩
        (H.regularizedStageStart T u i.castSucc) ∈ Subtype.val '' K := by
      obtain ⟨z, hz, _⟩ := hnodes n i hk.1 hl
      refine ⟨E.oldTerminal z, mem_range_self z, ?_⟩
      rw [E.oldTerminal_eq, hstart]
      exact hz
    have hlag (gamma : ℝ → (H.stage i.castSucc).Carrier) :
        H.stageRegularizedLagrangian i.castSucc T gamma =
          lRegularizedLagrangian E.incoming.flow T gamma :=
      funext (H.stageRegularizedLagrangian_castSucc i T gamma)
    obtain ⟨phi, gamma, hgamma, hphi, hconv, _, hAC, hInt, hbound⟩ :=
      E.terminal.exists_subsequence_action_le_of_tendsto_action K hK hstart0 hstrict
        hterminal hphysicalPast A B ell hB (fun n => alpha n ⟨i.castSucc, hk⟩)
        (fun n => halpha n ⟨i.castSucc, hk⟩) hstartK
        (fun n => by simpa only [hlag] using hint n)
        (fun n r hr => by
          change -B ≤ metricScalarAt ((H.event i).incoming.flow.base.metric (T - r ^ 2))
            (alpha n ⟨i.castSucc, hk⟩ r)
          simpa only [stageMetric, Fin.lastCases_castSucc] using hscalar n r hr)
        (fun n => by simpa only [H.stageRegularizedAction_castSucc] using hact n)
        (by simpa only [H.stageRegularizedAction_castSucc] using haction)
    refine ⟨phi, gamma, hgamma, hphi, hconv, hAC, ?_, ?_⟩
    · simpa only [hlag] using hInt
    · simpa only [H.stageRegularizedAction_castSucc] using hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uFinal

private theorem exists_subsequence_stageAction_le_of_tendsto_at_observed_time
    (H : ObservedHistory.{uFinal}) (t : Icc (0 : ℝ) H.horizon)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = t.val)
    (ha : H.time (H.activeStage t) ≤ T - v ^ 2)
    (p : (H.stageAt t).Carrier) (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → ℝ → (H.stageAt t).Carrier)
    (halpha : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n) (Icc u v))
    (hstart : ∀ n, alpha n u = p)
    (hscalar : ∀ n, ∀ r ∈ Ioo u v,
      -B ≤ metricScalarAt (H.stageMetric (H.activeStage t) (T - r ^ 2)) (alpha n r))
    (hact : ∀ n, H.stageRegularizedAction (H.activeStage t) T (alpha n) u v ≤ A)
    (haction : Tendsto
      (fun n => H.stageRegularizedAction (H.activeStage t) T (alpha n) u v)
      atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → (H.stageAt t).Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) r.val,
        (halpha (phi n)).continuousOn.domRestrict⟩ : C(Icc u v, (H.stageAt t).Carrier)))
        atTop (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      gamma u = p ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v ∧
      IntervalIntegrable (H.stageRegularizedLagrangian (H.activeStage t) T gamma)
        volume u v ∧
      H.stageRegularizedAction (H.activeStage t) T gamma u v ≤ ell := by
  let : TopologicalSpace.MetrizableSpace (H.stageAt t).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stageAt t).Carrier
  let : MetricSpace (H.stageAt t).Carrier := TopologicalSpace.metrizableSpaceMetric _
  have ht : H.time (H.activeStage t) < t.val := by
    have hsq : u ^ 2 < v ^ 2 := (sq_lt_sq₀ hu (hu.trans huv.le)).2 huv
    linarith only [ha, hTu, hsq]
  generalize hS : H.closedPrefixAt t ht = S
  let G : (H.stageAt t).IncomingSlab (H.time (H.activeStage t)) t.val :=
    S.restrictIncoming le_rfl S.lt le_rfl
  let L : G.TerminalLimitMetric := S.endpointTerminalLimitMetric (H.stageAt t)
  have hmetric (r : ℝ) : G.flow.base.metric r = H.stageMetric (H.activeStage t) r := by
    change S.flow.base.metric r = _
    rw [← hS]
    exact H.closedPrefixAt_metric t ht r
  have hlag (beta : ℝ → (H.stageAt t).Carrier) :
      lRegularizedLagrangian G.flow T beta =
        H.stageRegularizedLagrangian (H.activeStage t) T beta := by
    funext r
    simp only [lRegularizedLagrangian, stageRegularizedLagrangian,
      SolutionOn.scalar, SolutionFamily.scalar, hmetric]
  have hactionEq (beta : ℝ → (H.stageAt t).Carrier) :
      lRegularizedAction G.flow T beta u v =
        H.stageRegularizedAction (H.activeStage t) T beta u v := by
    unfold lRegularizedAction stageRegularizedAction
    rw [hlag]
  let pG : G.terminalRegularOpen := ⟨p, by
    change p ∈ G.terminalRegularRegion
    rw [S.terminalRegularRegion_eq_univ]
    exact mem_univ _⟩
  have hclock (r : ℝ) (hr : r ∈ Icc u v) :
      T - r ^ 2 ∈ Icc (H.time (H.activeStage t)) t.val := by
    have hl := pow_le_pow_left₀ hu hr.1 2
    have hr' := pow_le_pow_left₀ (hu.trans hr.1) hr.2 2
    constructor <;> linarith only [ha, hTu, hl, hr']
  have hint (n : ℕ) :
      IntervalIntegrable (lRegularizedLagrangian G.flow T (alpha n)) volume u v := by
    change IntervalIntegrable (lRegularizedLagrangian S.flow T (alpha n)) volume u v
    have hMet : MetricFamilySmoothOn (I := ThreeModel)
        (RealTimeInterval.closed (H.time (H.activeStage t)) t.val ht.le) S.flow.family.metric :=
      S.equation.smoothMetric
    have hSc : ScalarSTContOn S.flow := ⟨S.equation.scalarCont⟩
    exact intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
      (I := ThreeModel) S.flow hMet hSc
      T u v huv.le (alpha n) (halpha n) hclock
  obtain ⟨phi, gamma, hgamma, hphi, hconv, hpoint, hAC, hInt, hle⟩ :=
    L.exists_subsequence_action_le_of_tendsto_action (P := H.stageAt t) (G := G) {pG} isCompact_singleton
      hu huv hTu ha A B ell hB alpha halpha
      (fun n => ⟨pG, mem_singleton pG, (hstart n).symm⟩) hint
      (fun n r hr => by
        change -B ≤ metricScalarAt (G.flow.base.metric (T - r ^ 2)) (alpha n r)
        rw [hmetric]
        exact hscalar n r hr)
      (fun n => by rw [hactionEq]; exact hact n)
      (by simpa only [hactionEq] using haction)
  refine ⟨phi, gamma, hgamma, hphi, hconv, ?_, hAC, ?_, ?_⟩
  · rcases hpoint with ⟨z, hz, heq⟩
    have hz' : z = pG := mem_singleton_iff.mp hz
    simpa only [hz'] using heq.symm
  · rwa [hlag] at hInt
  · rwa [hactionEq] at hle

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uStageZero
variable (H : ObservedHistory.{uStageZero})

private theorem exists_zero_final_stage_limit
    {last : Fin (H.eventCount + 1)} {T u v : ℝ} (hu : 0 ≤ u)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hcollapsed : H.regularizedStageStart T u last = H.regularizedStageEnd T v last)
    (p : (H.stage last).Carrier) (α : ℕ → ℝ → (H.stage last).Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n)
      (Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hstart : ∀ n, α n u = p) :
    H.regularizedStageStart T u last = u ∧ H.regularizedStageEnd T v last = u ∧
      (∀ n, H.stageRegularizedAction last T (α n)
        (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) = 0) ∧
      ∃ (φ : ℕ → ℕ) (γ : ℝ → (H.stage last).Carrier) (hγ : Continuous γ),
        φ = id ∧ γ = (fun _ => p) ∧ StrictMono φ ∧
        Tendsto (fun n => (⟨fun r => α (φ n) r.val,
          (hα (φ n)).continuousOn.domRestrict⟩ :
            C(Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last),
              (H.stage last).Carrier))) atTop
          (𝓝 ⟨fun r => γ r.val, hγ.comp continuous_subtype_val⟩) ∧
        γ u = p ∧
        Manifold.absolutelyContinuousOnInterval ThreeModel γ
          (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) ∧
        IntervalIntegrable (H.stageRegularizedLagrangian last T γ) volume
          (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) ∧
        H.stageRegularizedAction last T γ
          (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) = 0 := by
  have hs : H.regularizedStageStart T u last = u :=
    H.regularizedStageStart_eq_of_mem_Icc hu
      ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have he : H.regularizedStageEnd T v last = u := hcollapsed.symm.trans hs
  have hzero (α : ℝ → (H.stage last).Carrier) : H.stageRegularizedAction last T α
      (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) = 0 := by
    simp only [hs, he, stageRegularizedAction, intervalIntegral.integral_same]
  refine ⟨hs, he, fun n => hzero (α n), id, (fun _ => p), continuous_const,
    rfl, rfl, strictMono_id, ?_, rfl, ?_, ?_, hzero _⟩
  · have heq (n : ℕ) :
        (⟨fun r => α (id n) r.val, (hα (id n)).continuousOn.domRestrict⟩ :
          C(Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last),
            (H.stage last).Carrier)) = ⟨fun _ => p, continuous_const⟩ := by
      ext r
      have hr : r.val = u :=
        le_antisymm (r.property.2.trans_eq he) (hs.symm.trans_le r.property.1)
      change α (id n) r.val = p
      simpa only [id_eq, hr] using hstart n
    simpa only [heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (⟨fun _ => p, continuous_const⟩ :
          C(Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last),
            (H.stage last).Carrier))) atTop (𝓝 _))
  · let : IsManifold ThreeModel 1 (H.stage last).Carrier := IsManifold.of_le (n := ∞) (by decide)
    exact Manifold.absolutelyContinuousOnInterval_of_contMDiffOn contMDiffOn_const
  · rw [hs, he]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uStageLimit
variable (H : ObservedHistory.{uStageLimit})

private theorem exists_subsequence_stage_action_le_of_tendsto_action
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (hle : first ≤ last) (j : H.StageInterval first last)
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier)
    (halpha : ∀ n k, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n k)
      (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)))
    (hstart : ∀ n, alpha n ⟨last, hle, le_rfl⟩ u = p)
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hint : ∀ n, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ n, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ A)
    (haction : Tendsto (fun n => H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → (H.stage j.val).Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T gamma) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      H.stageRegularizedAction j.val T gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ ell := by
  rcases lt_or_eq_of_le j.property.2 with hj | hj
  · exact H.exists_subsequence_old_stage_action_le_of_tendsto_action j hj hu huv hupper hpast
      A B ell hB alpha halpha hnodes hint hscalar hact haction
  rcases j with ⟨k, hk⟩
  dsimp only at hj
  subst k
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hs : H.regularizedStageStart T u last = u :=
    H.regularizedStageStart_eq_of_mem_Icc hu hupperIcc
  have hbounds := H.regularizedStage_bounds hu huv hupperIcc hpast
    (⟨last, hle, le_rfl⟩ : H.StageInterval first last)
  rcases hbounds.2.1.eq_or_lt with hcollapsed | hstrict
  · obtain ⟨_, _, hzero, phi, gamma, hgamma, _, _, hphi, hconv, _, hAC, hInt, hbound⟩ :=
      H.exists_zero_final_stage_limit hu hupper hcollapsed p
        (fun n => alpha n ⟨last, hle, le_rfl⟩)
        (fun n => halpha n ⟨last, hle, le_rfl⟩) hstart
    have hell : ell = 0 := tendsto_nhds_unique haction (by
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact ⟨phi, gamma, hgamma, hphi, hconv, hAC, hInt, hbound.le.trans_eq hell.symm⟩
  · generalize ht : (⟨T - u ^ 2, H.stageDomain_subset last hupper⟩ :
        Icc (0 : ℝ) H.horizon) = t
    have hTu : T - u ^ 2 = t.val := congrArg Subtype.val ht
    have hactive : H.activeStage t = last := (H.mem_stageDomain_iff t last).mp (by
      rw [← hTu]
      exact hupper)
    subst last
    have hclocks := H.regularizedStage_endpoint_clocks hupperIcc huv hu
      (⟨H.activeStage t, hle, le_rfl⟩ : H.StageInterval first (H.activeStage t))
    have hphysicalPast : H.time (H.activeStage t) ≤
        T - (H.regularizedStageEnd T v (H.activeStage t)) ^ 2 := by
      rw [hclocks.2]
      exact le_max_right _ _
    obtain ⟨phi, gamma, hgamma, hphi, hconv, _, hAC, hInt, hbound⟩ :=
      H.exists_subsequence_stageAction_le_of_tendsto_at_observed_time t
        hu (by simpa only [hs] using hstrict) hTu hphysicalPast p A B ell hB
        (fun n => alpha n ⟨H.activeStage t, hle, le_rfl⟩)
        (fun n => by simpa only [hs] using halpha n ⟨H.activeStage t, hle, le_rfl⟩) hstart
        (fun n r hr => hscalar n r (by simpa only [hs] using hr))
        (fun n => by simpa only [hs] using hact n)
        (by simpa only [hs] using haction)
    refine ⟨phi, gamma, hgamma, hphi, ?_, ?_, ?_, ?_⟩
    · let e : C(Icc (H.regularizedStageStart T u (H.activeStage t))
          (H.regularizedStageEnd T v (H.activeStage t)),
          Icc u (H.regularizedStageEnd T v (H.activeStage t))) :=
        ⟨fun r => ⟨r.val, by simpa only [hs] using r.property⟩,
          continuous_subtype_val.subtype_mk (fun r => by simpa only [hs] using r.property)⟩
      exact (ContinuousMap.continuous_precomp e).continuousAt.tendsto.comp hconv
    · simpa only [hs] using hAC
    · simpa only [hs] using hInt
    · simpa only [hs] using hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryLimit

theorem exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_free_endpoint
    (H : ObservedHistory.{uHistoryLimit})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier)
    (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (halpha : ∀ n j, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hint : ∀ n j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j))
      volume (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hstart : ∀ n, alpha n ⟨last, hle, le_rfl⟩ u = p)
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ n j, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ A)
    (haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
      (hgamma : ∀ j, Continuous (gamma j)),
      StrictMono phi ∧
      (∀ j, Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma j r.val, (hgamma j).comp continuous_subtype_val⟩)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ ell := by
  classical
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let a (j : H.StageInterval first last) := H.regularizedStageStart T u j.val
  let b (j : H.StageInterval first last) := H.regularizedStageEnd T v j.val
  let action (n : ℕ) (j : H.StageInterval first last) :=
    H.stageRegularizedAction j.val T (alpha n j) (a j) (b j)
  let lower (j : H.StageInterval first last) := -(2 * B / 3) * ((b j) ^ 3 - (a j) ^ 3)
  let upper (j : H.StageInterval first last) :=
    A + (2 * B / 3) * ((v ^ 3 - u ^ 3) - ((b j) ^ 3 - (a j) ^ 3))
  have hbound (n : ℕ) (j : H.StageInterval first last) :
      lower j ≤ action n j ∧ action n j ≤ upper j :=
    ⟨H.stageRegularizedAction_ge_of_scalar_lower_bound j.val T (alpha n j)
      (H.regularizedStage_bounds hu huv hupperIcc hpast j).2.1 (hscalar n j) (hint n j),
      H.stageRegularizedAction_le_of_sum_le hu huv hupperIcc hpast
        (alpha n) (hint n) (hscalar n) (hact n) j⟩
  obtain ⟨psi, values, hpsi, hvalues, hvaluesSum⟩ :=
    exists_finite_action_vector_limit action lower upper ell hbound haction
  let F (j : H.StageInterval first last) (n : ℕ) :
      C(Icc (a j) (b j), (H.stage j.val).Carrier) :=
    ⟨fun r => alpha (psi n) j r.val, (halpha (psi n) j).continuousOn.domRestrict⟩
  let R (j : H.StageInterval first last)
      (f : C(Icc (a j) (b j), (H.stage j.val).Carrier)) : Prop :=
    ∃ (gamma : ℝ → (H.stage j.val).Carrier) (hgamma : Continuous gamma),
      (⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩ :
        C(Icc (a j) (b j), (H.stage j.val).Carrier)) = f ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma (a j) (b j) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T gamma) volume (a j) (b j) ∧
      H.stageRegularizedAction j.val T gamma (a j) (b j) ≤ values j
  have hcoordinate (j : H.StageInterval first last) (_hj : j ∈ Finset.univ)
      (chi : ℕ → ℕ) (hchi : StrictMono chi) :
      ∃ (theta : ℕ → ℕ) (f : C(Icc (a j) (b j), (H.stage j.val).Carrier)),
        StrictMono theta ∧ R j f ∧ Tendsto (F j ∘ chi ∘ theta) atTop (𝓝 f) := by
    obtain ⟨theta, gamma, hgamma, htheta, hconv, hAC, hInt, hleAction⟩ :=
      H.exists_subsequence_stage_action_le_of_tendsto_action hle j hu huv hupper hpast
        p (upper j) B (values j) hB (fun n => alpha (psi (chi n)))
        (fun n => halpha (psi (chi n))) (fun n => hstart (psi (chi n)))
        (fun n => hnodes (psi (chi n))) (fun n => hint (psi (chi n)) j)
        (fun n => hscalar (psi (chi n)) j) (fun n => (hbound (psi (chi n)) j).2)
        ((hvalues j).comp hchi.tendsto_atTop)
    exact ⟨theta, ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩,
      htheta, ⟨gamma, hgamma, rfl, hAC, hInt, hleAction⟩, hconv⟩
  obtain ⟨chi, hchi, hlimits⟩ :=
    exists_finset_subsequence_limits Finset.univ F R hcoordinate
  choose maps hmapsR hmapsConv using fun j => hlimits j (Finset.mem_univ j)
  choose gamma hgamma hgammaEq hgammaAC hgammaInt hgammaAction using hmapsR
  let phi := psi ∘ chi
  have hconv (j : H.StageInterval first last) :
      Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (a j) (b j), (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma j r.val, (hgamma j).comp continuous_subtype_val⟩) := by
    rw [hgammaEq j]
    exact hmapsConv j
  have heval (j : H.StageInterval first last) (r : ℝ) (hr : r ∈ Icc (a j) (b j)) :
      Tendsto (fun n => alpha (phi n) j r) atTop (𝓝 (gamma j r)) :=
    (continuous_eval_const (⟨r, hr⟩ : Icc (a j) (b j))).continuousAt.tendsto.comp (hconv j)
  let jlast : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have haLast : a jlast = u := H.regularizedStageStart_eq_of_mem_Icc hu hupperIcc
  have huLast : u ∈ Icc (a jlast) (b jlast) :=
    ⟨haLast.le, haLast.symm.trans_le (H.regularizedStage_bounds hu huv hupperIcc hpast jlast).2.1⟩
  refine ⟨phi, gamma, hgamma, hpsi.comp hchi, hconv, hgammaAC, hgammaInt, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (heval jlast u huLast)
    simpa only [jlast, hstart] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p))
  · intro i hf hl
    let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    let w := Real.sqrt (T - H.time i.succ)
    have hao : a jo = w := H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl
    have hbn : b jn = w := H.regularizedStageEnd_succ_eq_event_clock hpast i hf
    have hwo : w ∈ Icc (a jo) (b jo) := by
      rw [← hao]
      exact ⟨le_rfl, (H.regularizedStage_bounds hu huv hupperIcc hpast jo).2.1⟩
    have hwn : w ∈ Icc (a jn) (b jn) := by
      rw [← hbn]
      exact ⟨(H.regularizedStage_bounds hu huv hupperIcc hpast jn).2.1, le_rfl⟩
    exact (H.event i).exists_old_of_tendsto (heval jo w hwo) (heval jn w hwn)
      (Eventually.of_forall fun n => hnodes (phi n) i hf hl)
  · calc
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤
          ∑ j, values j := Finset.sum_le_sum (fun j _ => hgammaAction j)
      _ = ell := hvaluesSum

theorem exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action
    (H : ObservedHistory.{uHistoryLimit})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (halpha : ∀ n j, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hint : ∀ n j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j))
      volume (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hstart : ∀ n, alpha n ⟨last, hle, le_rfl⟩ u = p)
    (hend : ∀ n, alpha n ⟨first, le_rfl, hle⟩ v = q)
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ n j, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ A)
    (haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
      (hgamma : ∀ j, Continuous (gamma j)),
      StrictMono phi ∧
      (∀ j, Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma j r.val, (hgamma j).comp continuous_subtype_val⟩)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ ell := by
  obtain ⟨phi, gamma, hgamma, hphi, hconv, hAC, hInt, hstart', hnodes', hact'⟩ :=
    H.exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_free_endpoint
      first last hle hu huv hupper hpast p A B ell hB alpha halpha hint hstart hnodes
      hscalar hact haction
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hbFirst : H.regularizedStageEnd T v jfirst.val = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast
  have hvFirst : v ∈ Icc (H.regularizedStageStart T u jfirst.val)
      (H.regularizedStageEnd T v jfirst.val) :=
    ⟨(H.regularizedStage_bounds hu huv hupperIcc hpast jfirst).2.1.trans_eq hbFirst, hbFirst.ge⟩
  have heval : Tendsto (fun n => alpha (phi n) jfirst v) atTop (𝓝 (gamma jfirst v)) :=
    (continuous_eval_const (⟨v, hvFirst⟩ : Icc (H.regularizedStageStart T u jfirst.val)
      (H.regularizedStageEnd T v jfirst.val))).continuousAt.tendsto.comp (hconv jfirst)
  refine ⟨phi, gamma, hgamma, hphi, hconv, hAC, hInt, hstart', ?_, hnodes', hact'⟩
  apply tendsto_nhds_unique heval
  simpa only [jfirst, hend] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end


noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uStageMinimality

theorem stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uStageMinimality})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (k : H.StageInterval first last) (beta : ℝ → (H.stage k.val).Carrier)
    (hbetaAC : Manifold.absolutelyContinuousOnInterval ThreeModel beta
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val))
    (hbetaInt : IntervalIntegrable (H.stageRegularizedLagrangian k.val T beta) volume
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val))
    (hbetaStart : beta (H.regularizedStageStart T u k.val) =
      gamma k (H.regularizedStageStart T u k.val))
    (hbetaEnd : beta (H.regularizedStageEnd T v k.val) =
      gamma k (H.regularizedStageEnd T v k.val)) :
    H.stageRegularizedAction k.val T (gamma k)
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val) ≤
    H.stageRegularizedAction k.val T beta
      (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val) := by
  classical
  let delta := Function.update gamma k beta
  have hdeltaAC (j : H.StageInterval first last) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases h : j = k
    · subst j
      simpa only [delta, Function.update_self] using hbetaAC
    · simpa only [delta, Function.update_of_ne h] using hgammaAC j
  have hdeltaInt (j : H.StageInterval first last) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases h : j = k
    · subst j
      simpa only [delta, Function.update_self] using hbetaInt
    · simpa only [delta, Function.update_of_ne h] using hgammaInt j
  have hdeltaStart (j : H.StageInterval first last) :
      delta j (H.regularizedStageStart T u j.val) =
        gamma j (H.regularizedStageStart T u j.val) := by
    by_cases h : j = k
    · subst j
      simpa only [delta, Function.update_self] using hbetaStart
    · simp only [delta, Function.update_of_ne h]
  have hdeltaEnd (j : H.StageInterval first last) :
      delta j (H.regularizedStageEnd T v j.val) =
        gamma j (H.regularizedStageEnd T v j.val) := by
    by_cases h : j = k
    · subst j
      simpa only [delta, Function.update_self] using hbetaEnd
    · simp only [delta, Function.update_of_ne h]
  have hmember : H.regularizedExtendedAction first last T B u v delta ∈
      H.regularizedActionValues first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v) := by
    refine ⟨hu, huv, hupper, hpast, delta, hdeltaAC, ?_, ?_, ?_, rfl⟩
    · simpa only [H.regularizedStageStart_eq_of_mem_Icc hu hupper] using
        hdeltaStart ⟨last, hle, le_rfl⟩
    · simpa only [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast] using
        hdeltaEnd ⟨first, le_rfl, hle⟩
    · intro i hf hl
      obtain ⟨z, hzold, hznew⟩ := hgammaNodes i hf hl
      have ho := hdeltaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      have hn := hdeltaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
      rw [H.regularizedStageStart_castSucc_eq_event_clock hupper i hl] at ho
      rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
      exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  have hsum := H.regularizedCost_le_of_competitor first last hle T B u v
    (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v) hmember
  rw [← hmin,
    H.regularizedExtendedAction_eq_sum_action first last hu huv hupper hpast gamma hgammaInt
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar j t ht (gamma j t)),
    H.regularizedExtendedAction_eq_sum_action first last hu huv hupper hpast delta hdeltaInt
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar j t ht (delta j t))] at hsum
  have hsumReal := WithTop.coe_le_coe.mp hsum
  by_contra hn
  have hstrict := lt_of_not_ge hn
  apply not_lt_of_ge hsumReal
  apply Finset.sum_lt_sum
  · intro j _
    by_cases h : j = k
    · subst j
      simpa only [delta, Function.update_self] using hstrict.le
    · simp only [delta, Function.update_of_ne h, le_refl]
  · exact ⟨k, Finset.mem_univ k, by simpa only [delta, Function.update_self] using hstrict⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryInterior

theorem contMDiffOn_stage_interior_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uHistoryInterior})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v)) :
    ∀ j : H.StageInterval first last,
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)
        (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
  have hphysical (j : H.StageInterval first last) (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
      T - r ^ 2 ∈ Ioo (H.time j.val) (H.stageEndTime j.val) :=
    H.mapsTo_regularizedStage_Ioo_Ioo T u v j.val hr
  intro j r hr
  have hflow : ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D),
      IsSolutionOn S ∧
      (∀ (alpha : ℝ → (H.stage j.val).Carrier) (s : ℝ),
        H.stageRegularizedLagrangian j.val T alpha s = lRegularizedLagrangian S T alpha s) ∧
      (∀ s ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
        T - s ^ 2 ∈ D.regular) := by
    rcases j with ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
      have hp := hphysical ⟨Fin.last H.eventCount, hk⟩ r hr
      have htime : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hp.1.trans hp.2
      refine ⟨_, (H.finalSlab htime).flow, (H.finalSlab htime).equation,
        H.stageRegularizedLagrangian_last htime T, ?_⟩
      intro s hs
      change H.time (Fin.last H.eventCount) < T - s ^ 2 ∧ T - s ^ 2 < H.horizon
      simpa only [H.stageEndTime_last, mem_Ioo] using hphysical ⟨Fin.last H.eventCount, hk⟩ s hs
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation,
        H.stageRegularizedLagrangian_castSucc i T, ?_⟩
      intro s hs
      change H.time i.castSucc < T - s ^ 2 ∧ T - s ^ 2 < H.time i.succ
      simpa only [H.stageEndTime_castSucc, mem_Ioo] using hphysical ⟨i.castSucc, hk⟩ s hs
  obtain ⟨D, S, hS, hlag, hclock⟩ := hflow
  let : TopologicalSpace.MetrizableSpace (H.stage j.val).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stage j.val).Carrier
  let : PseudoMetricSpace (H.stage j.val).Carrier :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (H.stage j.val).Carrier
  have hlagFun (alpha : ℝ → (H.stage j.val).Carrier) :
      H.stageRegularizedLagrangian j.val T alpha = lRegularizedLagrangian S T alpha :=
    funext (hlag alpha)
  have haction (alpha : ℝ → (H.stage j.val).Carrier) (c d : ℝ) :
      H.stageRegularizedAction j.val T alpha c d = lRegularizedAction S T alpha c d := by
    simp only [stageRegularizedAction, lRegularizedAction, hlagFun]
  have hgammaIntS : IntervalIntegrable (lRegularizedLagrangian S T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    simpa only [hlagFun] using hgammaInt j
  have hminS (eta : ℝ → (H.stage j.val).Carrier)
      (heta : Manifold.absolutelyContinuousOnInterval ThreeModel eta
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      (hetaInt : IntervalIntegrable (lRegularizedLagrangian S T eta) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      (hetaA : eta (H.regularizedStageStart T u j.val) = gamma j (H.regularizedStageStart T u j.val))
      (hetaB : eta (H.regularizedStageEnd T v j.val) = gamma j (H.regularizedStageEnd T v j.val)) :
      lRegularizedAction S T (gamma j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤
        lRegularizedAction S T eta (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      j eta heta (by simpa only [hlagFun] using hetaInt) hetaA hetaB
    simpa only [haction] using hh
  obtain ⟨c, hac, hcr⟩ := exists_between hr.1
  obtain ⟨d, hrd, hdb⟩ := exists_between hr.2
  have hcd := hcr.trans hrd
  have hab := hr.1.trans hr.2
  have hsub : Icc c d ⊆ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) :=
    Icc_subset_Icc hac.le hdb.le
  have hgammaSub : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j) c d :=
    Manifold.absolutelyContinuousOnInterval_mono (hgammaAC j)
    (by simpa only [uIcc_of_le hcd.le, uIcc_of_le hab.le] using hsub)
  have hintSub : IntervalIntegrable (lRegularizedLagrangian S T (gamma j)) volume c d :=
    hgammaIntS.mono_set (by simpa only [uIcc_of_le hcd.le, uIcc_of_le hab.le] using hsub)
  have hclockSub (s : ℝ) (hs : s ∈ Icc c d) : T - s ^ 2 ∈ D.regular :=
    hclock s ⟨hac.trans_le hs.1, hs.2.trans_lt hdb⟩
  have hsubmin := lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval
    S T (H.regularizedStageStart T u j.val) c d (H.regularizedStageEnd T v j.val)
    hac.le hcd.le hdb.le (gamma j) (hgammaAC j) hgammaIntS hminS
  have hc1 := lMinCurve_c1_of_absolutelyContinuousOnInterval S hS T c d hcd
    (gamma j) hgammaSub hintSub hclockSub (fun delta hdelta hda hdd =>
      hsubmin delta (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hdelta.contMDiffOn)
        (intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
          S hS.smoothMetric ⟨hS.scalarCont⟩ T c d hcd.le delta hdelta.contMDiffOn hclockSub) hda hdd)
  exact (hc1.contMDiffAt (Icc_mem_nhds hcr hrd)).contMDiffWithinAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uTwoStageMinimality

theorem stageRegularizedAction_add_le_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uTwoStageMinimality})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (betaOld : ℝ → (H.stage i.castSucc).Carrier)
    (betaNew : ℝ → (H.stage i.succ).Carrier)
    (hbetaOldAC : Manifold.absolutelyContinuousOnInterval ThreeModel betaOld
      (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc))
    (hbetaNewAC : Manifold.absolutelyContinuousOnInterval ThreeModel betaNew
      (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ))
    (hbetaOldInt : IntervalIntegrable (H.stageRegularizedLagrangian i.castSucc T betaOld) volume
      (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc))
    (hbetaNewInt : IntervalIntegrable (H.stageRegularizedLagrangian i.succ T betaNew) volume
      (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ))
    (hbetaOldEnd : betaOld (H.regularizedStageEnd T v i.castSucc) =
      gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
        (H.regularizedStageEnd T v i.castSucc))
    (hbetaNewStart : betaNew (H.regularizedStageStart T u i.succ) =
      gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (H.regularizedStageStart T u i.succ))
    (hbetaNode : ∃ z : (H.event i).old,
      z.val.val = betaOld (Real.sqrt (T - H.time i.succ)) ∧
      (H.event i).oldOutput z = betaNew (Real.sqrt (T - H.time i.succ))) :
    H.stageRegularizedAction i.castSucc T
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) +
      H.stageRegularizedAction i.succ T
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ) ≤
    H.stageRegularizedAction i.castSucc T betaOld
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) +
      H.stageRegularizedAction i.succ T betaNew
        (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ) := by
  classical
  let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  have hne : jo ≠ jn := fun h => i.castSucc_lt_succ.ne (congrArg Subtype.val h)
  let delta := Function.update (Function.update gamma jo betaOld) jn betaNew
  have hdeltaOld : delta jo = betaOld := by
    simp only [delta, Function.update_of_ne hne, Function.update_self]
  have hdeltaNew : delta jn = betaNew := by
    simp only [delta, Function.update_self]
  have hdeltaEq (j : H.StageInterval first last) (hjo : j ≠ jo) (hjn : j ≠ jn) :
      delta j = gamma j := by
    simp only [delta, Function.update_of_ne hjn, Function.update_of_ne hjo]
  have hdeltaAC (j : H.StageInterval first last) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases hjo : j = jo
    · subst j
      rw [hdeltaOld]
      exact hbetaOldAC
    · by_cases hjn : j = jn
      · subst j
        rw [hdeltaNew]
        exact hbetaNewAC
      · rw [hdeltaEq j hjo hjn]
        exact hgammaAC j
  have hdeltaInt (j : H.StageInterval first last) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases hjo : j = jo
    · subst j
      rw [hdeltaOld]
      exact hbetaOldInt
    · by_cases hjn : j = jn
      · subst j
        rw [hdeltaNew]
        exact hbetaNewInt
      · rw [hdeltaEq j hjo hjn]
        exact hgammaInt j
  have hdeltaStart (j : H.StageInterval first last) (hjo : j ≠ jo) :
      delta j (H.regularizedStageStart T u j.val) =
        gamma j (H.regularizedStageStart T u j.val) := by
    by_cases hjn : j = jn
    · subst j
      rw [hdeltaNew]
      exact hbetaNewStart
    · rw [hdeltaEq j hjo hjn]
  have hdeltaEnd (j : H.StageInterval first last) (hjn : j ≠ jn) :
      delta j (H.regularizedStageEnd T v j.val) =
        gamma j (H.regularizedStageEnd T v j.val) := by
    by_cases hjo : j = jo
    · subst j
      rw [hdeltaOld]
      exact hbetaOldEnd
    · rw [hdeltaEq j hjo hjn]
  have hmember : H.regularizedExtendedAction first last T B u v delta ∈
      H.regularizedActionValues first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v) := by
    refine ⟨hu, huv, hupper, hpast, delta, hdeltaAC, ?_, ?_, ?_, rfl⟩
    · have hlast : (⟨last, hle, le_rfl⟩ : H.StageInterval first last) ≠ jo := by
        intro h
        exact (i.castSucc_lt_succ.trans_le hl).ne (congrArg Subtype.val h).symm
      simpa only [H.regularizedStageStart_eq_of_mem_Icc hu hupper] using
        hdeltaStart ⟨last, hle, le_rfl⟩ hlast
    · have hfirst : (⟨first, le_rfl, hle⟩ : H.StageInterval first last) ≠ jn := by
        intro h
        exact (hf.trans_lt i.castSucc_lt_succ).ne (congrArg Subtype.val h)
      simpa only [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast] using
        hdeltaEnd ⟨first, le_rfl, hle⟩ hfirst
    · intro k hkf hkl
      by_cases hki : k = i
      · subst k
        obtain ⟨z, hzo, hzn⟩ := hbetaNode
        exact ⟨z, hzo.trans (congrFun hdeltaOld _).symm,
          hzn.trans (congrFun hdeltaNew _).symm⟩
      · have hko : (⟨k.castSucc, hkf, k.castSucc_lt_succ.le.trans hkl⟩ :
            H.StageInterval first last) ≠ jo := by
          intro h
          exact hki (Fin.ext (congrArg (fun j : H.StageInterval first last => j.val.val) h))
        have hkn : (⟨k.succ, hkf.trans k.castSucc_lt_succ.le, hkl⟩ :
            H.StageInterval first last) ≠ jn := by
          intro h
          apply hki
          apply Fin.ext
          have he := congrArg (fun j : H.StageInterval first last => j.val.val) h
          exact Nat.add_right_cancel he
        obtain ⟨z, hzo, hzn⟩ := hgammaNodes k hkf hkl
        have ho := hdeltaStart ⟨k.castSucc, hkf, k.castSucc_lt_succ.le.trans hkl⟩ hko
        have hn := hdeltaEnd ⟨k.succ, hkf.trans k.castSucc_lt_succ.le, hkl⟩ hkn
        rw [H.regularizedStageStart_castSucc_eq_event_clock hupper k hkl] at ho
        rw [H.regularizedStageEnd_succ_eq_event_clock hpast k hkf] at hn
        exact ⟨z, hzo.trans ho.symm, hzn.trans hn.symm⟩
  have hsum := H.regularizedCost_le_of_competitor first last hle T B u v
    (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v) hmember
  rw [← hmin,
    H.regularizedExtendedAction_eq_sum_action first last hu huv hupper hpast gamma hgammaInt
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar j t ht (gamma j t)),
    H.regularizedExtendedAction_eq_sum_action first last hu huv hupper hpast delta hdeltaInt
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hscalar j t ht (delta j t))] at hsum
  have hsumReal := WithTop.coe_le_coe.mp hsum
  let ag (j : H.StageInterval first last) := H.stageRegularizedAction j.val T (gamma j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  let ad (j : H.StageInterval first last) := H.stageRegularizedAction j.val T (delta j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  change (∑ j, ag j) ≤ ∑ j, ad j at hsumReal
  have hcompl : ∑ j ∈ ({jo, jn} : Finset (H.StageInterval first last))ᶜ, ad j =
      ∑ j ∈ ({jo, jn} : Finset (H.StageInterval first last))ᶜ, ag j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hh : j ≠ jo ∧ j ≠ jn := by simpa only [Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton, not_or] using hj
    simp only [ad, ag, hdeltaEq j hh.1 hh.2]
  rw [← Finset.sum_add_sum_compl {jo, jn} ag,
    ← Finset.sum_add_sum_compl {jo, jn} ad, Finset.sum_pair hne, Finset.sum_pair hne,
    hcompl, add_le_add_iff_right] at hsumReal
  simpa only [ag, ad, hdeltaOld, hdeltaNew, jo, jn] using hsumReal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter Function Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uIncomingGeodesic

theorem regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uIncomingGeodesic})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.castSucc ≤ last) :
    IsLRegularizedGeodesicOn (H.event i).incoming.flow T
      (gamma ⟨i.castSucc, hf, hl⟩)
      (Ioo (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)) := by
  let j : H.StageInterval first last := ⟨i.castSucc, hf, hl⟩
  let S := (H.event i).incoming.flow
  let : TopologicalSpace.MetrizableSpace (H.stage i.castSucc).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stage i.castSucc).Carrier
  have hlag (eta : ℝ → (H.stage i.castSucc).Carrier) :
      H.stageRegularizedLagrangian i.castSucc T eta = lRegularizedLagrangian S T eta :=
    funext (H.stageRegularizedLagrangian_castSucc i T eta)
  have haction (eta : ℝ → (H.stage i.castSucc).Carrier) (c d : ℝ) :
      H.stageRegularizedAction i.castSucc T eta c d = lRegularizedAction S T eta c d := by
    simp only [stageRegularizedAction, lRegularizedAction, hlag]
  apply lMinCurve_regularizedGeodesicOn_of_absolutelyContinuousOnInterval_of_minimal
    S (H.event i).incoming.equation T
    (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)
    (gamma j) (hgammaAC j) (by simpa only [j, hlag] using hgammaInt j)
  · intro r hr
    change H.time i.castSucc < T - r ^ 2 ∧ T - r ^ 2 < H.time i.succ
    simpa only [H.stageEndTime_castSucc, mem_Ioo] using
      H.mapsTo_regularizedStage_Ioo_Ioo T u v i.castSucc hr
  · intro eta heta hetaInt hetaA hetaB
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      j eta heta (by simpa only [j, hlag] using hetaInt) hetaA hetaB
    simpa only [j, haction] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uFinalGeodesic

theorem regularizedGeodesicOn_final_stage_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uFinalGeodesic}) (first : Fin (H.eventCount + 1))
    (hfinal : H.time (Fin.last H.eventCount) < H.horizon)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first (Fin.last H.eventCount),
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first (Fin.last H.eventCount)) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, Fin.le_last _⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, Fin.le_last _⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first (Fin.last H.eventCount) T B u v gamma =
      H.regularizedCost first (Fin.last H.eventCount) (Fin.le_last first) T B u v
        (gamma ⟨Fin.last H.eventCount, Fin.le_last first, le_rfl⟩ u)
        (gamma ⟨first, le_rfl, Fin.le_last first⟩ v)) :
    IsLRegularizedGeodesicOn (H.finalSlab hfinal).flow T
      (gamma ⟨Fin.last H.eventCount, Fin.le_last first, le_rfl⟩)
      (Ioo (H.regularizedStageStart T u (Fin.last H.eventCount))
        (H.regularizedStageEnd T v (Fin.last H.eventCount))) := by
  let j : H.StageInterval first (Fin.last H.eventCount) :=
    ⟨Fin.last H.eventCount, Fin.le_last first, le_rfl⟩
  let S := (H.finalSlab hfinal).flow
  let : TopologicalSpace.MetrizableSpace (H.stage (Fin.last H.eventCount)).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
  have hlag (eta : ℝ → (H.stage (Fin.last H.eventCount)).Carrier) :
      H.stageRegularizedLagrangian (Fin.last H.eventCount) T eta =
        lRegularizedLagrangian S T eta :=
    funext (H.stageRegularizedLagrangian_last hfinal T eta)
  have haction (eta : ℝ → (H.stage (Fin.last H.eventCount)).Carrier) (c d : ℝ) :
      H.stageRegularizedAction (Fin.last H.eventCount) T eta c d =
        lRegularizedAction S T eta c d := by
    simp only [stageRegularizedAction, lRegularizedAction, hlag]
  apply lMinCurve_regularizedGeodesicOn_of_absolutelyContinuousOnInterval_of_minimal
    S (H.finalSlab hfinal).equation T
    (H.regularizedStageStart T u (Fin.last H.eventCount))
    (H.regularizedStageEnd T v (Fin.last H.eventCount))
    (gamma j) (hgammaAC j) (by simpa only [j, hlag] using hgammaInt j)
  · intro r hr
    change H.time (Fin.last H.eventCount) < T - r ^ 2 ∧ T - r ^ 2 < H.horizon
    simpa only [H.stageEndTime_last, mem_Ioo] using
      H.mapsTo_regularizedStage_Ioo_Ioo T u v (Fin.last H.eventCount) hr
  · intro eta heta hetaInt hetaA hetaB
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
      first (Fin.last H.eventCount) (Fin.le_last first) hu huv
      (by simpa only [H.stageEndTime_last] using hupper) hpast hscalar gamma hgammaAC hgammaInt
      (fun i hf _ => hgammaNodes i hf) hmin
      j eta heta (by simpa only [j, hlag] using hetaInt) hetaA hetaB
    simpa only [j, haction] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryEndpoint

theorem exists_contMDiffOn_stage_terminal_collar_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uHistoryEndpoint})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.castSucc ≤ last)
    (hreach : H.time i.succ ≤ T - u ^ 2)
    (hterminal : gamma ⟨i.castSucc, hf, hl⟩ (Real.sqrt (T - H.time i.succ)) ∈
      (H.event i).incoming.terminalRegularOpen) :
    ∃ d ∈ Ioo (Real.sqrt (T - H.time i.succ)) (H.regularizedStageEnd T v i.castSucc),
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (gamma ⟨i.castSucc, hf, hl⟩)
        (Icc (Real.sqrt (T - H.time i.succ)) d) := by
  let j : H.StageInterval first last := ⟨i.castSucc, hf, hl⟩
  have hstart : H.regularizedStageStart T u i.castSucc =
      Real.sqrt (T - H.time i.succ) := by
    simp only [regularizedStageStart, H.stageEndTime_castSucc, min_eq_right hreach]
  have hclocks := H.regularizedStage_endpoint_clocks hupper huv hu j
  have hterminalClock : T - (H.regularizedStageStart T u i.castSucc) ^ 2 = H.time i.succ := by
    rw [hclocks.1, H.stageEndTime_castSucc, min_eq_right hreach]
  have hpastlt : T - v ^ 2 < H.time i.succ := by
    let tPast : Icc (0 : ℝ) H.horizon := ⟨T - v ^ 2, H.stageDomain_subset first hpast⟩
    have hactive : H.activeStage tPast = first := (H.mem_stageDomain_iff tPast first).mp hpast
    by_contra hn
    have hif : i.succ ≤ first := by
      simpa only [hactive] using H.le_activeStage tPast i.succ (not_lt.mp hn)
    exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hif
  have hmaxlt : max (T - v ^ 2) (H.time i.castSucc) < H.time i.succ :=
    max_lt hpastlt (H.time_strictMono i.castSucc_lt_succ)
  have hstart0 : 0 ≤ H.regularizedStageStart T u i.castSucc := Real.sqrt_nonneg _
  have hend0 : 0 ≤ H.regularizedStageEnd T v i.castSucc := Real.sqrt_nonneg _
  have hstrict : H.regularizedStageStart T u i.castSucc <
      H.regularizedStageEnd T v i.castSucc := by
    by_contra hn
    have hsq := (sq_le_sq₀ hend0 hstart0).mpr (not_lt.mp hn)
    nlinarith only [hterminalClock, hclocks.2, hmaxlt, hsq]
  have hphysicalPast : H.time i.castSucc ≤ T - (H.regularizedStageEnd T v i.castSucc) ^ 2 := by
    rw [hclocks.2]
    exact le_max_right _ _
  have hlag (alpha : ℝ → (H.stage i.castSucc).Carrier) :
      H.stageRegularizedLagrangian i.castSucc T alpha =
        lRegularizedLagrangian (H.event i).incoming.flow T alpha :=
    funext (H.stageRegularizedLagrangian_castSucc i T alpha)
  have hint : IntervalIntegrable
      (lRegularizedLagrangian (H.event i).incoming.flow T (gamma j)) volume
      (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) := by
    simpa only [j, hlag] using hgammaInt j
  have hminimum (beta : ℝ → (H.stage i.castSucc).Carrier)
      (hbeta : Manifold.absolutelyContinuousOnInterval ThreeModel beta
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc))
      (hbetaInt : IntervalIntegrable (lRegularizedLagrangian (H.event i).incoming.flow T beta) volume
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc))
      (hbetaStart : beta (H.regularizedStageStart T u i.castSucc) =
        gamma j (H.regularizedStageStart T u i.castSucc))
      (hbetaEnd : beta (H.regularizedStageEnd T v i.castSucc) =
        gamma j (H.regularizedStageEnd T v i.castSucc)) :
      lRegularizedAction (H.event i).incoming.flow T (gamma j)
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) ≤
      lRegularizedAction (H.event i).incoming.flow T beta
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) := by
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      j beta hbeta (by simpa only [j, hlag] using hbetaInt) hbetaStart hbetaEnd
    simpa only [j, H.stageRegularizedAction_castSucc] using hh
  obtain ⟨d, hd, hc1⟩ := (H.event i).terminal.exists_contMDiffOn_one_collar_of_action_minimal
    hstart0 hstrict hterminalClock hphysicalPast (hgammaAC j) hint
    (by simpa only [j, hstart] using hterminal) hminimum
  exact ⟨d, by simpa only [hstart] using hd, by simpa only [j, hstart] using hc1⟩

theorem exists_contMDiffOn_event_incoming_collar_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uHistoryEndpoint})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    ∃ d ∈ Ioo (Real.sqrt (T - H.time i.succ)) (H.regularizedStageEnd T v i.castSucc),
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (Icc (Real.sqrt (T - H.time i.succ)) d) := by
  have hreach : H.time i.succ ≤ T - u ^ 2 :=
    (H.time_strictMono.monotone hl).trans hupper.1
  have hterminal : gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      (Real.sqrt (T - H.time i.succ)) ∈ (H.event i).incoming.terminalRegularOpen := by
    obtain ⟨z, hz, _⟩ := hgammaNodes i hf hl
    rw [← hz, ← (H.event i).oldTerminal_eq z]
    exact ((H.event i).oldTerminal z).property
  exact H.exists_contMDiffOn_stage_terminal_collar_of_regularizedExtendedAction_eq_regularizedCost
    first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
    i hf (i.castSucc_lt_succ.le.trans hl) hreach hterminal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uNodeNeighborhood

private theorem exists_survivor_neighborhood_of_regularCrossing
    (H : ObservedHistory.{uNodeNeighborhood}) (i : Fin H.eventCount)
    {T u v : ℝ} (hu : 0 ≤ u)
    (huw : u < Real.sqrt (T - H.time i.succ))
    (hwv : Real.sqrt (T - H.time i.succ) < v)
    (horizon : T - u ^ 2 ≤ H.horizon)
    (betaOld : ℝ → (H.stage i.castSucc).Carrier)
    (betaNew : ℝ → (H.stage i.succ).Carrier)
    (hOld : ContinuousOn betaOld
      (Icc (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)))
    (hNew : ContinuousOn betaNew
      (Icc (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ)))
    (hcross : (H.event i).RegularCrossing
      (betaOld (Real.sqrt (T - H.time i.succ)))
      (betaNew (Real.sqrt (T - H.time i.succ)))) :
    ∃ G : (H.stage i.succ).IncomingSlab (H.time i.succ) (H.stageEndTime i.succ),
      (∀ t, G.flow.base.metric t = H.stageMetric i.succ t) ∧
    ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
      (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
      (F : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W)
        (RealTimeInterval.closed C D (hCs.trans hsD).le))
      (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
      (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
      H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧
      Injective (fun z : W => z.val.val) ∧ Injective (fun z : W => F z.val) ∧
      IsSolutionOn S ∧
      (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
      (∃ z : W, z.val.val = betaOld (Real.sqrt (T - H.time i.succ)) ∧
        F z.val = betaNew (Real.sqrt (T - H.time i.succ))) ∧
      (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
        localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hf) ∧
      (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
        localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hg) ∧
      S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
      ∃ c d : ℝ, u < c ∧ c < Real.sqrt (T - H.time i.succ) ∧
        Real.sqrt (T - H.time i.succ) < d ∧ d < v ∧
        H.regularizedStageStart T u i.succ < c ∧
        d < H.regularizedStageEnd T v i.castSucc ∧
        MapsTo betaNew (Icc c (Real.sqrt (T - H.time i.succ)))
          (range (fun z : W => F z.val)) ∧
        MapsTo betaOld (Icc (Real.sqrt (T - H.time i.succ)) d)
          (range (fun z : W => z.val.val)) ∧
        ∀ r ∈ Icc c d, T - r ^ 2 ∈ Ioo C D := by
  let w := Real.sqrt (T - H.time i.succ)
  have hw : 0 < w := hu.trans_lt huw
  have hTs : 0 < T - H.time i.succ := Real.sqrt_pos.mp hw
  have hwclock : T - w ^ 2 = H.time i.succ := by
    rw [show w ^ 2 = T - H.time i.succ from Real.sq_sqrt hTs.le]
    ring
  have hsupper : H.time i.succ < T - u ^ 2 := by
    have hh := (sq_lt_sq₀ hu hw.le).mpr huw
    linarith only [hh, hwclock]
  have hlower : T - v ^ 2 < H.time i.succ := by
    have hh := (sq_lt_sq₀ hw.le (hw.le.trans hwv.le)).mpr hwv
    linarith only [hh, hwclock]
  have hsb : H.time i.succ < H.stageEndTime i.succ := by
    cases heq : i.succ using Fin.lastCases with
    | last => simpa only [heq, H.stageEndTime_last] using hsupper.trans_le horizon
    | cast j => simpa only [heq, H.stageEndTime_castSucc] using H.time_strictMono j.castSucc_lt_succ
  have hout (j : Fin (H.eventCount + 1)) (hj : H.time j < H.stageEndTime j) :
      ∃ G : (H.stage j).IncomingSlab (H.time j) (H.stageEndTime j),
        ∀ t, G.flow.base.metric t = H.stageMetric j t := by
    cases j using Fin.lastCases with
    | last =>
      rw [H.stageEndTime_last]
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hj
      let G := (H.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
      refine ⟨G, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      rfl
    | cast j =>
      rw [H.stageEndTime_castSucc]
      refine ⟨(H.event j).incoming, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_castSucc]
  obtain ⟨G, hGmetric⟩ := hout i.succ hsb
  have hmetric : G.flow.base.metric (H.time i.succ) = (H.event i).outputMetric :=
    (hGmetric _).trans ((H.stageMetric_initial i.succ).trans (H.event_output i).symm)
  have hOldStart : H.regularizedStageStart T u i.castSucc = w := by
    simp only [regularizedStageStart, H.stageEndTime_castSucc, min_eq_right hsupper.le, w]
  have hNewEnd : H.regularizedStageEnd T v i.succ = w := by
    simp only [regularizedStageEnd, max_eq_right hlower.le, w]
  have hNewStrict : H.regularizedStageStart T u i.succ < w := by
    have hm : H.time i.succ < min (T - u ^ 2) (H.stageEndTime i.succ) :=
      lt_min hsupper hsb
    apply Real.sqrt_lt_sqrt
    · have hh := min_le_left (T - u ^ 2) (H.stageEndTime i.succ)
      linarith [sq_nonneg u]
    · linarith only [hm]
  have hOldStrict : w < H.regularizedStageEnd T v i.castSucc := by
    have hm : max (T - v ^ 2) (H.time i.castSucc) < H.time i.succ :=
      max_lt hlower (H.time_strictMono i.castSucc_lt_succ)
    exact Real.sqrt_lt_sqrt hTs.le (by linarith only [hm])
  have hOldCont : ContinuousOn betaOld (Icc w (H.regularizedStageEnd T v i.castSucc)) := by
    simpa only [hOldStart] using hOld
  have hNewCont : ContinuousOn betaNew (Icc (H.regularizedStageStart T u i.succ) w) := by
    simpa only [hNewEnd] using hNew
  let p : (H.event i).incoming.terminalRegularOpen :=
    ⟨betaOld w, hcross.mem_terminalRegularRegion (H.event i)⟩
  obtain ⟨F₀, hsource₀, hp₀, _, _, _, _⟩ :=
    hcross.exists_survivor_partialDiffeomorph (H.event i) (p := p)
  let W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨F₀.source, F₀.open_source⟩
  let x₀ : W := ⟨p, hp₀⟩
  have hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' (H.event i).old) := by
    intro x hx
    change x ∈ F₀.source at hx
    simpa only [hsource₀, mem_ofPred_eq] using hx
  obtain ⟨C, haC, hCs⟩ := exists_between (H.time_strictMono i.castSucc_lt_succ)
  obtain ⟨D, hsD, hDb⟩ := exists_between hsb
  let : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.event i).incoming.terminalRegularOpen.isOpen)
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  obtain ⟨F, Splus, hsource, _, hFcross, hstart, hpull, _, hS, _, _⟩ :=
    (H.event i).exists_survivor_solution_across_event G hmetric W x₀ hW
      haC.le hCs hsD hDb
  let S : SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed C D (hCs.trans hsD).le) :=
    { base.metric := fun t => if t ≤ H.time i.succ then
        ((H.event i).terminal.extendedMetric t).restrictOpen W else Splus.base.metric t }
  let f : W → (H.stage i.castSucc).Carrier := fun z => z.val.val
  let g : W → (H.stage i.succ).Carrier := fun z => F z.val
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_subtype_val (H.event i).incoming.terminalRegularOpen)
      (isLocalDiffeomorph_subtype_val W)
  have hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g := by
    intro z
    have hFz : IsLocalDiffeomorphAt ThreeModel ThreeModel ∞ F z.val :=
      ⟨F, (hsource ▸ z.property), fun _ _ => rfl⟩
    exact (isLocalDiffeomorph_subtype_val W z).comp ThreeModel _ hFz
  have hfi : Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hgi : Injective g := by
    intro z y heq
    apply Subtype.ext
    exact F.toPartialEquiv.injOn (hsource ▸ z.property) (hsource ▸ y.property) heq
  have hcrossW (z : W) : (H.event i).RegularCrossing (f z) (g z) :=
    hFcross z.val z.property
  have hxOld : f x₀ = betaOld w := rfl
  have hxNew : g x₀ = betaNew w :=
    (H.event i).regularCrossing_right_unique (hcrossW x₀) hcross
  have hleft (t : ℝ) (ht : t ≤ H.time i.succ) :
      S.base.metric t = ((H.event i).terminal.extendedMetric t).restrictOpen W := ite_eq_left ht
  have hright (t : ℝ) (ht : H.time i.succ < t) :
      S.base.metric t = Splus.base.metric t := ite_eq_right (not_le.mpr ht)
  have hterminal : S.base.metric (H.time i.succ) =
      (H.event i).terminal.metric.restrictOpen W := by
    rw [hleft _ le_rfl,
      OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
  have hpullNew (t : ℝ) : Splus.base.metric t = localPullMetric (H.stageMetric i.succ t) g hg := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v₁ v₂
    rw [localPullMetric_inner, ← hGmetric, hpull]
    have hd := DifferentialGeometry.mfderiv_restrict_open
      (I := ThreeModel) (J := ThreeModel)
      (F : (H.event i).incoming.terminalRegularOpen → (H.stage i.succ).Carrier) W z
    change mfderiv ThreeModel ThreeModel g z = mfderiv ThreeModel ThreeModel F z.val at hd
    rw [hd]
    rfl
  refine ⟨G, hGmetric, C, D, hCs, hsD, W, F, S, hf, hg, haC, hDb, hsource,
    hfi, hgi, hS, hcrossW, ⟨x₀, hxOld, hxNew⟩, ?_, ?_, hterminal, ?_⟩
  · intro t ht
    rw [hleft t ht.2.le,
      OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_before _ ht.2]
    apply SmoothRiemannianMetric.ext_inner
    intro z v₁ v₂
    rw [localPullMetric_inner]
    have hd : mfderiv ThreeModel ThreeModel f z = ContinuousLinearMap.id ℝ ThreeSpace := by
      have hh := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
        (Subtype.val : W → (H.event i).incoming.terminalRegularOpen) z
      exact hh.trans (DifferentialGeometry.mfderiv_subtype_val W z)
    rw [hd]
    simp only [stageMetric, Fin.lastCases_castSucc]
    rfl
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hst
    · rw [hterminal, ← hstart]
      exact hpullNew _
    · rw [hright t hst]
      exact hpullNew t
  · let V : Set ℝ := {r | T - r ^ 2 ∈ Ioo C D}
    have hV : V ∈ 𝓝 w :=
      (continuous_const.sub (continuous_id.pow 2)).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by change C < T - w ^ 2 ∧ T - w ^ 2 < D; rw [hwclock]; exact ⟨hCs, hsD⟩))
    have hOldN : betaOld ⁻¹' range f ∈ 𝓝[≥] w := by
      have hmem := hOldCont w ⟨le_rfl, hOldStrict.le⟩
        (hf.isOpen_range.mem_nhds ⟨x₀, hxOld⟩)
      rwa [nhdsWithin_Icc_eq_nhdsGE hOldStrict] at hmem
    have hNewN : betaNew ⁻¹' range g ∈ 𝓝[≤] w := by
      have hmem := hNewCont w ⟨hNewStrict.le, le_rfl⟩
        (hg.isOpen_range.mem_nhds ⟨x₀, hxNew⟩)
      rwa [nhdsWithin_Icc_eq_nhdsLE hNewStrict] at hmem
    obtain ⟨d, hwd, hd⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
      (inter_mem hOldN (inter_mem
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hOldStrict))
        (inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hwv))
          (mem_nhdsWithin_of_mem_nhds hV))))
    obtain ⟨c, hcw, hc⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp
      (inter_mem hNewN (inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hNewStrict))
        (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds huw))
          (mem_nhdsWithin_of_mem_nhds hV))))
    have hdc := hd ⟨hwd.le, le_rfl⟩
    have hcc := hc ⟨le_rfl, hcw.le⟩
    refine ⟨c, d, hcc.2.2.1, hcw, hwd, hdc.2.2.1, hcc.2.1, hdc.2.1,
      (fun _ hr => (hc hr).1), (fun _ hr => (hd hr).1), ?_⟩
    intro r hr
    rcases le_total r w with hrw | hwr
    · exact (hc ⟨hr.1, hrw⟩).2.2.2
    · exact (hd ⟨hwr, hr.2⟩).2.2.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryNodeRegularity

theorem exists_regularizedGeodesic_survivor_lift_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uHistoryNodeRegularity})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (huw : u < Real.sqrt (T - H.time i.succ))
    (hwv : Real.sqrt (T - H.time i.succ) < v)
    (hcross : (H.event i).RegularCrossing
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
        (Real.sqrt (T - H.time i.succ)))
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (T - H.time i.succ)))) :
    ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
      (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
      (F : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W)
        (RealTimeInterval.closed C D (hCs.trans hsD).le))
      (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
      (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
      H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧
      IsSolutionOn S ∧
      (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
      (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
        localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld) ∧
      (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
        localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew) ∧
      S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
      ∃ c d : ℝ, u < c ∧ c < Real.sqrt (T - H.time i.succ) ∧
        Real.sqrt (T - H.time i.succ) < d ∧ d < v ∧
        H.regularizedStageStart T u i.succ < c ∧
        d < H.regularizedStageEnd T v i.castSucc ∧
        (∀ r ∈ Icc c d, T - r ^ 2 ∈ Ioo C D) ∧
        ∃ eta : ℝ → W,
          Manifold.absolutelyContinuousOnInterval ThreeModel eta c d ∧
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 eta (Icc c d) ∧
          IsLRegularizedGeodesicOn S T eta (Ioo c d) ∧
          EqOn ((fun z : W => F z.val) ∘ eta)
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
            (Icc c (Real.sqrt (T - H.time i.succ))) ∧
          EqOn ((fun z : W => z.val.val) ∘ eta)
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
            (Icc (Real.sqrt (T - H.time i.succ)) d) ∧
          IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d ∧
          lRegularizedAction S T eta c d =
            H.stageRegularizedAction i.succ T
              (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
              c (Real.sqrt (T - H.time i.succ)) +
            H.stageRegularizedAction i.castSucc T
              (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
              (Real.sqrt (T - H.time i.succ)) d := by
  let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  let beta := gamma jo
  let alpha := gamma jn
  let w := Real.sqrt (T - H.time i.succ)
  have hw : 0 < w := hu.trans_lt huw
  have huv : u ≤ v := huw.le.trans hwv.le
  have hwclock : T - w ^ 2 = H.time i.succ := by
    rw [show w ^ 2 = T - H.time i.succ from Real.sq_sqrt (Real.sqrt_pos.mp hw).le]
    ring
  have hsupper : H.time i.succ < T - u ^ 2 := by
    have hh := (sq_lt_sq₀ hu hw.le).mpr huw
    linarith only [hh, hwclock]
  have hlower : T - v ^ 2 < H.time i.succ := by
    have hh := (sq_lt_sq₀ hw.le (hw.le.trans hwv.le)).mpr hwv
    linarith only [hh, hwclock]
  have hOldStart : H.regularizedStageStart T u i.castSucc = w := by
    simp only [regularizedStageStart, H.stageEndTime_castSucc, min_eq_right hsupper.le, w]
  have hNewEnd : H.regularizedStageEnd T v i.succ = w := by
    simp only [regularizedStageEnd, max_eq_right hlower.le, w]
  obtain ⟨G, hGmetric, C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew,
      haC, hDb, hsource, hfi, _, hS, hcrossW, _, hpullOld, hpullNew, hterminal,
      c, d, huc, hcw, hwd, hdv, hnc, hdo, hnewStay, holdStay, hclock⟩ :=
    exists_survivor_neighborhood_of_regularCrossing H i hu huw hwv
      (hupper.2.trans (H.stageEndTime_le_horizon last)) beta alpha
      ((hgammaAC jo).1.mono Icc_subset_uIcc) ((hgammaAC jn).1.mono Icc_subset_uIcc) hcross
  change c < w at hcw
  change w < d at hwd
  let f : W → (H.stage i.castSucc).Carrier := fun z => z.val.val
  let g : W → (H.stage i.succ).Carrier := fun z => F z.val
  have hACOld : Manifold.absolutelyContinuousOnInterval ThreeModel beta w
      (H.regularizedStageEnd T v i.castSucc) := by
    have hh := hgammaAC jo
    change Manifold.absolutelyContinuousOnInterval ThreeModel beta
      (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) at hh
    rwa [hOldStart] at hh
  have hACNew : Manifold.absolutelyContinuousOnInterval ThreeModel alpha
      (H.regularizedStageStart T u i.succ) w := by
    have hh := hgammaAC jn
    change Manifold.absolutelyContinuousOnInterval ThreeModel alpha
      (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ) at hh
    rwa [hNewEnd] at hh
  have hlagOld (zeta : ℝ → (H.stage i.castSucc).Carrier) :
      H.stageRegularizedLagrangian i.castSucc T zeta =
        lRegularizedLagrangian (H.event i).incoming.flow T zeta :=
    funext (H.stageRegularizedLagrangian_castSucc i T zeta)
  have hlagNew (zeta : ℝ → (H.stage i.succ).Carrier) :
      H.stageRegularizedLagrangian i.succ T zeta = lRegularizedLagrangian G.flow T zeta := by
    funext r
    unfold stageRegularizedLagrangian lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
    rw [hGmetric]
  have hactNew (zeta : ℝ → (H.stage i.succ).Carrier) (x y : ℝ) :
      H.stageRegularizedAction i.succ T zeta x y = lRegularizedAction G.flow T zeta x y := by
    unfold stageRegularizedAction lRegularizedAction
    rw [hlagNew]
  have hintOld : IntervalIntegrable (lRegularizedLagrangian (H.event i).incoming.flow T beta)
      volume w (H.regularizedStageEnd T v i.castSucc) := by
    have hh := hgammaInt jo
    change IntervalIntegrable (H.stageRegularizedLagrangian i.castSucc T beta) volume
      (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) at hh
    simpa only [hOldStart, hlagOld] using hh
  have hintNew : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha)
      volume (H.regularizedStageStart T u i.succ) w := by
    have hh := hgammaInt jn
    change IntervalIntegrable (H.stageRegularizedLagrangian i.succ T alpha) volume
      (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ) at hh
    simpa only [hNewEnd, hlagNew] using hh
  have hbefore (r : ℝ) (hr : r ∈ Ioo w d) : S.base.metric (T - r ^ 2) =
      localPullMetric ((H.event i).incoming.flow.base.metric (T - r ^ 2)) f hlocalOld := by
    have hphys := hclock r ⟨hcw.le.trans hr.1.le, hr.2.le⟩
    have hrs : T - r ^ 2 < H.time i.succ := by
      have hh := (sq_lt_sq₀ hw.le (hw.le.trans hr.1.le)).mpr hr.1
      linarith only [hh, hwclock]
    have hh := hpullOld (T - r ^ 2) ⟨hphys.1.le, hrs⟩
    simpa only [stageMetric, Fin.lastCases_castSucc] using hh
  have hafter (r : ℝ) (hr : r ∈ Ioo c w) : S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hlocalNew := by
    have hphys := hclock r ⟨hr.1.le, hr.2.le.trans hwd.le⟩
    have hrs : H.time i.succ < T - r ^ 2 := by
      have hh := (sq_lt_sq₀ (hu.trans (huc.le.trans hr.1.le)) hw.le).mpr hr.2
      linarith only [hh, hwclock]
    have hh := hpullNew (T - r ^ 2) ⟨hrs.le, hphys.2.le⟩
    simpa only [hGmetric] using hh
  have hACNewSub : Manifold.absolutelyContinuousOnInterval ThreeModel alpha c w :=
    Manifold.absolutelyContinuousOnInterval_mono hACNew (by
      simpa only [uIcc_of_le hcw.le, uIcc_of_le (hnc.le.trans hcw.le)] using
        Icc_subset_Icc hnc.le le_rfl)
  have hACOldSub : Manifold.absolutelyContinuousOnInterval ThreeModel beta w d :=
    Manifold.absolutelyContinuousOnInterval_mono hACOld (by
      simpa only [uIcc_of_le hwd.le, uIcc_of_le (hwd.le.trans hdo.le)] using
        Icc_subset_Icc le_rfl hdo.le)
  have hintNewSub : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume c w :=
    hintNew.mono_set (by
      simpa only [uIcc_of_le hcw.le, uIcc_of_le (hnc.le.trans hcw.le)] using
        Icc_subset_Icc hnc.le le_rfl)
  have hintOldSub : IntervalIntegrable (lRegularizedLagrangian (H.event i).incoming.flow T beta)
      volume w d := hintOld.mono_set (by
      simpa only [uIcc_of_le hwd.le, uIcc_of_le (hwd.le.trans hdo.le)] using
        Icc_subset_Icc le_rfl hdo.le)
  have hnode : ∃ z : (H.event i).old, z.val.val = beta w ∧ (H.event i).oldOutput z = alpha w := by
    obtain ⟨z, _, hz, hzout⟩ := hcross
    exact ⟨z, hz, hzout⟩
  obtain ⟨eta, hetaAC, hleft, hright, hetaInt, hetaAct⟩ :=
    (H.event i).exists_survivor_curve_action_eq_of_confined_event_competitor G
      f g hlocalOld hlocalNew hfi hcrossW S T hcw.le hwd.le hbefore hafter
      alpha beta hACNewSub hACOldSub hintNewSub hintOldSub hnewStay holdStay hnode
  have hpairMin (alpha' : ℝ → (H.stage i.succ).Carrier)
      (beta' : ℝ → (H.stage i.castSucc).Carrier)
      (ha' : Manifold.absolutelyContinuousOnInterval ThreeModel alpha'
        (H.regularizedStageStart T u i.succ) w)
      (hb' : Manifold.absolutelyContinuousOnInterval ThreeModel beta'
        w (H.regularizedStageEnd T v i.castSucc))
      (hai' : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha') volume
        (H.regularizedStageStart T u i.succ) w)
      (hbi' : IntervalIntegrable (lRegularizedLagrangian (H.event i).incoming.flow T beta') volume
        w (H.regularizedStageEnd T v i.castSucc))
      (has' : alpha' (H.regularizedStageStart T u i.succ) = alpha (H.regularizedStageStart T u i.succ))
      (hbe' : beta' (H.regularizedStageEnd T v i.castSucc) = beta (H.regularizedStageEnd T v i.castSucc))
      (hn' : ∃ z : (H.event i).old, z.val.val = beta' w ∧ (H.event i).oldOutput z = alpha' w) :
      lRegularizedAction G.flow T alpha (H.regularizedStageStart T u i.succ) w +
        lRegularizedAction (H.event i).incoming.flow T beta w (H.regularizedStageEnd T v i.castSucc) ≤
      lRegularizedAction G.flow T alpha' (H.regularizedStageStart T u i.succ) w +
        lRegularizedAction (H.event i).incoming.flow T beta' w (H.regularizedStageEnd T v i.castSucc) := by
    have hh := H.stageRegularizedAction_add_le_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      i hf hl beta' alpha' (by simpa only [hOldStart] using hb')
      (by simpa only [hNewEnd] using ha') (by simpa only [hOldStart, hlagOld] using hbi')
      (by simpa only [hNewEnd, hlagNew] using hai') hbe' has' hn'
    simpa only [hOldStart, hNewEnd, H.stageRegularizedAction_castSucc, hactNew, add_comm] using hh
  have hminLocal := (H.event i).lRegularizedAction_le_of_minimal_event_competitor G
    f g hlocalOld hlocalNew hcrossW S T hnc.le hcw.le hwd.le hdo.le
    hbefore hafter alpha beta hACNew hACOld hintNew hintOld hpairMin eta hetaAC hleft hright
  have hcd : c < d := hcw.trans hwd
  let : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.event i).incoming.terminalRegularOpen.isOpen)
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace ThreeModel W
  let : PseudoMetricSpace W := TopologicalSpace.pseudoMetrizableSpacePseudoMetric W
  have hclockReg (r : ℝ) (hr : r ∈ Icc c d) :
      T - r ^ 2 ∈ (RealTimeInterval.closed C D (hCs.trans hsD).le).regular := hclock r hr
  have hminC1 (delta : ℝ → W) (hdelta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 delta)
      (hdc : delta c = eta c) (hdd : delta d = eta d) :
      lRegularizedAction S T eta c d ≤ lRegularizedAction S T delta c d :=
    hminLocal delta (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hdelta.contMDiffOn)
      (intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric
        ⟨hS.scalarCont⟩ T c d hcd.le delta hdelta.contMDiffOn hclockReg) hdc hdd
  have hetaC1 := lMinCurve_c1_of_absolutelyContinuousOnInterval S hS T c d hcd
    eta hetaAC hetaInt hclockReg hminC1
  have hetaGeo := lMinCurve_regularizedGeodesicOn_of_absolutelyContinuousOnInterval
    S hS T c d eta hetaAC hetaInt hclockReg hminC1
  refine ⟨C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, haC, hDb, hsource, hS,
    hcrossW, hpullOld, hpullNew, hterminal, c, d, huc, hcw, hwd, hdv, hnc, hdo, hclock,
    eta, hetaAC, hetaC1, hetaGeo, hleft, hright, hetaInt, ?_⟩
  simpa only [H.stageRegularizedAction_castSucc, hactNew] using hetaAct

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def regularizedSpatialCost (t : Icc (0 : ℝ) H.horizon) (B : ℝ)
    (p : (H.stageAt t).Carrier) (v : Icc (0 : ℝ) (Real.sqrt t.val)) : WithTop ℝ :=
  let s : Icc (0 : ℝ) H.horizon := ⟨t.val - v.val ^ 2, by
    constructor
    · have hsq : v.val ^ 2 ≤ t.val := (Real.le_sqrt v.property.1 t.property.1).mp v.property.2
      exact sub_nonneg.mpr hsq
    · exact (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  sInf (range (H.regularizedCost (H.activeStage s) (H.activeStage t)
    (H.activeStage_mono (by change t.val - v.val ^ 2 ≤ t.val; exact sub_le_self _ (sq_nonneg _))) t B 0 v.val p))

theorem regularizedSpatialCost_eq_of_mem_stageDomain
    (t : Icc (0 : ℝ) H.horizon) (B : ℝ) (p : (H.stageAt t).Carrier)
    (v : Icc (0 : ℝ) (Real.sqrt t.val)) (first : Fin (H.eventCount + 1))
    (hle : first ≤ H.activeStage t) (hclock : t.val - v.val ^ 2 ∈ H.stageDomain first) :
    H.regularizedSpatialCost t B p v =
      sInf (range (H.regularizedCost first (H.activeStage t) hle t B 0 v.val p)) := by
  let s : Icc (0 : ℝ) H.horizon := ⟨t.val - v.val ^ 2, H.stageDomain_subset first hclock⟩
  have hs : s ≤ t := by change t.val - v.val ^ 2 ≤ t.val; exact sub_le_self _ (sq_nonneg _)
  have he : H.activeStage s = first := (H.mem_stageDomain_iff s first).mp hclock
  have hj : (⟨H.activeStage s, H.activeStage_mono hs⟩ :
      {j : Fin (H.eventCount + 1) // j ≤ H.activeStage t}) = ⟨first, hle⟩ := Subtype.ext he
  exact congrArg (fun j : {j : Fin (H.eventCount + 1) // j ≤ H.activeStage t} =>
    sInf (range (H.regularizedCost j.val (H.activeStage t) j.property t B 0 v.val p))) hj

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
