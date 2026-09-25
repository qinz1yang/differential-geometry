import DifferentialGeometry.Analysis.Integration.Integral.LowerBounded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

private theorem integrable_scalar_floor (B a b : ℝ) :
    Integrable (fun s : ℝ ↦ -2 * B * s ^ 2) (volume.restrict (Ioo a b)) := by
  exact (continuous_const.mul (continuous_id.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem scalar_floor_le_lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D) (T B a b : ℝ) (α : ℝ → M)
    (hscalar : ∀ᵐ s ∂volume.restrict (Ioo a b), -B ≤ S.scalar (T - s ^ 2) (α s)) :
    (fun s ↦ -2 * B * s ^ 2) ≤ᵐ[volume.restrict (Ioo a b)]
      lRegularizedLagrangian S T α := by
  filter_upwards [hscalar] with s hs
  have hkin := metric_inner_self_nonneg (S.base.metric (T - s ^ 2)) (α s) (lVelocity α s)
  have hscalar' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * s ^ 2 by positivity)
  dsimp only [lRegularizedLagrangian]
  nlinarith

def lRegularizedExtendedAction
    (S : SolutionOn (I := I) (M := M) D) (T B : ℝ) (α : ℝ → M) (a b : ℝ) : WithTop ℝ :=
  lowerBoundedIntegral (lRegularizedLagrangian S T α) (fun s ↦ -2 * B * s ^ 2)
    (volume.restrict (Ioo a b))

theorem lRegularizedExtendedAction_eq_action
    (S : SolutionOn (I := I) (M := M) D) (T B : ℝ) (α : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) (hα : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b)
    (hscalar : ∀ᵐ s ∂volume.restrict (Ioo a b), -B ≤ S.scalar (T - s ^ 2) (α s)) :
    lRegularizedExtendedAction S T B α a b = (lRegularizedAction S T α a b : WithTop ℝ) := by
  rw [lRegularizedExtendedAction, lowerBoundedIntegral_eq_integral
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hα)
    (integrable_scalar_floor B a b) (scalar_floor_le_lRegularizedLagrangian S T B a b α hscalar)]
  rw [lRegularizedAction, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem lRegularizedExtendedAction_eq_top_iff
    (S : SolutionOn (I := I) (M := M) D) (T B : ℝ) (α : ℝ → M) {a b : ℝ}
    (hab : a ≤ b)
    (hα : AEStronglyMeasurable (lRegularizedLagrangian S T α) (volume.restrict (Ioo a b)))
    (hscalar : ∀ᵐ s ∂volume.restrict (Ioo a b), -B ≤ S.scalar (T - s ^ 2) (α s)) :
    lRegularizedExtendedAction S T B α a b = ⊤ ↔
      ¬ IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
  rw [lRegularizedExtendedAction, lowerBoundedIntegral_eq_top_iff hα
    (integrable_scalar_floor B a b) (scalar_floor_le_lRegularizedLagrangian S T B a b α hscalar)]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  rfl

theorem lRegularizedExtendedAction_congr_scalar_lower_bound
    (S : SolutionOn (I := I) (M := M) D) (T B C : ℝ) (α : ℝ → M) (a b : ℝ)
    (hα : AEStronglyMeasurable (lRegularizedLagrangian S T α) (volume.restrict (Ioo a b)))
    (hB : ∀ᵐ s ∂volume.restrict (Ioo a b), -B ≤ S.scalar (T - s ^ 2) (α s))
    (hC : ∀ᵐ s ∂volume.restrict (Ioo a b), -C ≤ S.scalar (T - s ^ 2) (α s)) :
    lRegularizedExtendedAction S T B α a b = lRegularizedExtendedAction S T C α a b := by
  exact lowerBoundedIntegral_congr_lower_bound hα
    (integrable_scalar_floor B a b) (integrable_scalar_floor C a b)
    (scalar_floor_le_lRegularizedLagrangian S T B a b α hB)
    (scalar_floor_le_lRegularizedLagrangian S T C a b α hC)

theorem lRegularizedExtendedAction_eq_lintegral
    (S : SolutionOn (I := I) (M := M) D) (T B : ℝ) (α : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    lRegularizedExtendedAction S T B α a b =
      if (∫⁻ s in Ioo a b, ENNReal.ofReal (lRegularizedLagrangian S T α s + 2 * B * s ^ 2)) = (⊤ : ℝ≥0∞) then ⊤ else
        ↑((∫⁻ s in Ioo a b, ENNReal.ofReal (lRegularizedLagrangian S T α s + 2 * B * s ^ 2)).toReal -
          2 * B / 3 * (b ^ 3 - a ^ 3) : ℝ) := by
  have hint : ∫ s in Ioo a b, -2 * B * s ^ 2 = -(2 * B / 3 * (b ^ 3 - a ^ 3)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  unfold lRegularizedExtendedAction lowerBoundedIntegral
  rw [hint]
  simp only [neg_mul, neg_neg, sub_eq_add_neg]

end DifferentialGeometry.PDE.RicciFlow.Perelman
