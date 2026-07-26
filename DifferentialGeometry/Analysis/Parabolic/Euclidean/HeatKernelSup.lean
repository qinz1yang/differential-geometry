import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Euclidean heat kernels on the spatial supremum norm

This file supplies the endpoint missing from `HeatKernelLp`: an `L¹` scalar
kernel acts pointwise on a bounded continuous Banach-valued function, with the
usual `L¹ * L∞ → L∞` estimate.  In particular the Euclidean heat kernel is a
contraction in the spatial supremum norm, while its first and second spatial
derivatives have the expected `t⁻¹ᐟ²` and `t⁻¹` bounds.

The operator is deliberately defined pointwise.  Translation is not strongly
continuous on the full space of bounded continuous functions on a noncompact
Euclidean space, so packaging the convolution as a Bochner integral *in* that
Banach space would assert a false fact.  The pointwise construction is exactly
what the local rough Ricci--DeTurck Duhamel estimates consume.
-/

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section SupKernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Pointwise convolution of an `L¹` scalar kernel with a bounded continuous
Banach-valued function. -/
def supKernel (η : V → ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ y, η y • u (x - y)

omit [CompleteSpace F] in
/-- The pointwise integrand defining `supKernel` is Bochner integrable. -/
theorem supKernel_int {η : V → ℝ} (hη : Integrable η)
    (u : BoundedContinuousFunction V F) (x : V) :
    Integrable (fun y : V => η y • u (x - y)) := by
  refine (hη.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hη.aestronglyMeasurable.smul
      ((u.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (x - y)) (norm_nonneg _)

omit [CompleteSpace F] in
/-- Young's pointwise `L¹ * L∞ → L∞` estimate. -/
theorem supKernel_norm {η : V → ℝ} (hη : Integrable η)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖supKernel η u x‖ ≤ (∫ y, ‖η y‖) * ‖u‖ := by
  unfold supKernel
  calc
    ‖∫ y, η y • u (x - y)‖
        ≤ ∫ y, ‖η y‖ * ‖u‖ :=
      norm_integral_le_of_norm_le (hη.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (x - y))
            (norm_nonneg _))
    _ = (∫ y, ‖η y‖) * ‖u‖ := by rw [integral_mul_const]

omit [CompleteSpace F] in
/-- Pointwise convolution is linear in the bounded input. -/
theorem supKernel_sub {η : V → ℝ} (hη : Integrable η)
    (u v : BoundedContinuousFunction V F) (x : V) :
    supKernel η (u - v) x = supKernel η u x - supKernel η v x := by
  unfold supKernel
  rw [← integral_sub (supKernel_int hη u x) (supKernel_int hη v x)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [BoundedContinuousFunction.sub_apply, smul_sub]

omit [CompleteSpace F] in
/-- A nonnegative probability kernel acts contractively in the spatial
supremum norm, stated pointwise so no uniform-continuity hypothesis is hidden. -/
theorem supKernel_contract {η : V → ℝ} (hη : Integrable η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∫ y, η y = 1)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖supKernel η u x‖ ≤ ‖u‖ := by
  refine (supKernel_norm hη u x).trans_eq ?_
  have habs : (fun y : V => ‖η y‖) = η := by
    funext y
    simp [Real.norm_eq_abs, abs_of_nonneg (hη0 y)]
  rw [habs, hη1, one_mul]

end SupKernel

section HeatSup

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Pointwise Euclidean heat evolution of bounded continuous data. -/
def heatSup (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatKernel t) u x

omit [CompleteSpace F] in
/-- The positive-time Euclidean heat operator is a pointwise `L∞`
contraction. -/
theorem heatSup_contract {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatSup t u x‖ ≤ ‖u‖ := by
  exact supKernel_contract (heatKernel_int ht) (heatKernel_nonneg ht)
    (integral_heatKernel ht) u x

/-- First spatial derivative heat convolution in direction `v`. -/
def heatD1Sup (t : ℝ) (v : V) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatD1 t v) u x

/-- Second spatial derivative heat convolution in directions `v,w`. -/
def heatD2Sup (t : ℝ) (v w : V) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatD2 t v w) u x

omit [CompleteSpace F] in
/-- First-derivative heat convolution is linear in its bounded input. -/
theorem heatD1Sup_sub {t : ℝ} (ht : 0 < t) (v : V)
    (u₁ u₂ : BoundedContinuousFunction V F) (x : V) :
    heatD1Sup t v (u₁ - u₂) x =
      heatD1Sup t v u₁ x - heatD1Sup t v u₂ x := by
  exact supKernel_sub (heatD1_int ht v) u₁ u₂ x

omit [CompleteSpace F] in
/-- Second-derivative heat convolution is linear in its bounded input. -/
theorem heatD2Sup_sub {t : ℝ} (ht : 0 < t) (v w : V)
    (u₁ u₂ : BoundedContinuousFunction V F) (x : V) :
    heatD2Sup t v w (u₁ - u₂) x =
      heatD2Sup t v w u₁ x - heatD2Sup t v w u₂ x := by
  exact supKernel_sub (heatD2_int ht v w) u₁ u₂ x

omit [CompleteSpace F] in
/-- First-derivative pointwise `L∞` smoothing estimate. -/
theorem heatD1Sup_norm {t : ℝ} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD1Sup t v u x‖ ≤
      (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ := by
  refine (supKernel_norm (heatD1_int ht v) u x).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D1 ht v) (norm_nonneg _)

omit [CompleteSpace F] in
/-- Second-derivative pointwise `L∞` smoothing estimate. -/
theorem heatD2Sup_norm {t : ℝ} (ht : 0 < t) (v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD2Sup t v w u x‖ ≤
      (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
  refine (supKernel_norm (heatD2_int ht v w) u x).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) (norm_nonneg _)

end HeatSup

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
