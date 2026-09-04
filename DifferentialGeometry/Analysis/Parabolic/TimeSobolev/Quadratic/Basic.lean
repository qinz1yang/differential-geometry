import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

noncomputable def timeQuad
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeL2 X T) : ℝ :=
  inner ℝ (timeOp A hA C hC u) u

omit [CompleteSpace X] in
theorem timeQuad_int
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hT : 0 ≤ T)
    (u : timeL2 X T) :
    IntervalIntegrable (fun t ↦ inner ℝ (A t (u t)) (u t)) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  change Integrable (fun t ↦ inner ℝ (A t (u t)) (u t)) (timeMeasure T)
  refine (L2.integrable_inner (timeOp A hA C hC u) u).congr ?_
  filter_upwards [timeOp_apply_ae A hA C hC u] with t ht
  rw [ht]

omit [CompleteSpace X] in
theorem timeQuad_eq_integral
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hT : 0 ≤ T)
    (u : timeL2 X T) :
    timeQuad A hA C hC u =
      ∫ t in (0 : ℝ)..T, inner ℝ (A t (u t)) (u t) := by
  rw [timeQuad, inner_def, intervalIntegral.integral_of_le hT,
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [timeOp_apply_ae A hA C hC u] with t ht
  rw [ht]

omit [CompleteSpace X] in
private theorem timeOp_nonneg
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A t x) x)
    (u : timeL2 X T) :
    0 ≤ inner ℝ (timeOp A hA C hC u) u := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [timeOp_apply_ae A hA C hC u, hpos] with t hu ht
  rw [hu]
  exact ht (u t)

private theorem timeOp_positive
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A t x) x) :
    (timeOp A hA C hC).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨?_, ?_⟩
  · intro u v
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [timeOp_apply_ae A hA C hC u,
      timeOp_apply_ae A hA C hC v, hself] with t hu hv ht
    change inner ℝ ((timeOp A hA C hC u) t) (v t) =
      inner ℝ (u t) ((timeOp A hA C hC v) t)
    rw [hu, hv]
    exact ht.isSymmetric (u t) (v t)
  · intro u
    exact timeOp_nonneg A hA C hC hpos u

private theorem quad_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (hL : L.IsPositive) :
    ConvexOn ℝ univ (fun x ↦ inner ℝ (L x) x) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hxy : 0 ≤ inner ℝ (L (x - y)) (x - y) := hL.inner_nonneg_left (x - y)
  have hsym : inner ℝ (L x) y = inner ℝ x (L y) :=
    hL.inner_left_eq_inner_right x y
  have hid :
      inner ℝ (L (a • x + b • y)) (a • x + b • y) =
        a * inner ℝ (L x) x + b * inner ℝ (L y) y -
          a * b * inner ℝ (L (x - y)) (x - y) := by
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hsym, real_inner_comm x (L y)]
    have hb_eq : b = 1 - a := by linarith
    rw [hb_eq]
    ring
  change inner ℝ (L (a • x + b • y)) (a • x + b • y) ≤
    a * inner ℝ (L x) x + b * inner ℝ (L y) y
  rw [hid]
  have habpos : 0 ≤ a * b * inner ℝ (L (x - y)) (x - y) :=
    mul_nonneg (mul_nonneg ha hb) hxy
  linarith

private theorem quad_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) :
    Continuous (fun x ↦ inner ℝ (L x) x) :=
  L.continuous.inner continuous_id

private theorem weak_lsc_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ConvexOn ℝ univ f) (hc : Continuous f) :
    LowerSemicontinuous (fun x : WeakSpace ℝ E ↦ f ((toWeakSpace ℝ E).symm x)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  let s : Set E := {x | f x ≤ r}
  have hsconv : Convex ℝ s := by
    simpa [s] using hf.convex_le r
  have hsclosed : IsClosed s := by
    exact isClosed_le hc continuous_const
  have himage : IsClosed ((toWeakSpace ℝ E) '' s) := by
    rw [← closure_eq_iff_isClosed]
    rw [← hsconv.toWeakSpace_closure ℝ, hsclosed.closure_eq]
  have heq :
      (fun x : WeakSpace ℝ E ↦ f ((toWeakSpace ℝ E).symm x)) ⁻¹' Iic r =
        (toWeakSpace ℝ E) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨(toWeakSpace ℝ E).symm x, hx, (toWeakSpace ℝ E).apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [s] using hy
  rw [heq]
  exact himage

omit [CompleteSpace X] in
theorem timeQuad_nonneg
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A t x) x)
    (u : timeL2 X T) :
    0 ≤ timeQuad A hA C hC u :=
  timeOp_nonneg A hA C hC hpos u

theorem timeQuad_convex
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A t x) x) :
    ConvexOn ℝ univ (timeQuad A hA C hC) := by
  exact quad_convex _ (timeOp_positive A hA C hC hself hpos)

theorem timeQuad_weak_lsc
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ inner ℝ (A t x) x) :
    LowerSemicontinuous
      (fun u : WeakSpace ℝ (timeL2 X T) ↦
        timeQuad A hA C hC ((toWeakSpace ℝ (timeL2 X T)).symm u)) := by
  apply weak_lsc_of_convex
  · exact timeQuad_convex A hA C hC hself hpos
  · exact quad_continuous (timeOp A hA C hC)

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
