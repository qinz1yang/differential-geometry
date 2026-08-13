import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
open DifferentialGeometry.Geometry.Curvature


noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorPointwiseNorm_intervalIntegral_sq_le_of_affine_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (F : ℝ → TensorRSModel r s ℝ E) (c u v : ℝ)
    (hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      tensorPointwiseNorm (I := I) (M := M) g r s x (F t) ≤
        c * (u * t + v * (1 - t))) :
    tensorPointwiseNorm (I := I) (M := M) g r s x
        (∫ t in (0 : ℝ)..1, F t) ^ 2 ≤ (c * ((u + v) / 2)) ^ 2 := by
  have hint_le := tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g r s x F hcont
  have hint1 : IntervalIntegrable
      (fun t : ℝ => tensorPointwiseNorm (I := I) (M := M) g r s x (F t))
      MeasureTheory.volume 0 1 :=
    ((tensorPointwiseNorm_continuous (I := I) (M := M) g r s x).comp_continuousOn
      hcont).intervalIntegrable_of_Icc (by norm_num)
  have hint2 : IntervalIntegrable (fun t : ℝ => c * (u * t + v * (1 - t)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul (continuous_const.sub continuous_id)))
  have hmono : (∫ t in (0 : ℝ)..1,
      tensorPointwiseNorm (I := I) (M := M) g r s x (F t)) ≤
      ∫ t in (0 : ℝ)..1, c * (u * t + v * (1 - t)) :=
    intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hbound
  have hwval : (∫ t in (0 : ℝ)..1, c * (u * t + v * (1 - t))) =
      c * ((u + v) / 2) := by
    have hderiv : ∀ t : ℝ, HasDerivAt
        (fun z : ℝ => c * (((u - v) / 2) * z ^ 2 + v * z))
        (c * (u * t + v * (1 - t))) t := by
      intro t
      convert (hasDerivAt_const t c).mul
        (((hasDerivAt_const t ((u - v) / 2)).mul ((hasDerivAt_id t).pow 2)).add
          ((hasDerivAt_const t v).mul (hasDerivAt_id t))) using 1 ;
        simp only [id_eq] ; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint2]
    ring
  have hnorm_nonneg : (0 : ℝ) ≤ tensorPointwiseNorm (I := I) (M := M) g r s x
      (∫ t in (0 : ℝ)..1, F t) :=
    tensorPointwiseNorm_nonneg (I := I) (M := M) g r s x _
  have hfinal : tensorPointwiseNorm (I := I) (M := M) g r s x
      (∫ t in (0 : ℝ)..1, F t) ≤ c * ((u + v) / 2) := by
    refine le_trans hint_le ?_
    rw [← hwval]
    exact hmono
  exact pow_le_pow_left₀ hnorm_nonneg hfinal 2

end L2
end Integral
end DifferentialGeometry
