import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem gradient_norm_le_of_sqrt_lipschitz
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {L : ℝ≥0}
    (hf : ∀ x, 0 ≤ f x)
    (hlip : ∀ x y, edist (Real.sqrt (f x)) (Real.sqrt (f y)) ≤
      (L : ℝ≥0∞) * riemannianEDistOf g x y) (x : M) :
    Real.sqrt (g.inner x (gradientFun g f x) (gradientFun g f x)) ≤
      2 * (L : ℝ) * Real.sqrt (f x) := by
  have hright : 0 ≤ 2 * (L : ℝ) * Real.sqrt (f x) := by positivity
  by_cases hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · by_cases hx : f x = 0
    · have hmin : IsLocalMin f x := Eventually.of_forall fun y => by
        simpa only [hx] using hf y
      rw [gradientFun_eq_zero_of_isLocalMin g hmin hdiff]
      simpa only [map_zero, Real.sqrt_zero] using hright
    · have hsqrt : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.sqrt (f y)) x :=
        (Real.hasDerivAt_sqrt hx).differentiableAt.mdifferentiableAt.comp x hdiff
      have heq : (fun y => Real.sqrt (f y) * Real.sqrt (f y)) = f :=
        funext fun y => Real.mul_self_sqrt (hf y)
      have hgrad : gradientFun g f x =
          (2 * Real.sqrt (f x)) • gradientFun g (fun y => Real.sqrt (f y)) x := by
        simpa only [heq] using gradientFun_mul_self g hsqrt
      have hnorm : Real.sqrt (g.inner x
          (gradientFun g (fun y => Real.sqrt (f y)) x)
          (gradientFun g (fun y => Real.sqrt (f y)) x)) ≤ (L : ℝ) :=
        Riemannian.grad_norm_le_lip_all g hlip
      let v := gradientFun g (fun y => Real.sqrt (f y)) x
      have hinner : g.inner x ((2 * Real.sqrt (f x)) • v)
          ((2 * Real.sqrt (f x)) • v) = (2 * Real.sqrt (f x)) ^ 2 * g.inner x v v := by
        rw [(g.inner x).map_smul (2 * Real.sqrt (f x)) v, smul_apply,
          (g.inner x v).map_smul (2 * Real.sqrt (f x)) v]
        simp only [smul_eq_mul]
        ring
      rw [hgrad]
      change Real.sqrt (g.inner x ((2 * Real.sqrt (f x)) • v)
        ((2 * Real.sqrt (f x)) • v)) ≤ _
      rw [hinner, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      calc
        _ ≤ (2 * Real.sqrt (f x)) * (L : ℝ) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = 2 * (L : ℝ) * Real.sqrt (f x) := by ring
  · rw [gradientFun_eq_zero_of_mfderiv_eq_zero g f
      (mfderiv_zero_of_not_mdifferentiableAt hdiff)]
    simpa only [map_zero, Real.sqrt_zero] using hright

end DifferentialGeometry.Geometry.Operator
