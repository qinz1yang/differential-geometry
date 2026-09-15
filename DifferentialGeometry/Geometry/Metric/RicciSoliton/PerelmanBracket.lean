import DifferentialGeometry.Geometry.Metric.RicciSoliton.TensorForm
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem gradientRicciSoliton_iff_normSq0S_eq_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (sigma : ℝ) :
    gradientRicciSoliton (I := I) g f sigma ↔
      ∀ x, normSq0S (I := I) g x 2
        (metricRicciAt (I := I) g x +
          hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
            (f : M → ℝ) f.contMDiff x -
          (sigma / 2) • metricTensor0S (I := I) g x) = 0 := by
  rw [← metricRicciAt_add_hessianSec_eq_iff_gradientRicciSoliton]
  constructor
  · intro h x
    apply (normSq0S_eq_zero_iff (I := I) g x 2 _).mpr
    apply (tensor0S_eq_zero_iff_vec2 (I := I) _).mpr
    intro v w
    simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.add_apply,
      Tensor0SSpace.smul_apply, metricTensor0S_apply, smul_eq_mul]
    change metricRicciAt (I := I) g x (vec2 v w) +
      hessianSec (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g)
        (f : M → ℝ) f.contMDiff x (vec2 v w) - (sigma / 2) * g.inner x v w = 0
    exact sub_eq_zero.mpr (h x v w)
  · intro h x v w
    have hx := (normSq0S_eq_zero_iff (I := I) g x 2 _).mp (h x)
    have hv := (tensor0S_eq_zero_iff_vec2 (I := I) _).mp hx v w
    simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.add_apply,
      Tensor0SSpace.smul_apply, metricTensor0S_apply, smul_eq_mul] at hv
    exact sub_eq_zero.mp hv

theorem gradientRicciSoliton_perelman_bracket
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {tau : ℝ}
    (htau : tau ≠ 0) (hsol : gradientRicciSoliton (I := I) g f (1 / tau)) (x : M) :
    tau * (2 * ΔG (I := I) g f x - normGradSqFun (I := I) g f x +
      metricScalarAt (I := I) g x) + f x - (Module.finrank ℝ E : ℝ) =
      f x - tau * (metricScalarAt (I := I) g x + normGradSqFun (I := I) g f x) := by
  have htrace := gradientRicciSoliton_trace hsol x
  have htrace' : tau * (metricScalarAt (I := I) g x + ΔG (I := I) g f x) =
      (Module.finrank ℝ E : ℝ) / 2 := by
    rw [htrace]
    field_simp
  nlinarith

theorem gradientRicciSoliton_hamiltonNormalized_iff_perelman_bracket_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {tau : ℝ}
    (htau : tau ≠ 0) (hsol : gradientRicciSoliton (I := I) g f (1 / tau)) :
    hamiltonNormalized (I := I) g f (1 / tau) ↔
      ∀ x, tau * (2 * ΔG (I := I) g f x - normGradSqFun (I := I) g f x +
        metricScalarAt (I := I) g x) + f x - (Module.finrank ℝ E : ℝ) = 0 := by
  constructor
  · intro h x
    rw [gradientRicciSoliton_perelman_bracket htau hsol x]
    have hx := h x
    change metricScalarAt (I := I) g x + normGradSqFun (I := I) g f x =
      (1 / tau) * f x at hx
    rw [hx]
    field_simp
    ring
  · intro h x
    have hx := h x
    rw [gradientRicciSoliton_perelman_bracket htau hsol x] at hx
    change metricScalarAt (I := I) g x + normGradSqFun (I := I) g f x =
      (1 / tau) * f x
    field_simp
    nlinarith

end DifferentialGeometry.Geometry
