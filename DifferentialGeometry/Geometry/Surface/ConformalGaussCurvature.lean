import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Hodge.Codifferential

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian.Forms
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless] [BoundarylessManifold I M]


theorem ricciTensor_conformalMetric_twoDim
    (hdim : Module.finrank Real E = 2)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (conformalMetric f hf g) x v w
      = ricciTensor (I := I) g x v w
        + formLaplacianScalar (I := I) g hf x * g.inner x v w := sorry


theorem ricci_conformalMetric_twoDim
    (hdim : Module.finrank Real E = 2)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) (conformalMetric f hf g) x (vec2 (I := I) v w)
      = metricRicciAt (I := I) g x (vec2 (I := I) v w)
        + formLaplacianScalar (I := I) g hf x * g.inner x v w := by
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) (conformalMetric f hf g) x v w,
      metricRicciAt_apply_eq_ricciTensor (I := I) g x v w]
  exact ricciTensor_conformalMetric_twoDim (I := I) hdim f hf g x v w


theorem gaussCurvature_conformalMetric
    (hdim : Module.finrank Real E = 2)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) :
    gaussCurvature (I := I) (conformalMetric f hf g) x
      = Real.exp (-(2 * f x)) * (gaussCurvature (I := I) g x + formLaplacianScalar (I := I) g hf x) := by
  haveI hntE : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Nontrivial (TangentSpace I x) := hntE
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : TangentSpace I x)
  have hpos : 0 < g.inner x v₀ v₀ := g.pos x v₀ hv₀
  have hne : g.inner x v₀ v₀ ≠ 0 := ne_of_gt hpos
  have hE2 : Real.exp (2 * f x) ≠ 0 := Real.exp_ne_zero _
  have hEg : metricRicciAt (I := I) g x (vec2 (I := I) v₀ v₀)
      = gaussCurvature (I := I) g x * g.inner x v₀ v₀ :=
    ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim g x v₀ v₀
  have hEĝ : metricRicciAt (I := I) (conformalMetric f hf g) x (vec2 (I := I) v₀ v₀)
      = gaussCurvature (I := I) (conformalMetric f hf g) x
          * (conformalMetric f hf g).inner x v₀ v₀ :=
    ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim (conformalMetric f hf g) x v₀ v₀
  rw [conformalMetric_inner] at hEĝ
  have hRic := ricci_conformalMetric_twoDim (I := I) hdim f hf g x v₀ v₀
  have hchain : gaussCurvature (I := I) (conformalMetric f hf g) x
        * (Real.exp (2 * f x) * g.inner x v₀ v₀)
      = (gaussCurvature (I := I) g x + formLaplacianScalar (I := I) g hf x)
          * g.inner x v₀ v₀ := by
    rw [← hEĝ, hRic, hEg]; ring
  have hkey : gaussCurvature (I := I) (conformalMetric f hf g) x * Real.exp (2 * f x)
      = gaussCurvature (I := I) g x + formLaplacianScalar (I := I) g hf x := by
    have h := hchain
    rw [← mul_assoc] at h
    exact mul_right_cancel₀ hne h
  rw [Real.exp_neg, ← hkey,
      mul_comm (gaussCurvature (I := I) (conformalMetric f hf g) x) (Real.exp (2 * f x)),
      ← mul_assoc, inv_mul_cancel₀ hE2, one_mul]


end DifferentialGeometry.Integral.Connection
