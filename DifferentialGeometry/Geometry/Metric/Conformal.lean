import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.Riemannian.Basic



noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def conformalMetric (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : SmoothRiemannianMetric I M where
  inner x := Real.exp (2 * f x) • g.inner x
  symm x := (scaleMetric _ (Real.exp_pos _) g).symm x
  pos x := (scaleMetric _ (Real.exp_pos _) g).pos x
  isVonNBounded x := (scaleMetric _ (Real.exp_pos _) g).isVonNBounded x
  contMDiff := by
    have hs : ContMDiff I 𝓘(ℝ) ∞ (fun x => Real.exp (2 * f x)) :=
      Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hf)
    exact hs.smul_section g.contMDiff

@[simp] theorem conformalMetric_inner (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v w : TangentSpace I x) :
    (conformalMetric g f hf).inner x v w = Real.exp (2 * f x) * g.inner x v w := rfl


def euclideanMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    SmoothRiemannianMetric 𝓘(ℝ, V) V :=
  { riemannianMetricVectorSpace V with
    contMDiff := (riemannianMetricVectorSpace V).contMDiff.of_le le_top }

@[simp] theorem euclideanMetric_inner (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x v w : V) :
    (euclideanMetric V).inner x v w = inner ℝ v w := rfl

end DifferentialGeometry.Geometry
