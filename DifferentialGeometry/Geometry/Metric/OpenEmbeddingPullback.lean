import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Scaling

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

def pullbackMetricOfInjectiveLocalDiffeomorph
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) :
    SmoothRiemannianMetric I M :=
  Diffeomorph.pullbackMetricCross (g.restrictOpen hf.image)
    (diffeomorphOntoImage f hf hinj)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M]
  [T2Space M] [IsManifold J ∞ N] [T2Space N] in
private theorem mfderiv_chart_eq_of_ambient_eq
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V) (f : M → N)
    (he : ∀ x, (Φ x : N) = f x) (x : M) :
    mfderiv I J Φ x = mfderiv I J f x := by
  have hcomp : (Subtype.val : V → N) ∘ Φ = f := funext he
  rw [← hcomp, mfderiv_comp x
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    (Φ.contMDiff.mdifferentiableAt (by decide)), mfderiv_subtype_val]
  rfl

theorem pullbackMetricOfInjectiveLocalDiffeomorph_inner
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (x : M) (v w : TangentSpace I x) :
    (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  unfold pullbackMetricOfInjectiveLocalDiffeomorph
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_chart_eq_of_ambient_eq hf.image (diffeomorphOntoImage f hf hinj) f
      (diffeomorphOntoImage_apply f hf hinj) x]
  rfl

theorem pullbackMetricOfInjectiveLocalDiffeomorph_eq_chart
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V)
    (he : ∀ x, (Φ x : N) = f x) :
    pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj =
      Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner,
    Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_chart_eq_of_ambient_eq V Φ f he x, he x]
  rfl

theorem pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (c : ℝ) (hc : 0 < c)
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V)
    (he : ∀ x, (Φ x : N) = f x) :
    pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric c hc g) f hf hinj =
      Diffeomorph.pullbackMetricCross (scaleMetric c hc (g.restrictOpen V)) Φ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner,
    Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner, scaleMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_chart_eq_of_ambient_eq V Φ f he x, he x]
  rfl

end DifferentialGeometry.Geometry.Metric
