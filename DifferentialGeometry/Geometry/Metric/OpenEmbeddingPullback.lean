import DifferentialGeometry.Geometry.Metric.Construction.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding
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

open Manifold

namespace DifferentialGeometry.Geometry.Metric

open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq
    (g : SmoothRiemannianMetric J N) {f : M → N} (hf : IsImmersion I J ∞ f)
    (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V)
    (he : ∀ x, (Φ x : N) = f x) :
    Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ = immersionInducedMetric g hf := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hcomp : (fun y => (Φ y : N)) = f := funext he
  have hd : mfderiv I J Φ x = mfderiv I J f x := by
    rw [← hcomp]
    exact (DifferentialGeometry.mfderiv_subtypeVal_comp Φ x).symm
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    immersionInducedMetric_inner, hd, he x]
  rfl

theorem pullbackMetricCross_diffeomorphOntoImage_eq_immersionInducedMetric
    (g : SmoothRiemannianMetric J N) {f : M → N} (hf : IsImmersion I J ∞ f)
    (hlocal : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    Diffeomorph.pullbackMetricCross (g.restrictOpen hlocal.image)
      (diffeomorphOntoImage f hlocal hinj) = immersionInducedMetric g hf :=
  pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq g hf hlocal.image
    (diffeomorphOntoImage f hlocal hinj) (diffeomorphOntoImage_apply f hlocal hinj)

theorem exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric
    [J.Boundaryless] (g : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsImmersion I J ∞ f) (hinj : Function.Injective f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ (V : TopologicalSpace.Opens N) (Φ : M ≃ₘ⟮I, J⟯ V),
      (V : Set N) = Set.range f ∧ (∀ x, (Φ x : N) = f x) ∧
        (∀ y : V, f (Φ.symm y) = (y : N)) ∧
        Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ =
          immersionInducedMetric g hf := by
  obtain ⟨V, Φ, hV, he, hi⟩ := exists_diffeomorph_onto_range_of_injective_immersion f
    hf.contMDiff hinj
    (fun x => immersionAt_mfderiv_injective (hf.isImmersionAt x)) hdim
  exact ⟨V, Φ, hV, he, hi, pullbackMetricCross_eq_immersionInducedMetric_of_coe_eq g
    hf V Φ he⟩

end DifferentialGeometry.Geometry.Metric
