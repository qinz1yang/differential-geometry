import Mathlib.Geometry.Manifold.Instances.Real
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.OperatorNaturality

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Curvature
private abbrev SectionE3 := EuclideanSpace ℝ (Fin 3)
private local instance : NeZero (Module.finrank ℝ SectionE3) := ⟨by simp⟩
variable {S T : Type*} [TopologicalSpace S] [ChartedSpace SectionE3 S] [IsManifold (𝓡 3) ∞ S] [T2Space S]
  [TopologicalSpace T] [ChartedSpace SectionE3 T] [IsManifold (𝓡 3) ∞ T] [T2Space T]
  [SigmaCompactSpace S]

theorem riemann_of_injective_local_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (x : S) (v w z u : TangentSpace (𝓡 3) x) :
    metricRm04StandardAt g x v w z u = metricRm04StandardAt h (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
      (mfderiv (𝓡 3) (𝓡 3) f x z) (mfderiv (𝓡 3) (𝓡 3) f x u) := by
  let D := diffeomorphOntoImage f hf hinj
  have hrange : range D = univ := D.surjective.range_eq
  let : SigmaCompactSpace hf.image := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range D.continuous)
  have hpoint : (Subtype.val : hf.image → T) ∘ D = f := funext (diffeomorphOntoImage_apply f hf hinj)
  have hd : mfderiv (𝓡 3) (𝓡 3) D x = mfderiv (𝓡 3) (𝓡 3) f x := by
    have hc := mfderiv_comp x
      ((contMDiff_subtype_val (I := 𝓡 3) (U := hf.image) (n := ∞)).mdifferentiable (by simp) (D x))
      (D.contMDiff.mdifferentiable (by simp) x)
    rw [mfderiv_subtype_val] at hc
    exact hc.symm.trans (mfderiv_congr hpoint)
  have hg : g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro y a b
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric y a b
  have he := metricRm04Standard_pullbackCross (h.restrictOpen hf.image) D x v w z u
  have hr := metricRm04StandardAt_restrictOpen h hf.image (D x)
    (mfderiv (𝓡 3) (𝓡 3) D x v) (mfderiv (𝓡 3) (𝓡 3) D x w)
    (mfderiv (𝓡 3) (𝓡 3) D x z) (mfderiv (𝓡 3) (𝓡 3) D x u)
  rw [hg]
  change metricRm04StandardAt (Diffeomorph.pullbackMetricCross (h.restrictOpen hf.image) D) x v w z u = _
  simp only [mfderiv_subtype_val_apply] at hr
  have ht := he.trans hr
  have hDx : (D x : T) = f x := diffeomorphOntoImage_apply f hf hinj x
  dsimp only [TangentSpace] at hd
  erw [hd, hDx] at ht
  exact ht

theorem sectional_of_injective_local_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (x : S) (v w : TangentSpace (𝓡 3) x) :
    sectionalCurvature g x v w = sectionalCurvature h (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  rw [sectionalCurvature_eq_metricRm04StandardAt_div, sectionalCurvature_eq_metricRm04StandardAt_div,
    riemann_of_injective_local_isometry g h f hf hinj hmetric x v w w v,
    hmetric x v v, hmetric x w w, hmetric x v w]
end DifferentialGeometry.Geometry.Curvature
