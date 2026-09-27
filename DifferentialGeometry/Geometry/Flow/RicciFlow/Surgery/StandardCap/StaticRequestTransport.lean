import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticRequests
import DifferentialGeometry.Geometry.Metric.EmbeddingComposition

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticRequest
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {S T : Type*} [TopologicalSpace S] [ChartedSpace E3 S] [IsManifold (𝓡 3) ∞ S] [T2Space S]
  [TopologicalSpace T] [ChartedSpace E3 T] [IsManifold (𝓡 3) ∞ T] [T2Space T]

theorem IsSatisfied.comp_of_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) = g.inner x v w)
    (Q : ℝ) (hQ : 0 < Q) (U : Opens E3) (J : U → S)
    (hJ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ J) (hJinj : Injective J) (p : S)
    {P : StaticRequest} (hP : P.IsSatisfied g Q hQ U J hJ hJinj p) :
    P.IsSatisfied h Q hQ U (f ∘ J)
      (fun q => (hJ q).comp (𝓡 3) T (hf (J q))) (hinj.comp hJinj) (f p) := by
  refine ⟨hP.1, fun h0 => congrArg f (hP.2.1 h0), ?_⟩
  rw [scaled_pullback_comp_of_isometry g h f hf hinj hmetric J hJ hJinj]
  exact hP.2.2
end DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticRequest
