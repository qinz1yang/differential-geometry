import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Topology.Manifold.GluingAtlas

section

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))


theorem IntrinsicBallChart.exists_smooth_atlas_bufferedTransitionGlueData
    (hsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2))) :
    let U : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    ∃ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued ∧
      ∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z) := by
  let U : TopologicalSpace.Opens E := ⟨Metric.ball 0 (ρ / 8), Metric.isOpen_ball⟩
  let : Nonempty U := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  dsimp only [IntrinsicBallChart.bufferedTransitionGlueData]
  exact TopCat.GlueData.exists_smooth_atlas_ofTransitionMaps U near J
    (fun a => (hcont a).mono (Metric.ball_subset_ball (by linarith)))
    _ _ _ _ _ (fun a => (hsmooth a).mono (Metric.ball_subset_ball (by linarith)))

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
