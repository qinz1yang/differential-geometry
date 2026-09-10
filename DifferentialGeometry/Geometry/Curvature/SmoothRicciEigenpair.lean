import DifferentialGeometry.Bundle.SmoothMetricEigenpair
import DifferentialGeometry.Geometry.Curvature.RicciSharpSmooth

noncomputable section
open Set Bundle
open scoped ContDiff Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace Poincare.Geometry.Curvature

theorem exists_smooth_ricci_eigenpair_near_simple
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {U : Set M} (hU : IsOpen U)
    {x₀ : M} (hx₀ : x₀ ∈ U) (μ₀ : ℝ) (w₀ : TangentSpace I x₀)
    (hw₀ : g.inner x₀ w₀ w₀ = 1) (heigen : ricciSharp g x₀ w₀ = μ₀ • w₀)
    (hsimple : Module.End.eigenspace (ricciSharp g x₀).toLinearMap μ₀ = Submodule.span ℝ {w₀}) :
    ∃ V : Set M, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : M → ℝ) (w : ∀ x : M, TangentSpace I x),
        ContMDiffOn I 𝓘(ℝ) ∞ μ V ∧
        ContMDiffOn I I.tangent ∞ (fun x ↦ (⟨x, w x⟩ : TangentBundle I M)) V ∧
        μ x₀ = μ₀ ∧ w x₀ = w₀ ∧ ∀ x ∈ V,
          g.inner x (w x) (w x) = 1 ∧ ricciSharp g x (w x) = μ x • w x := by
  apply Poincare.Geometry.VectorBundle.exists_smooth_metric_normalized_eigenpair g (ricciSharp g)
    hU (ricciSharp_contMDiff g).contMDiffOn hx₀ _ μ₀ w₀ hw₀ heigen hsimple
  intro u v
  rw [inner_ricciSharp, inner_ricciSharp_right, ricciTensor_symm g x₀ u v]

end Poincare.Geometry.Curvature
