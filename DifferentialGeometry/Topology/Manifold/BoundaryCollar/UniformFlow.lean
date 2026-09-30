import DifferentialGeometry.Topology.Manifold.BoundaryCollar.UniformInwardFlow

open Set Function Filter Manifold
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_uniform_boundary_flow
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      IsCompact (tsupport V) ∧
      ∃ U : TopologicalSpace.Opens M, (𝓡∂ (n + 1)).boundary M ⊆ U ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ F : M × ℝ → M,
          ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ F
            ((U : Set M) ×ˢ Icc (0 : ℝ) ε) ∧
          (∀ y ∈ U, F (y, 0) = y) ∧
          (∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y, t)) V (Icc (0 : ℝ) ε)) ∧
          (∀ y ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (y, t))) ∧
          ∀ t ∈ Icc (0 : ℝ) ε, InjOn (fun y => F (y, t)) U := by
  obtain ⟨V, hV, hVK, _, hflow⟩ := exists_uniform_positive_boundary_flow hK
  exact ⟨V, hV, hVK, hflow⟩

end DifferentialGeometry.Manifold.BoundaryCollar
