import DifferentialGeometry.Geometry.Boundary.LocalFlow
import DifferentialGeometry.Topology.Manifold.UniformBoundaryFlow

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M]

theorem exists_inward_uniformFlow
    {v : (x : M) → TangentSpace I x} {K : Set M} (hK : IsCompact K)
    (hboundary : K ⊆ I.boundary M)
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hinward : ∀ (x : BoundaryManifold I M), x.1 ∈ K →
      ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
        v x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x) :
    ∃ ε > 0, ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
      ∃ Φ : M × ℝ → M,
        (∀ y ∈ U, Φ (y, 0) = y) ∧
        ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (U ×ˢ Ico 0 ε) ∧
        (∀ y ∈ U, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) v (Ico 0 ε)) ∧
        ∀ y ∈ U, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  apply exists_uniform_localFlow_of_compact hK (hv.of_le (by simp))
  intro x hx
  exact exists_inward_localFlow hv ⟨x, hboundary hx⟩ (hinward ⟨x, hboundary hx⟩ hx)

end DifferentialGeometry.Geometry.Boundary
