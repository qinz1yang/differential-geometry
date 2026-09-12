import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux



noncomputable section

open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_universal_neck_recenter_constants :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M],
      ∀ (g : SmoothRiemannianMetric ThreeModel M) (k : ℕ), 2 ≤ k →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ N : NormalizedNeck g δ k,
      ∀ side : Bool,
      let s : ℝ := if side then 1 else -1
      ∃ hbuffer : ∀ x : neckBuffer (c * δ),
          (x.1.1, s * (1 + x.1.2)) ∈ neckBuffer δ,
      ∃ N' : NormalizedNeck g (c * δ) k,
        N'.sphereMark = N.sphereMark ∧
        (∀ x : neckBuffer (c * δ), N'.chart x =
          N.chart ⟨(x.1.1, s * (1 + x.1.2)), hbuffer x⟩) ∧
        (∃ hcenter : (N.sphereMark, s) ∈ neckBuffer δ,
          N'.center = N.chart ⟨(N.sphereMark, s), hcenter⟩) ∧
        |N'.scale / N.scale - 1| ≤ c * δ := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
