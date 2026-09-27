import DifferentialGeometry.Topology.Manifold.BallChartScale
import DifferentialGeometry.Topology.Manifold.AffineBallIsotopy

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

theorem ballChartIsotopic_of_modelIsotopy {M : Type*} [TopologicalSpace M]
    [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (c c' : BallChart 3 (𝓡 3) M)
    (hover : ∀ x ∈ Metric.closedBall (0 : E₃) 2, c.chart x ∈ c'.chart.target)
    (D : ℝ → Diffeomorph 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) E₃ E₃ ∞)
    (hDc : ContDiff ℝ ∞ (fun q : ℝ × E₃ => D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : ℝ × E₃ => (D q.1).symm q.2))
    (hD0 : D 0 = Diffeomorph.refl 𝓘(ℝ, E₃) E₃ ∞)
    {K : Set E₃} (hK : IsCompact K) (hKt : K ⊆ c'.chart.source)
    (hfix : ∀ t z, z ∉ K → D t z = z ∧ (D t).symm z = z)
    (hact : ∀ x ∈ Metric.closedBall (0 : E₃) 2, D 1 (c'.chart.symm (c.chart x)) = x) :
    BallChartIsotopic c c' := by
  obtain ⟨J, hJ, hJi, hJe, -, -, -⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family (P := ℝ)
      c'.chart.symm.toOpenPartialHomeomorph c'.chart.contMDiffOn_invFun
      c'.chart.contMDiffOn_toFun D hDc hDi hK hKt hfix
  refine ⟨J, hJ, hJi, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro y
    rw [(hJe 0 y).1]
    by_cases hy : y ∈ c'.chart.symm.toOpenPartialHomeomorph.source
    · have h1 : extendChartById c'.chart.symm.toOpenPartialHomeomorph (D 0) y
          = c'.chart.symm.toOpenPartialHomeomorph.symm
            (c'.chart.symm.toOpenPartialHomeomorph y) := by
        rw [extendChartById, if_pos hy, hD0]
        rfl
      rw [h1, OpenPartialHomeomorph.left_inv _ hy]
      simp only [Diffeomorph.coe_refl, id_eq]
    · rw [extendChartById, if_neg hy]
      simp only [Diffeomorph.coe_refl, id_eq]
  · intro x hx
    rw [(hJe 1 (c.chart x)).1, extendChartById_chartSymm_of_target c' (D 1) (hover x hx),
      hact x hx]

end DifferentialGeometry.Topology.Manifold
