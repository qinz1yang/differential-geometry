import DifferentialGeometry.Topology.Circle.GermExtension

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 1 + 1)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

omit [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
theorem exists_disk_chart_eqOn_circle_neighborhood
    (φ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hφ : closedBall (0 : E) 1 ⊆ φ.source) (hψ : sphere (0 : E) 1 ⊆ ψ.source)
    (hboundary : φ '' sphere (0 : E) 1 = ψ '' sphere (0 : E) 1)
    (hside : MapsTo ψ (closedBall (0 : E) 1 ∩ ψ.source) (φ '' closedBall (0 : E) 1)) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      closedBall (0 : E) 1 ⊆ χ.source ∧ χ '' closedBall (0 : E) 1 = φ '' closedBall (0 : E) 1 ∧
      ∃ V : Set E, IsOpen V ∧ sphere (0 : E) 1 ⊆ V ∧ V ⊆ ψ.source ∧ EqOn χ ψ V := by
  let G := ψ.trans φ.symm
  have hSG : sphere (0 : E) 1 ⊆ G.source := by
    intro x hx
    refine ⟨hψ hx, ?_⟩
    have hm : ψ x ∈ φ '' sphere (0 : E) 1 := hboundary.symm ▸ mem_image_of_mem ψ hx
    obtain ⟨y, hy, hyeq⟩ := hm
    change ψ x ∈ φ.target
    rw [← hyeq]
    exact φ.map_source (hφ (sphere_subset_closedBall hy))
  have hGboundary : MapsTo G (sphere (0 : E) 1) (sphere (0 : E) 1) := by
    intro x hx
    have hm : ψ x ∈ φ '' sphere (0 : E) 1 := hboundary.symm ▸ mem_image_of_mem ψ hx
    obtain ⟨y, hy, hyeq⟩ := hm
    change φ.symm (ψ x) ∈ sphere (0 : E) 1
    rw [← hyeq, show φ.symm (φ y) = y from φ.left_inv (hφ (sphere_subset_closedBall hy))]
    exact hy
  have hGside : MapsTo G (closedBall (0 : E) 1 ∩ G.source) (closedBall (0 : E) 1) := by
    intro x hx
    obtain ⟨y, hy, hyeq⟩ := hside ⟨hx.1, hx.2.1⟩
    change φ.symm (ψ x) ∈ closedBall (0 : E) 1
    rw [← hyeq, show φ.symm (φ y) = y from φ.left_inv (hφ hy)]
    exact hy
  obtain ⟨D, hDball, V, hV, hSV, hVG, hD⟩ :=
    G.exists_diffeomorph_eqOn_circle_neighborhood hSG hGboundary hGside
  let χ := D.toPartialDiffeomorph.trans φ
  refine ⟨χ, ?_, ?_, V, hV, hSV, fun x hx => (hVG hx).1, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hφ (hDball.subset ⟨x, hx, rfl⟩)⟩
  · rw [show (χ : E → M) = φ ∘ D from rfl, image_comp, hDball]
  · intro x hx
    change φ (D x) = ψ x
    rw [hD hx]
    exact φ.right_inv (hVG hx).2

end PartialDiffeomorph
