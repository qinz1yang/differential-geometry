import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section ModelBridge

theorem isPLOn_iff_isPiecewiseAffineOn {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} : IsPLOn n m f s ↔ IsPiecewiseAffineOn f s := by
  have hchart : chartAt (EuclideanSpace ℝ (Fin m)) (0 : EuclideanSpace ℝ (Fin m)) =
      OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin m)) := chartAt_self_eq
  have he : OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin m)) ∈
      (plGroupoid m).maximalAtlas (EuclideanSpace ℝ (Fin m)) := by
    rw [← hchart]
    exact StructureGroupoid.chart_mem_maximalAtlas (plGroupoid m) 0
  have hmap : MapsTo f s (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin m))).source := by
    intro x _
    simp
  rw [isPLOn_iff_isPiecewiseAffineOn_comp_chart _ he hmap]
  exact ⟨fun h => h.congr fun _ _ => rfl, fun h => h.congr fun _ _ => rfl⟩

end ModelBridge

end DifferentialGeometry.Topology.PiecewiseLinear
