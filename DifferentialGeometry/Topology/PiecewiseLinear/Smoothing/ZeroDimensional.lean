import Mathlib.Geometry.Manifold.Instances.Real

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isManifold_zero {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) X] : IsManifold (𝓡 0) ∞ X := by
  have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
    (WithLp.equiv 2 (Fin 0 → ℝ)).subsingleton
  exact { compatible := fun _ _ =>
    mem_groupoid_of_pregroupoid.mpr ⟨contDiffOn_of_subsingleton, contDiffOn_of_subsingleton⟩ }

theorem exists_isManifold_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 0)) M,
      letI := C
      IsManifold (𝓡 0) ∞ M :=
  ⟨inferInstance, isManifold_zero⟩

end DifferentialGeometry.Topology.PiecewiseLinear
