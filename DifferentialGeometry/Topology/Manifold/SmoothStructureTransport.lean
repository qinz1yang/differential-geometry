import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Geometry.Manifold.Instances.Sphere

namespace DifferentialGeometry.Topology

open scoped _root_.Manifold ContDiff
open Metric Set

noncomputable section

theorem exists_manifold_structure_of_homeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (r : ℕ∞ω)
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I r N] (h : M ≃ₜ N) :
    ∃ cs : ChartedSpace H M, @IsManifold 𝕜 _ E _ _ H _ I r M _ cs := by
  refine ⟨DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace h, ?_⟩
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := I) (n := r) h

theorem exists_smooth_structure_of_homeomorph_sphere {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    (h : M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) ∞ M _
        cs :=
  exists_manifold_structure_of_homeomorph (𝓡 n) ∞ h

end

end DifferentialGeometry.Topology
