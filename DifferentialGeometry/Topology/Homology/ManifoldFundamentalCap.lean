import DifferentialGeometry.Topology.Homology.ManifoldHomologyGenerator
import DifferentialGeometry.Topology.Homology.ManifoldLocalCapDuality

noncomputable section

open CategoryTheory Module Set
open scoped Manifold

universe u

namespace DifferentialGeometry.Topology

theorem exists_integralSingularHomology_generator_with_local_cap_bijections_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ a : integralSingularHomology (finrank ℝ E) M,
      Function.Bijective (fun z : ℤ => z • a) ∧
      ∀ x : M,
        Function.Bijective (fun z : ℤ =>
          z • integralAbsoluteToRelative (finrank ℝ E) ({x}ᶜ : Set M) a) ∧
        Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E) ({x}ᶜ : Set M) =>
          integralRelativeCohomologyCapToAbsolute ({x}ᶜ : Set M) (finrank ℝ E) 0 α
            (integralAbsoluteToRelative (finrank ℝ E) ({x}ᶜ : Set M) a)) := by
  obtain ⟨a, ha, hpoints⟩ :=
    exists_integralSingularHomology_generator_of_simplyConnected (E := E) (M := M)
  refine ⟨a, ha, ?_⟩
  intro x
  exact ⟨hpoints x,
    integralManifoldLocalHomology_cap_bijective_of_generator (E := E) x _ (hpoints x)⟩

end DifferentialGeometry.Topology
