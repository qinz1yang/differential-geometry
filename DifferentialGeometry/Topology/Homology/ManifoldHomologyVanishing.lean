import DifferentialGeometry.Topology.Homology.ManifoldCapDuality
import DifferentialGeometry.Topology.Homology.ManifoldHomologyGenerator
import DifferentialGeometry.Topology.Homology.CochainCones

noncomputable section

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace E X]
  [IsManifold 𝓘(ℝ, E) 1 X] [SimplyConnectedSpace X]

theorem integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank
    (m : ℕ) (hm : 1 + m = Module.finrank ℝ E) :
    Subsingleton (integralSingularHomology m X) := by
  let _ : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨a, _, ha⟩ := exists_integralSingularHomology_generator_of_simplyConnected (E := E) (M := X)
  have hex : ∃ a : integralSingularHomology (1 + m) X,
      ∀ p : X, Function.Bijective (fun z : ℤ =>
        z • integralAbsoluteToRelative (1 + m) ({p}ᶜ : Set X) a) := by
    rw [hm]
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  let _ := integralSingularCohomology_one_subsingleton (X := X)
  exact (integralSingularCohomologyCapProduct_bijective_of_chartedSpace_of_local_generators
    1 m hm a ha).surjective.subsingleton

theorem integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three
    (hE : Module.finrank ℝ E = 3) : Subsingleton (integralSingularHomology 2 X) :=
  integralSingularHomology_subsingleton_of_simplyConnected_of_one_add_eq_finrank 2 hE.symm

end DifferentialGeometry.Topology

end
