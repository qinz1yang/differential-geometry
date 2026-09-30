import DifferentialGeometry.Topology.Double.Rounded.RoundedDouble
import DifferentialGeometry.Topology.Manifold.GeneralPosition.ChartDiskComplement
import DifferentialGeometry.Topology.Homology.Punctures.PuncturedFilling

namespace DifferentialGeometry.Topology.RoundedDouble

open Set
open scoped ContinuousMap

universe u

variable {X : Type u} [TopologicalSpace X]

theorem simplyConnectedSpace_filling (g : X → ℝ) [SimplyConnectedSpace (base g)] :
    SimplyConnectedSpace (filling g) :=
  (homotopyEquivBase g).simplyConnectedSpace

theorem acyclic_filling (R : ModuleCat.{u} ℤ) (g : X → ℝ)
    (h : SingularPair.acyclic R (TopCat.of (base g))) :
    SingularPair.acyclic R (TopCat.of (filling g)) :=
  SingularPair.acyclic.of_homotopyEquiv R (homotopyEquivBase g) h

theorem punctured_filling_hcobordism_input [T2Space X] {d : ℕ} (hd : 3 ≤ d)
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) (X × ℝ)]
    (g : X → ℝ) [SimplyConnectedSpace (base g)]
    (hacyclic : SingularPair.acyclic SingularPair.integerCoefficients.{u} (TopCat.of (base g)))
    {e : Disk d → X × ℝ} (he : isChartDisk e) (hD : range e ⊆ filling g) :
    SimplyConnectedSpace (filling g \ e '' diskInterior d : Set (X × ℝ)) ∧
      relHomologyVanishes (filling g \ e '' diskInterior d : Set (X × ℝ))
        (Subtype.val ⁻¹' (e '' diskSphere d)) := by
  have hB : IsSimplyConnected (filling g) := simplyConnectedSpace_filling g
  exact ⟨isSimplyConnected_sdiff_chartDisk hd he hD hB,
    SingularPair.relHomologyVanishes_puncturedFilling he hD
      (acyclic_filling SingularPair.integerCoefficients g hacyclic)⟩

end DifferentialGeometry.Topology.RoundedDouble
