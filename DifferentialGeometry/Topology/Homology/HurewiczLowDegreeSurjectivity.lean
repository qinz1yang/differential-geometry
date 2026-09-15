import DifferentialGeometry.Topology.Homology.TwoCycleRealization
import DifferentialGeometry.Topology.Homology.ThreeCycleRealization
import DifferentialGeometry.Topology.Homology.CubeSphereGenerator
import DifferentialGeometry.Topology.Homology.HurewiczTwoAdditivity
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem surjective_sphereHurewicz_of_span (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b)
    (hspan : Submodule.span ℤ (Set.range (sphereHurewicz n x c)) = ⊤) :
    Function.Surjective (sphereHurewicz n x c) := by
  intro y
  have hy : y ∈ Submodule.span ℤ (Set.range (sphereHurewicz n x c)) := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    exact hz
  · exact ⟨1, sphereHurewicz_one n x c⟩
  · intro z w _ _ hz hw
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨b, rfl⟩ := hw
    exact ⟨a * b, hmul a b⟩
  · intro k z _ hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨a ^ k, (sphereHurewicz_zpow_of_additive n x c hmul a k).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (integralSingularHomology (n + 1) X))
        k (sphereHurewicz n x c a)).symm⟩

theorem surjective_sphereHurewicz_two [SimplyConnectedSpace X] (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Surjective (sphereHurewicz 1 x c) :=
  surjective_sphereHurewicz_of_span 1 x c (sphereHurewicz_two_mul x c)
    (span_range_sphereHurewicz_two x c hc)

theorem surjective_sphereHurewicz_three [SimplyConnectedSpace X]
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Surjective (sphereHurewicz 2 x c) :=
  surjective_sphereHurewicz_of_span 2 x c (sphereHurewicz_three_mul x c)
    (span_range_sphereHurewicz_three x c hc)

end DifferentialGeometry.Topology
