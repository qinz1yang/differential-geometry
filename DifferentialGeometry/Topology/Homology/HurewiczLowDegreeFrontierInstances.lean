import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeCriterion
import DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczTwoSphereGeneration_of_subsingleton (x : X)
    [Subsingleton (integralSingularHomology 2 X)] : HurewiczTwoSphereGeneration X :=
  fun _ => ⟨ContinuousMap.const _ x, Subsingleton.elim _ _⟩

theorem hurewiczThreeSphereGeneration_of_subsingleton (x : X)
    [Subsingleton (integralSingularHomology 3 X)] : HurewiczThreeSphereGeneration X :=
  fun _ => ⟨ContinuousMap.const _ x, Subsingleton.elim _ _⟩

theorem hurewiczTwoSphereNullhomotopic_of_subsingleton_homotopyGroup [PathConnectedSpace X]
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] : HurewiczTwoSphereNullhomotopic X := by
  intro f _
  obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective 1 x (ZerothHomotopy.mk f)
  refine (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x f).mp ?_
  rw [← ha, Subsingleton.elim a 1, homotopyGroupToFreeSphere_one]

theorem hurewiczThreeSphereNullhomotopic_of_subsingleton_homotopyGroup [PathConnectedSpace X]
    (x : X) [Subsingleton (HomotopyGroup (Fin 3) X x)] : HurewiczThreeSphereNullhomotopic X := by
  intro f _
  obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective 2 x (ZerothHomotopy.mk f)
  refine (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f).mp ?_
  rw [← ha, Subsingleton.elim a 1, homotopyGroupToFreeSphere_one]

theorem hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator
    (h : IsSphereHomologyGenerator 1 squareSphereFundamentalClass.{u}) :
    HurewiczTwoMultiplicative X :=
  fun x c hc a b => hurewicz_two_mul x h c hc a b

theorem hurewicz_two_isomorphism_of_squareSphereFundamentalClass_sphereCriterion
    [SimplyConnectedSpace X] (x₀ : X)
    (hsq : IsSphereHomologyGenerator 1 squareSphereFundamentalClass.{u})
    (hgen : HurewiczTwoSphereGeneration X) (hnull : HurewiczTwoSphereNullhomotopic X)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  hurewicz_two_isomorphism_of_sphereCriterion x₀
    (hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator hsq) hgen hnull x c hc

theorem hurewicz_two_isomorphism_of_subsingleton_homotopyGroup_of_sphereGeneration
    [SimplyConnectedSpace X] (hπ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hgen : HurewiczTwoSphereGeneration X)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1)) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b := by
  have hzero : ∀ y : integralSingularHomology 2 X, y = 0 := by
    intro y
    obtain ⟨f, hf⟩ := hgen y
    obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective 1 x (ZerothHomotopy.mk f)
    rw [← hf, ← ha]
    exact (congrArg (sphereHurewicz 1 x (integralLiftedSphereGenerator.{u} 1))
      (Subsingleton.elim a 1)).trans (sphereHurewicz_one 1 x _)
  refine ⟨⟨fun a b _ => @Subsingleton.elim _ (hπ x) a b,
    fun y => ⟨1, (sphereHurewicz_one 1 x c).trans (hzero y).symm⟩⟩,
    fun a b => (hzero _).trans (hzero _).symm⟩

theorem hurewicz_three_isomorphism_of_subsingleton_homotopyGroup_of_sphereGeneration
    [SimplyConnectedSpace X] (hπ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 3) X x))
    (hgen : HurewiczThreeSphereGeneration X)
    (x : X) (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2)) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  have hzero : ∀ y : integralSingularHomology 3 X, y = 0 := by
    intro y
    obtain ⟨f, hf⟩ := hgen y
    obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective 2 x (ZerothHomotopy.mk f)
    rw [← hf, ← ha]
    exact (congrArg (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2))
      (Subsingleton.elim a 1)).trans (sphereHurewicz_one 2 x _)
  refine ⟨⟨fun a b _ => @Subsingleton.elim _ (hπ x) a b,
    fun y => ⟨1, (sphereHurewicz_one 2 x c).trans (hzero y).symm⟩⟩,
    fun a b => (hzero _).trans (hzero _).symm⟩

end DifferentialGeometry.Topology
