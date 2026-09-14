import DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier

noncomputable section

universe u

namespace DifferentialGeometry.Topology

def HurewiczLowDegreeFrontier (X : Type u) [TopologicalSpace X]
    [SimplyConnectedSpace X] : Prop :=
  SphereHurewiczTwoCanonical X ∧ SphereHurewiczThreeCanonical X

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem hurewiczLowDegreeFrontier_iff_canonical_isomorphism :
    HurewiczLowDegreeFrontier X ↔
      (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
        (_ : IsSphereHomologyGenerator 1 c), IsSphereHurewiczIsomorphism 1 X x c) ∧
      (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
        (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
        (_ : IsSphereHomologyGenerator 2 c), IsSphereHurewiczIsomorphism 2 X x c) :=
  ⟨fun h => ⟨(sphereHurewicz_two_isomorphism_iff_canonical_generator (X := X)).mpr h.1,
      (sphereHurewicz_three_isomorphism_iff_canonical_generator (X := X)).mpr h.2⟩,
    fun h => ⟨(sphereHurewicz_two_isomorphism_iff_canonical_generator (X := X)).mp h.1,
      (sphereHurewicz_three_isomorphism_iff_canonical_generator (X := X)).mp h.2⟩⟩

theorem hurewicz_two_isomorphism_of_lowDegreeFrontier (h : HurewiczLowDegreeFrontier X)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  sphereHurewicz_two_isomorphism_of_canonical_generator h.1 x c hc

theorem hurewicz_three_isomorphism_of_lowDegreeFrontier (h : HurewiczLowDegreeFrontier X)
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  sphereHurewicz_three_isomorphism_of_canonical_generator h.2 x hπ₂ c hc

theorem hurewiczLowDegreeFrontier_of_subsingleton
    (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hH₂ : Subsingleton (integralSingularHomology 2 X))
    (hπ₃ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 3) X x))
    (hH₃ : Subsingleton (integralSingularHomology 3 X)) :
    HurewiczLowDegreeFrontier X :=
  ⟨fun x => @IsSphereHurewiczIsomorphism.of_subsingleton X _ 1 x _ (hπ₂ x) hH₂,
    fun x _ => @IsSphereHurewiczIsomorphism.of_subsingleton X _ 2 x _ (hπ₃ x) hH₃⟩

theorem hurewiczLowDegreeFrontier_punit : HurewiczLowDegreeFrontier PUnit.{u + 1} :=
  ⟨sphereHurewiczTwoCanonical_punit, sphereHurewiczThreeCanonical_punit⟩

theorem not_bijective_sphereHurewicz_zero_twoSphere
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ¬ Function.Bijective (sphereHurewicz 1 x
      (0 : integralSingularHomology 2 (liftedHomotopySphere.{0} 1))) :=
  fun h => not_surjective_sphereHurewicz_zero_twoSphere x h.2

end DifferentialGeometry.Topology
