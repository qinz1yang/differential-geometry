import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeFrontier

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem sphereHurewiczTwoCanonical_iff_subsingleton_integralSingularHomology_two
    (x₀ : X) (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x)) :
    SphereHurewiczTwoCanonical X ↔ Subsingleton (integralSingularHomology 2 X) := by
  constructor
  · intro h
    exact @Function.Surjective.subsingleton (HomotopyGroup (Fin 2) X x₀)
      (integralSingularHomology 2 X)
      (sphereHurewicz 1 x₀ (integralLiftedSphereGenerator.{u} 1))
      (hπ₂ x₀) (h x₀).1.2
  · intro hH
    exact fun x => @IsSphereHurewiczIsomorphism.of_subsingleton X _ 1 x _
      (hπ₂ x) hH

theorem sphereHurewiczThreeCanonical_iff_subsingleton_integralSingularHomology_three
    (x₀ : X) (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hπ₃ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 3) X x)) :
    SphereHurewiczThreeCanonical X ↔ Subsingleton (integralSingularHomology 3 X) := by
  constructor
  · intro h
    exact @Function.Surjective.subsingleton (HomotopyGroup (Fin 3) X x₀)
      (integralSingularHomology 3 X)
      (sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2))
      (hπ₃ x₀) (h x₀ (hπ₂ x₀)).1.2
  · intro hH
    exact fun x _ => @IsSphereHurewiczIsomorphism.of_subsingleton X _ 2 x _
      (hπ₃ x) hH

theorem hurewicz_two_isomorphism_iff_subsingleton_homology_two_of_subsingleton
    (x₀ : X) (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x)) :
    (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
      (_ : IsSphereHomologyGenerator 1 c), IsSphereHurewiczIsomorphism 1 X x c) ↔
      Subsingleton (integralSingularHomology 2 X) :=
  (sphereHurewicz_two_isomorphism_iff_canonical_generator (X := X)).trans
    (sphereHurewiczTwoCanonical_iff_subsingleton_integralSingularHomology_two x₀ hπ₂)

theorem hurewicz_three_isomorphism_iff_subsingleton_homology_three_of_subsingleton
    (x₀ : X) (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hπ₃ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 3) X x)) :
    (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
      (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
      (_ : IsSphereHomologyGenerator 2 c), IsSphereHurewiczIsomorphism 2 X x c) ↔
      Subsingleton (integralSingularHomology 3 X) :=
  (sphereHurewicz_three_isomorphism_iff_canonical_generator (X := X)).trans
    (sphereHurewiczThreeCanonical_iff_subsingleton_integralSingularHomology_three
      x₀ hπ₂ hπ₃)

theorem hurewiczLowDegreeFrontier_iff_subsingleton_of_subsingleton_homotopyGroup
    (x₀ : X) (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hπ₃ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 3) X x)) :
    HurewiczLowDegreeFrontier X ↔
      Subsingleton (integralSingularHomology 2 X) ∧
        Subsingleton (integralSingularHomology 3 X) :=
  ⟨fun h => ⟨(sphereHurewiczTwoCanonical_iff_subsingleton_integralSingularHomology_two
      x₀ hπ₂).mp h.1,
    (sphereHurewiczThreeCanonical_iff_subsingleton_integralSingularHomology_three
      x₀ hπ₂ hπ₃).mp h.2⟩,
    fun h => ⟨(sphereHurewiczTwoCanonical_iff_subsingleton_integralSingularHomology_two
      x₀ hπ₂).mpr h.1,
    (sphereHurewiczThreeCanonical_iff_subsingleton_integralSingularHomology_three
      x₀ hπ₂ hπ₃).mpr h.2⟩⟩

theorem hurewicz_two_isomorphism_punit (x : PUnit.{u + 1})
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) PUnit.{u + 1} x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  hurewicz_two_isomorphism_of_lowDegreeFrontier hurewiczLowDegreeFrontier_punit x c hc

theorem hurewicz_three_isomorphism_punit (x : PUnit.{u + 1})
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) PUnit.{u + 1} x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) PUnit.{u + 1} x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  hurewicz_three_isomorphism_of_lowDegreeFrontier hurewiczLowDegreeFrontier_punit x hπ₂ c hc

theorem not_forall_bijective_sphereHurewicz_twoSphere :
    ¬ ∀ (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (c : integralSingularHomology 2 (liftedHomotopySphere.{0} 1)),
      Function.Bijective (sphereHurewicz 1 x c) := by
  intro h
  obtain ⟨x, hx⟩ :
      ∃ x : EuclideanSpace ℝ (Fin 3), x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)
  exact not_bijective_sphereHurewicz_zero_twoSphere ⟨x, hx⟩ (h ⟨x, hx⟩ 0)

end DifferentialGeometry.Topology
