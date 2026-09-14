import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeFrontier

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def HurewiczLowDegreeHypothesis (X : Type u) [TopologicalSpace X] : Prop :=
  (∀ x : X, IsSphereHurewiczIsomorphism 1 X x (integralLiftedSphereGenerator.{u} 1)) ∧
    ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x) →
      IsSphereHurewiczIsomorphism 2 X x (integralLiftedSphereGenerator.{u} 2)

theorem hurewiczLowDegreeHypothesis_iff_frontier [SimplyConnectedSpace X] :
    HurewiczLowDegreeHypothesis X ↔ HurewiczLowDegreeFrontier X :=
  Iff.rfl

theorem hurewiczLowDegreeHypothesis_iff_canonical_isomorphism [SimplyConnectedSpace X] :
    HurewiczLowDegreeHypothesis X ↔
      (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
        (_ : IsSphereHomologyGenerator 1 c), IsSphereHurewiczIsomorphism 1 X x c) ∧
      (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
        (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
        (_ : IsSphereHomologyGenerator 2 c), IsSphereHurewiczIsomorphism 2 X x c) :=
  (hurewiczLowDegreeHypothesis_iff_frontier (X := X)).trans
    hurewiczLowDegreeFrontier_iff_canonical_isomorphism

theorem hurewicz_two_isomorphism_of_hypothesis (h : HurewiczLowDegreeHypothesis X) (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 x hc (h.1 x)

theorem hurewicz_three_isomorphism_of_hypothesis (h : HurewiczLowDegreeHypothesis X) (x : X)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hc (h.2 x hπ₂)

theorem hurewiczLowDegreeHypothesis_of_subsingleton
    (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hH₂ : Subsingleton (integralSingularHomology 2 X))
    (hπ₃ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 3) X x))
    (hH₃ : Subsingleton (integralSingularHomology 3 X)) :
    HurewiczLowDegreeHypothesis X :=
  ⟨fun x => @IsSphereHurewiczIsomorphism.of_subsingleton X _ 1 x _ (hπ₂ x) hH₂,
    fun x _ => @IsSphereHurewiczIsomorphism.of_subsingleton X _ 2 x _ (hπ₃ x) hH₃⟩

theorem hurewiczLowDegreeHypothesis_punit : HurewiczLowDegreeHypothesis PUnit.{u + 1} :=
  (hurewiczLowDegreeHypothesis_iff_frontier (X := PUnit.{u + 1})).mpr
    hurewiczLowDegreeFrontier_punit

theorem isSphereHurewiczIsomorphism_zero_twoSphere
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ¬ IsSphereHurewiczIsomorphism 1 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x
      (0 : integralSingularHomology 2 (liftedHomotopySphere.{0} 1)) :=
  fun h => not_bijective_sphereHurewicz_zero_twoSphere x h.1

end DifferentialGeometry.Topology
