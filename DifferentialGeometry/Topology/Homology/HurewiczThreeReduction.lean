import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeCriterion

noncomputable section

open ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczThreeSphereGeneration_of_exists [SimplyConnectedSpace X] (x : X)
    (hmul : ∀ a b : HomotopyGroup (Fin 3) X x,
      sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) b)
    (a₀ : HomotopyGroup (Fin 3) X x)
    (z₀ : integralSingularHomology 3 X)
    (ha₀ : sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) a₀ = z₀)
    (hgen : ∀ y : integralSingularHomology 3 X, ∃ k : ℤ, y = k • z₀) :
    HurewiczThreeSphereGeneration X := by
  intro y
  obtain ⟨k, hk⟩ := hgen y
  refine ⟨Quotient.out (homotopyGroupToFreeSphere 2 x (a₀ ^ k)), ?_⟩
  have hout : ZerothHomotopy.mk (Quotient.out (homotopyGroupToFreeSphere 2 x (a₀ ^ k))) =
      homotopyGroupToFreeSphere 2 x (a₀ ^ k) := Quotient.out_eq _
  rw [hout]
  change sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) (a₀ ^ k) = y
  rw [sphereHurewicz_zpow_of_additive (X := X) 2 x (integralLiftedSphereGenerator.{u} 2)
      hmul a₀ k,
    ha₀, hk]

def HurewiczThreeHypothesis (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x) →
    Function.Bijective
      (sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2)) ∧
    ∀ a b : HomotopyGroup (Fin 3) X x,
      sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz (X := X) 2 x (integralLiftedSphereGenerator.{u} 2) b

theorem hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical [SimplyConnectedSpace X]
    (h : SphereHurewiczThreeCanonical X) : HurewiczThreeHypothesis X :=
  fun x hπ => h x hπ

theorem hurewiczThreeHypothesis_punit : HurewiczThreeHypothesis PUnit.{u + 1} :=
  hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical sphereHurewiczThreeCanonical_punit

theorem sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis [SimplyConnectedSpace X]
    (h : HurewiczThreeHypothesis X) :
    SphereHurewiczThreeCanonical X :=
  fun x hπ => h x hπ

theorem hurewiczThreeHypothesis_iff_sphereHurewiczThreeCanonical [SimplyConnectedSpace X] :
    HurewiczThreeHypothesis X ↔ SphereHurewiczThreeCanonical X :=
  ⟨fun h => sphereHurewiczThreeCanonical_of_hurewiczThreeHypothesis h,
    hurewiczThreeHypothesis_of_sphereHurewiczThreeCanonical⟩

end DifferentialGeometry.Topology
