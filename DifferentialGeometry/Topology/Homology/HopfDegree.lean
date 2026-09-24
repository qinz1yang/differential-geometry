import DifferentialGeometry.Topology.Homology.HurewiczEquivalences
import DifferentialGeometry.Topology.Homology.HurewiczHopfHalf

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem bijective_freeSphereDegree_three :
    Function.Bijective (freeSphereDegree.{u} 2) := by
  let x : liftedHomotopySphere.{u} 2 := ULift.up (cubeSphereBasepoint 2)
  let : Subsingleton (integralSingularHomology 2 (liftedHomotopySphere.{u} 2)) :=
    subsingleton_integralSingularHomology_two_liftedHomotopySphere_two
  let : Subsingleton (HomotopyGroup (Fin 2) (liftedHomotopySphere.{u} 2) x) :=
    homotopyTwo_subsingleton_of_homologyTwo x
  have h := (bijective_sphereHurewicz_iff_bijective_freeSphereHomologyImage 2 x
    (integralLiftedSphereGenerator.{u} 2)).mp
      (bijective_sphereHurewicz_three x (integralLiftedSphereGenerator.{u} 2)
        (integralLiftedSphereGenerator_isGenerator 2))
  exact (integralLiftedSphereTopEquiv.{u} 2).bijective.comp h

theorem homotopic_iff_freeSphereDegree_three_eq
    {f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, liftedHomotopySphere.{u} 2)} :
    f.Homotopic g ↔ freeSphereDegree.{u} 2 (ZerothHomotopy.mk f) =
      freeSphereDegree.{u} 2 (ZerothHomotopy.mk g) := by
  refine ⟨freeSphereDegree_eq_of_homotopic 2, fun h => ?_⟩
  exact (homotopic_iff_joined f g).mpr
    (Quotient.exact (bijective_freeSphereDegree_three.injective h))

theorem exists_sphereMap_freeSphereDegree_three_eq (k : ℤ) :
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, liftedHomotopySphere.{u} 2),
      freeSphereDegree.{u} 2 (ZerothHomotopy.mk f) = k := by
  obtain ⟨a, ha⟩ := bijective_freeSphereDegree_three.surjective k
  have hout : ZerothHomotopy.mk (Quotient.out a) = a := Quotient.out_eq a
  exact ⟨Quotient.out a, by rw [hout]; exact ha⟩

theorem nullhomotopic_iff_freeSphereDegree_three_eq_zero
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, liftedHomotopySphere.{u} 2)} :
    f.Nullhomotopic ↔ freeSphereDegree.{u} 2 (ZerothHomotopy.mk f) = 0 := by
  let x : liftedHomotopySphere.{u} 2 := ULift.up (cubeSphereBasepoint 2)
  rw [← zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f]
  exact ⟨fun h => by rw [h, freeSphereDegree_const], fun h =>
    bijective_freeSphereDegree_three.injective (h.trans (freeSphereDegree_const 2 x).symm)⟩

theorem exists_continuous_closedBall_iff_freeSphereDegree_three_eq_zero
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, liftedHomotopySphere.{u} 2)} :
    (∃ F : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1,
      liftedHomotopySphere.{u} 2),
        F.comp (ContinuousMap.inclusion Metric.sphere_subset_closedBall) = f) ↔
          freeSphereDegree.{u} 2 (ZerothHomotopy.mk f) = 0 :=
  (nullhomotopic_iff_exists_continuous_closedBall (by norm_num) f).symm.trans
    (nullhomotopic_iff_freeSphereDegree_three_eq_zero (f := f))

end DifferentialGeometry.Topology
