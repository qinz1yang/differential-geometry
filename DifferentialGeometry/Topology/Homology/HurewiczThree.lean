import DifferentialGeometry.Topology.Homology.TetrahedronSphereChain
import DifferentialGeometry.Topology.Homology.TetrahedronSphereHomologyInverse
import DifferentialGeometry.Topology.Simplex.TetrahedronGenLoopRepresentation
import DifferentialGeometry.Topology.Homology.TetrahedronSphereIdentification
import DifferentialGeometry.Topology.Homology.SimplexBoundarySphereGenerator
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem sphereHurewicz_tetrahedronGenLoop
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    sphereHurewicz 2 x tetrahedronSphereFundamentalClass
      (⟦Simplex.tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) =
        integralSingularCycleClass 2 X (integralSingularTetrahedronCycle g x hg) := by
  let a : HomotopyGroup (Fin 3) X x := ⟦Simplex.tetrahedronGenLoop g x hg⟧
  have h := sphereHurewicz_precompose 2 x Simplex.tetrahedronSphereCollapse
    (simplexBoundarySphereClass.{u} 2) a
  change sphereHurewicz 2 x tetrahedronSphereFundamentalClass a = _ at h
  rw [h]
  have he := Simplex.tetrahedronSphereMap_class_eq_precompose g x hg
  change (homotopyGroupFreeSphereEquiv 2 x).symm
    (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)) =
      homotopyGroupSpherePrecompose 2 x Simplex.tetrahedronSphereCollapse a at he
  rw [← he]
  change freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
    ((homotopyGroupFreeSphereEquiv 2 x) ((homotopyGroupFreeSphereEquiv 2 x).symm
      (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)))) = _
  rw [Equiv.apply_symm_apply, tetrahedronSphereMap_simplexBoundarySphereClass]

theorem isSphereHomologyGenerator_tetrahedronSphereFundamentalClass :
    IsSphereHomologyGenerator 2 tetrahedronSphereFundamentalClass.{u} := by
  obtain ⟨e, he⟩ := Simplex.tetrahedronSphereCollapse_homotopyEquiv
  have h := isSphereHomologyGenerator_liftedHomotopySphereMap 2 e
    isSphereHomologyGenerator_simplexBoundarySphereClass_three
  simpa only [he, tetrahedronSphereFundamentalClass] using h

variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

theorem integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz
    (a : HomotopyGroup (Fin 3) X x) :
    integralSingularTetrahedronSphereHomologyPairing x
      (sphereHurewicz 2 x tetrahedronSphereFundamentalClass a) = Additive.ofMul a := by
  obtain ⟨g, hg, rfl⟩ := Simplex.exists_tetrahedronGenLoop_class_eq a
  rw [sphereHurewicz_tetrahedronGenLoop, integralSingularTetrahedronSphereHomologyPairing_cycle,
    integralSingularTetrahedronCycle_val, integralSingularTetrahedronSpherePairing_simplex,
    integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop_of_boundary]

theorem bijective_sphereHurewicz_tetrahedronSphereFundamentalClass :
    Function.Bijective (sphereHurewicz 2 x tetrahedronSphereFundamentalClass) := by
  constructor
  · intro a b h
    have h' := congrArg (integralSingularTetrahedronSphereHomologyPairing x) h
    rw [integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz,
      integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz] at h'
    exact h'
  · intro y
    exact ⟨(integralSingularTetrahedronSphereHomologyPairing x y).toMul,
      sphereHurewicz_integralSingularTetrahedronSphereHomologyPairing x y⟩

theorem bijective_sphereHurewicz_three
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) := by
  apply (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 x c hc).mpr
  exact (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 x
    tetrahedronSphereFundamentalClass isSphereHomologyGenerator_tetrahedronSphereFundamentalClass).mp
      (bijective_sphereHurewicz_tetrahedronSphereFundamentalClass x)

end DifferentialGeometry.Topology
