import DifferentialGeometry.Topology.Homology.TetrahedronSphereRelation

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

omit [SimplyConnectedSpace X] in
private theorem constant_simplex_face (n : ℕ) (x : X) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i
      ((integralSingularSimplexEquiv (n + 1) X).symm (ContinuousMap.const _ x)) =
      (integralSingularSimplexEquiv n X).symm (ContinuousMap.const _ x) := by
  apply (integralSingularSimplexEquiv n X).injective
  ext p
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i
      ((integralSingularSimplexEquiv (n + 1) X).symm (ContinuousMap.const _ x))) p = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

theorem integralSingularTetrahedronSphereClass_const
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    integralSingularTetrahedronSphereClass x
      ((integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x)) = 1 := by
  have h := integralSingularTetrahedronSphereClass_face_relation x
    ((integralSingularSimplexEquiv 4 X).symm (ContinuousMap.const _ x))
  simp only [constant_simplex_face] at h
  exact (mul_eq_left.mp h)

theorem integralSingularConeThreeSphereClass_const
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    integralSingularConeThreeSphereClass x
      ((integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x)) = 1 := by
  rw [← homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass,
    integralSingularTetrahedronSphereClass_const, homotopyGroupSpherePrecompose_one]

theorem integralSingularConeThreeSphereMap_const_homotopic
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    (integralSingularConeThreeSphereMap x
      ((integralSingularSimplexEquiv 3 X).symm (ContinuousMap.const _ x))).Homotopic
      (ContinuousMap.const _ x) := by
  have h := congrArg (homotopyGroupFreeSphereEquiv 2 x)
    (integralSingularConeThreeSphereClass_const x)
  change (homotopyGroupFreeSphereEquiv 2 x) ((homotopyGroupFreeSphereEquiv 2 x).symm _) =
    homotopyGroupToFreeSphere 2 x 1 at h
  rw [Equiv.apply_symm_apply, homotopyGroupToFreeSphere_one] at h
  exact (homotopic_iff_joined _ _).mpr (Quotient.exact h)

end DifferentialGeometry.Topology
