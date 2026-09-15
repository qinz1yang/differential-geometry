import DifferentialGeometry.Topology.Homology.ConeThreeSpherePairing
import DifferentialGeometry.Topology.Simplex.TetrahedronSphereCollapse

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def integralSingularTetrahedronSphereClass (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (σ : integralSingularSimplex 3 X) :
    HomotopyGroup (Fin 3) X x :=
  Function.invFun
    (homotopyGroupSpherePrecompose 2 x Simplex.tetrahedronSphereCollapse)
    (integralSingularConeThreeSphereClass x σ)

theorem homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (σ : integralSingularSimplex 3 X) :
    homotopyGroupSpherePrecompose 2 x Simplex.tetrahedronSphereCollapse
      (integralSingularTetrahedronSphereClass x σ) =
        integralSingularConeThreeSphereClass x σ :=
  Function.rightInverse_invFun
    (Simplex.homotopyGroupSpherePrecompose_tetrahedronSphereCollapse_bijective x).surjective _

theorem integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (σ : integralSingularSimplex 3 X)
    (g : C(stdSimplex ℝ (Fin 4), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x)
    (h : (integralSingularConeThreeSphereMap x σ).Homotopic
      (Simplex.tetrahedronSphereMap g x hg)) :
    integralSingularTetrahedronSphereClass x σ =
      (⟦Simplex.tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) := by
  apply (Simplex.homotopyGroupSpherePrecompose_tetrahedronSphereCollapse_bijective x).injective
  rw [homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass,
    ← Simplex.tetrahedronSphereMap_class_eq_precompose]
  apply congrArg (homotopyGroupFreeSphereEquiv 2 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp h)

end DifferentialGeometry.Topology
