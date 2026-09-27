import DifferentialGeometry.Topology.Homology.ConeSpherePairing
import DifferentialGeometry.Topology.Simplex.TriangleSphereCollapse

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def integralSingularTriangleSphereClass (x : X) (σ : integralSingularSimplex 2 X) :
    HomotopyGroup (Fin 2) X x :=
  Function.invFun
    (homotopyGroupSpherePrecompose 1 x Simplex.triangleSphereCollapse)
    (integralSingularConeSphereClass x σ)

theorem homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass
    (x : X) (σ : integralSingularSimplex 2 X) :
    homotopyGroupSpherePrecompose 1 x Simplex.triangleSphereCollapse
      (integralSingularTriangleSphereClass x σ) =
        integralSingularConeSphereClass x σ :=
  Function.rightInverse_invFun
    (Simplex.homotopyGroupSpherePrecompose_triangleSphereCollapse_bijective x).surjective _

theorem integralSingularTriangleSphereClass_eq_triangleGenLoop
    (x : X) (σ : integralSingularSimplex 2 X)
    (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x)
    (h : (integralSingularConeSphereMap x σ).Homotopic
      (Simplex.triangleSphereMap g x hg)) :
    integralSingularTriangleSphereClass x σ =
      (⟦Simplex.triangleGenLoop g x hg⟧ : HomotopyGroup (Fin 2) X x) := by
  apply (Simplex.homotopyGroupSpherePrecompose_triangleSphereCollapse_bijective x).injective
  rw [homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass,
    ← Simplex.triangleSphereMap_class_eq_precompose]
  apply congrArg (homotopyGroupFreeSphereEquiv 1 x).symm
  exact Quotient.sound ((homotopic_iff_joined _ _).mp h)

end DifferentialGeometry.Topology
