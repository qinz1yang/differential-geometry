import DifferentialGeometry.Topology.Simplex.TetrahedronSphere
import DifferentialGeometry.Topology.Simplex.SphereCollapse
import DifferentialGeometry.Topology.Simplex.TetrahedronCubeSphere
import DifferentialGeometry.Topology.Homotopy.SpherePrecomposition

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Simplex

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def tetrahedronSphereCollapse :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  tetrahedronSphereMap tetrahedronCubeSphereMap (Topology.cubeSphereBasepoint 2)
    tetrahedronCubeSphereMap_boundary

theorem tetrahedronSphereMap_eq_comp_tetrahedronSphereCollapse
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    tetrahedronSphereMap g x hg =
      (Topology.genLoopSphereHomeomorph 2 x (tetrahedronGenLoop g x hg)).val.comp
        tetrahedronSphereCollapse := by
  let f := (Topology.genLoopSphereHomeomorph 2 x (tetrahedronGenLoop g x hg)).val
  have hfg : f.comp tetrahedronCubeSphereMap = g :=
    genLoopSphereHomeomorph_tetrahedronGenLoop_comp g x hg
  have hfx : f (Topology.cubeSphereBasepoint 2) = x :=
    (Topology.genLoopSphereHomeomorph 2 x (tetrahedronGenLoop g x hg)).property
  have h := simplexSphereMap_natural tetrahedronCubeSphereMap (Topology.cubeSphereBasepoint 2)
    tetrahedronCubeSphereMap_boundary f
  simpa only [hfg, hfx, tetrahedronSphereCollapse, tetrahedronSphereMap] using h

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem tetrahedronSphereMap_class_eq_precompose
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    (Topology.homotopyGroupFreeSphereEquiv 2 x).symm
      (ZerothHomotopy.mk (tetrahedronSphereMap g x hg)) =
      Topology.homotopyGroupSpherePrecompose 2 x tetrahedronSphereCollapse
        (⟦tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) := by
  unfold Topology.homotopyGroupSpherePrecompose
  rw [Topology.homotopyGroupToFreeSphere_mk, Topology.freeSpherePrecompose_mk,
    tetrahedronSphereMap_eq_comp_tetrahedronSphereCollapse]

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

theorem tetrahedronSphereCollapse_homotopyEquiv :
    ∃ e : ContinuousMap.HomotopyEquiv
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
      e.toFun = tetrahedronSphereCollapse :=
  simplexSphereMap_homotopyEquiv_of_isQuotientMap tetrahedronCubeSphereMap
    (Topology.cubeSphereBasepoint 2) tetrahedronCubeSphereMap_boundary
    tetrahedronCubeSphereMap_isQuotientMap tetrahedronCubeSphereMap_fiber

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem homotopyGroupSpherePrecompose_tetrahedronSphereCollapse_bijective (x : X) :
    Function.Bijective (Topology.homotopyGroupSpherePrecompose 2 x tetrahedronSphereCollapse) := by
  obtain ⟨e, he⟩ := tetrahedronSphereCollapse_homotopyEquiv
  rw [← he]
  exact Topology.homotopyGroupSpherePrecompose_homotopyEquiv 2 x e

end DifferentialGeometry.Simplex
