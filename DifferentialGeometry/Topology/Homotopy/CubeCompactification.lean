import DifferentialGeometry.Topology.Homotopy.CubeInterior
import DifferentialGeometry.Topology.Homotopy.CollapseMaps
import DifferentialGeometry.Topology.Homotopy.BasedMappingSpace
import Mathlib.Topology.Compactification.OnePoint.Sphere







noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X]



def genLoopCollapseConstantHomeomorph (x : X) :
    GenLoop N X x ≃ₜ collapseConstantMaps (cubeInterior N) x where
  toFun p := ⟨p.val, fun t ht => GenLoop.boundary p t (by
    simpa only [cubeInterior_eq_compl_boundary, mem_compl_iff, not_not] using ht)⟩
  invFun f := ⟨f.val, fun t ht => f.property t (by
    simpa only [cubeInterior_eq_compl_boundary, mem_compl_iff, not_not] using ht)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _



def genLoopCompactificationHomeomorph [Finite N] [Nonempty N] (x : X) :
    GenLoop N X x ≃ₜ basedOnePointMaps (cubeInterior N) x :=
  (genLoopCollapseConstantHomeomorph x).trans
    (collapseMapsHomeomorph (cubeInterior N) (isOpen_cubeInterior N)
      (cubeInterior_compl_nonempty N) x)



def cubeInteriorSphereHomeomorph (n : ℕ) :
    OnePoint (cubeInterior (Fin (n + 1))) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  (euclideanCubeInteriorHomeomorph (Fin (n + 1))).symm.onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := Fin (n + 1) → ℝ) (ι := Fin (n + 2)) (by simp))


def cubeSphereBasepoint (n : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  cubeInteriorSphereHomeomorph n OnePoint.infty



def genLoopSphereHomeomorph (n : ℕ) (x : X) :
    GenLoop (Fin (n + 1)) X x ≃ₜ basedMappingSpace (cubeSphereBasepoint n) x :=
  (genLoopCompactificationHomeomorph x).trans
    (basedMappingSpaceDomainHomeomorph (cubeInteriorSphereHomeomorph n).symm
      (cubeSphereBasepoint n) OnePoint.infty
      ((cubeInteriorSphereHomeomorph n).symm_apply_apply OnePoint.infty) x)



theorem genLoopSphereHomeomorph_homotopic_iff (n : ℕ) (x : X)
    (p q : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n x p).val.HomotopicRel
      (genLoopSphereHomeomorph n x q).val {cubeSphereBasepoint n} ↔ GenLoop.Homotopic p q := by
  rw [← basedMappingSpace_joined_iff, genLoop_homotopic_iff_joined]
  constructor
  · intro h
    simpa only [Homeomorph.symm_apply_apply] using
      h.map (genLoopSphereHomeomorph n x).symm.continuous
  · exact fun h => h.map (genLoopSphereHomeomorph n x).continuous

end DifferentialGeometry.Topology
