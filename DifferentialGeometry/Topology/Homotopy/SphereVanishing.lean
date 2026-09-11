import DifferentialGeometry.Topology.Homotopy.CubeSphereProjection
import DifferentialGeometry.Topology.LoopSpace.FamilySphere



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]



theorem sphereMap_homotopicRel_constant_of_subsingleton (n : ℕ) (x : X)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)]
    (f : basedMappingSpace (cubeSphereBasepoint n) x) :
    f.val.HomotopicRel (ContinuousMap.const _ x) {cubeSphereBasepoint n} := by
  let p := (genLoopSphereHomeomorph n x).symm f
  have heq := @Subsingleton.elim (HomotopyGroup (Fin (n + 1)) X x) inferInstance
    ⟦p⟧ ⟦GenLoop.const⟧
  have hp : GenLoop.Homotopic p GenLoop.const := Quotient.exact heq
  have hf := (genLoopSphereHomeomorph_homotopic_iff n x p GenLoop.const).mpr hp
  simpa only [p, Homeomorph.apply_symm_apply, genLoopSphereHomeomorph_const] using hf



theorem sphereMap_nullhomotopic_of_subsingleton (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X))
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X (f (cubeSphereBasepoint n)))] :
    f.Nullhomotopic := by
  refine ⟨f (cubeSphereBasepoint n), ?_⟩
  obtain ⟨H⟩ := sphereMap_homotopicRel_constant_of_subsingleton n
    (f (cubeSphereBasepoint n)) ⟨f, rfl⟩
  exact ⟨H.toHomotopy⟩



theorem familySphereMap_nullhomotopic_of_piTwo
    (h : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x)) (f : C(familySphere, X)) :
    f.Nullhomotopic := by
  let := h (f (cubeSphereBasepoint 1))
  exact sphereMap_nullhomotopic_of_subsingleton 1 f

end DifferentialGeometry.Topology
