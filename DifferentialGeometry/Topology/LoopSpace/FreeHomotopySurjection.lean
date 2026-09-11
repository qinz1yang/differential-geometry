import DifferentialGeometry.Topology.LoopSpace.Rotation
import Mathlib.Topology.Connected.PathConnected



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}



theorem pathToCircle_conjugate_homotopic (p : Path x y) (q : Path y y) :
    (pathToCircle (p.trans (q.trans p.symm))).Homotopic (pathToCircle q) := by
  apply (pathToCircle_trans_homotopic_comm p (q.trans p.symm)).trans
  apply pathToCircle_homotopic
  exact (Path.Homotopic.trans_assoc q p.symm p).trans
    (((Path.Homotopic.refl q).hcomp (Path.Homotopic.symm_trans p)).trans
      (Path.Homotopic.trans_refl q))



theorem exists_basedCircle_free_homotopic [PathConnectedSpace X] (x : X) (γ : freeLoop X) :
    ∃ δ : basedCircleLoop x, δ.val.Homotopic γ := by
  let y := γ 0
  let q := circleToPath (⟨γ, rfl⟩ : basedCircleLoop y)
  let p := PathConnectedSpace.somePath x y
  refine ⟨basedPathCircleHomeomorph x (p.trans (q.trans p.symm)), ?_⟩
  have heq : pathToCircle q = γ := by
    ext θ
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe q t
  exact (pathToCircle_conjugate_homotopic p q).trans (heq ▸ ContinuousMap.Homotopic.refl _)

end DifferentialGeometry.Topology
