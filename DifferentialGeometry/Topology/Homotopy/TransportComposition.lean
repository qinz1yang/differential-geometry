import DifferentialGeometry.Topology.Homotopy.ExtensionUniqueness



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y z : X}



def cubePathHomotopy (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x) :
    Γ.val.Homotopy (genLoopTransport n p Γ).val where
  toContinuousMap := ⟨cubePathExtension n p Γ, continuous_cubePathExtension n p Γ⟩
  map_zero_left := cubePathExtension_zero n p Γ
  map_one_left _ := rfl


theorem cubePathHomotopy_boundary (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) (t : unitInterval)
    (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    cubePathHomotopy n p Γ (t, v) = p t := cubePathExtension_boundary n p Γ t v hv



theorem genLoopTransport_trans_homotopic (n : ℕ) (p : Path x y) (q : Path y z)
    (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (genLoopTransport n q (genLoopTransport n p Γ))
      (genLoopTransport n (p.trans q) Γ) := by
  let H := (cubePathHomotopy n p Γ).trans (cubePathHomotopy n q (genLoopTransport n p Γ))
  apply genLoopTransport_extension_unique n (p.trans q) Γ _ H.toContinuousMap
    H.apply_zero H.apply_one
  intro t v hv
  change H (t, v) = (p.trans q) t
  simp only [H, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact cubePathHomotopy_boundary n p Γ _ v hv
  · exact cubePathHomotopy_boundary n q (genLoopTransport n p Γ) _ v hv

end DifferentialGeometry.Topology
