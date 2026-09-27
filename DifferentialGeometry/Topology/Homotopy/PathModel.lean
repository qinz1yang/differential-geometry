import DifferentialGeometry.Topology.Homotopy.Homeomorph



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]



def genLoopPathHomeomorph (N : Type*) [Unique N] (x : X) :
    GenLoop N X x ≃ₜ Path x x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_pi fun _ => continuous_snd))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_of_continuous_uncurry
    exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      (continuous_fst.prodMk ((continuous_apply default).comp continuous_snd))


theorem genLoopPathHomeomorph_const (N : Type*) [Unique N] (x : X) :
    genLoopPathHomeomorph N x GenLoop.const = Path.refl x := by
  ext t
  rfl

end DifferentialGeometry.Topology
