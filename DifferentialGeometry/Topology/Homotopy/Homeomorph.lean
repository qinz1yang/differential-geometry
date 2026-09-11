import DifferentialGeometry.Topology.Homotopy.LoopTopology
import DifferentialGeometry.Topology.Homotopy.Map



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def genLoopTargetHomeomorph (e : X ≃ₜ Y) (x : X) : GenLoop N X x ≃ₜ GenLoop N Y (e x) where
  toFun := genLoopPostcompose ⟨e, e.continuous⟩ x
  invFun p := ⟨(⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp p.val,
    fun y hy => by
      change e.symm (p y) = x
      rw [GenLoop.boundary p y hy, e.symm_apply_apply]⟩
  left_inv p := by ext t; exact e.symm_apply_apply (p t)
  right_inv p := by ext t; exact e.apply_symm_apply (p t)
  continuous_toFun := ((continuous_postcomp (⟨e, e.continuous⟩ : C(X, Y))).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_postcomp (⟨e.symm, e.symm.continuous⟩ : C(Y, X))).comp
    continuous_subtype_val).subtype_mk _


def homotopyGroupHomeomorphMulEquiv [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e x) where
  toEquiv := Quotient.congr (genLoopTargetHomeomorph e x).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff (genLoopTargetHomeomorph e x) p q).symm)
  map_mul' a b := (homotopyGroupMapHom (N := N) ⟨e, e.continuous⟩ x).map_mul a b

end DifferentialGeometry.Topology
