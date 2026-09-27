import DifferentialGeometry.Topology.Homotopy.Homeomorph



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def genLoopBasedMap (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y)
    (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.val, fun t ht => (congrArg f (GenLoop.boundary p t ht)).trans hf⟩


def homotopyGroupBasedMap (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (genLoopBasedMap f x y hf)
    (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)


def homotopyGroupBasedMapHom [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (x : X) (y : Y) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := homotopyGroupBasedMap f x y hf
  map_one' := by
    subst y
    exact (homotopyGroupMapHom f x).map_one
  map_mul' a b := by
    subst y
    exact (homotopyGroupMapHom f x).map_mul a b



def genLoopBasedHomeomorph (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) :
    GenLoop N X x ≃ₜ GenLoop N Y y where
  toFun := genLoopBasedMap ⟨e, e.continuous⟩ x y he
  invFun := genLoopBasedMap ⟨e.symm, e.symm.continuous⟩ y x
    ((congrArg e.symm he).symm.trans (e.symm_apply_apply x))
  left_inv p := by ext t; exact e.symm_apply_apply (p t)
  right_inv p := by ext t; exact e.apply_symm_apply (p t)
  continuous_toFun := ((continuous_postcomp (⟨e, e.continuous⟩ : C(X, Y))).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_postcomp (⟨e.symm, e.symm.continuous⟩ : C(Y, X))).comp
    continuous_subtype_val).subtype_mk _


def homotopyGroupBasedHomeomorphMulEquiv [DecidableEq N] [Nonempty N]
    (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y where
  toEquiv := Quotient.congr (genLoopBasedHomeomorph e x y he).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff (genLoopBasedHomeomorph e x y he) p q).symm)
  map_mul' a b := (homotopyGroupBasedMapHom ⟨e, e.continuous⟩ x y he).map_mul a b

end DifferentialGeometry.Topology
