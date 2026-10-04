import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup

set_option autoImplicit false

open CategoryTheory
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem fundamentalGroupChangeBasepoint_refl (x : X) :
    fundamentalGroupChangeBasepoint (Path.refl x) = MulEquiv.refl _ := by
  ext p
  change ((𝟙 (FundamentalGroupoid.mk x)) ≫ p) ≫ Groupoid.inv (𝟙 _) = p
  simp

theorem fundamentalGroupChangeBasepoint_trans {x y z : X} (α : Path x y) (β : Path y z) :
    fundamentalGroupChangeBasepoint (α.trans β) =
      (fundamentalGroupChangeBasepoint β).trans (fundamentalGroupChangeBasepoint α) := by
  ext p
  let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦α⟧
  let b : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z := ⟦β⟧
  change ((a ≫ b) ≫ p) ≫ Groupoid.inv (a ≫ b) =
    (a ≫ ((b ≫ p) ≫ Groupoid.inv b)) ≫ Groupoid.inv a
  simp

theorem fundamentalGroupChangeBasepoint_symm {x y : X} (α : Path x y) :
    fundamentalGroupChangeBasepoint α.symm = (fundamentalGroupChangeBasepoint α).symm := by
  ext p
  let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦α⟧
  change (Groupoid.inv a ≫ p) ≫ Groupoid.inv (Groupoid.inv a) =
    (Groupoid.inv a ≫ p) ≫ a
  simp

theorem fundamentalGroupChangeBasepoint_naturality (f : C(X, Y))
    {x y : X} (α : Path x y) :
    (FundamentalGroup.map f x).comp (fundamentalGroupChangeBasepoint α).toMonoidHom =
      (fundamentalGroupChangeBasepoint (α.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f y) := by
  ext p
  let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦α⟧
  let F := FundamentalGroupoid.map f
  change F.map ((a ≫ p) ≫ Groupoid.inv a) =
    (F.map a ≫ F.map p) ≫ Groupoid.inv (F.map a)
  simp

end DifferentialGeometry.Topology

namespace GC.Topology

open DifferentialGeometry.Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem markedMap_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) {y : Y} {z : Z}
    (α : Path y (f x)) (β : Path z (g y)) :
    markedMap (g.comp f) x (β.trans (α.map g.continuous)) =
      (markedMap g y β).comp (markedMap f x α) := by
  ext p
  change fundamentalGroupChangeBasepoint (β.trans (α.map g.continuous))
    (FundamentalGroup.map (g.comp f) x p) =
    fundamentalGroupChangeBasepoint β
      (FundamentalGroup.map g y (fundamentalGroupChangeBasepoint α
        (FundamentalGroup.map f x p)))
  rw [fundamentalGroupChangeBasepoint_trans, fundamentalGroup_map_comp]
  exact congrArg (fundamentalGroupChangeBasepoint β)
    (congrArg (fun k => k (FundamentalGroup.map f x p))
      (fundamentalGroupChangeBasepoint_naturality g α)).symm

theorem markedMap_homotopy_track (f g : C(X, Y)) (H : f.Homotopy g)
    (x : X) {y : Y} (α : Path y (f x)) :
    markedMap g x (α.trans (H.evalAt x)) = markedMap f x α := by
  ext p
  change fundamentalGroupChangeBasepoint (α.trans (H.evalAt x))
    (FundamentalGroup.map g x p) =
      fundamentalGroupChangeBasepoint α (FundamentalGroup.map f x p)
  rw [fundamentalGroupChangeBasepoint_trans]
  exact congrArg (fundamentalGroupChangeBasepoint α)
    (congrArg (fun k => k p) (homotopy_track f g H x))

theorem markedMap_ker (f : C(X, Y)) (x : X) {y : Y} (α : Path y (f x)) :
    (markedMap f x α).ker = (FundamentalGroup.map f x).ker := by
  ext p
  change fundamentalGroupChangeBasepoint α (FundamentalGroup.map f x p) = 1 ↔ _
  rw [← map_one (fundamentalGroupChangeBasepoint α),
    (fundamentalGroupChangeBasepoint α).injective.eq_iff]
  rfl

theorem homotopic_kernel (f g : C(X, Y)) (H : f.Homotopy g) (x : X) :
    (FundamentalGroup.map f x).ker = (FundamentalGroup.map g x).ker := by
  rw [← homotopy_track f g H x, markedMap_ker]

theorem common_core_homotopic_kernel {T : Type*} [TopologicalSpace T]
    (a b : C(T, X)) (H : a.Homotopy b) (jm : C(X, Y)) (jp : C(X, Z)) (t : T)
    (hm : Function.Injective (FundamentalGroup.map jm (a t)))
    (hp : Function.Injective (FundamentalGroup.map jp (b t))) :
    (FundamentalGroup.map (jm.comp a) t).ker =
      (FundamentalGroup.map (jp.comp b) t).ker := by
  rw [composite_kernel a jm t hm, composite_kernel b jp t hp]
  exact homotopic_kernel a b H t

end GC.Topology
