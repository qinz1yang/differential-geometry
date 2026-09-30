import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.FundamentalGroup.Retraction

namespace GC.Topology
open DifferentialGeometry.Topology CategoryTheory
open scoped ContinuousMap
noncomputable section
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def markedMap (f : C(X, Y)) (x : X) {y : Y} (β : Path y (f x)) :
    FundamentalGroup X x →* FundamentalGroup Y y :=
  (fundamentalGroupChangeBasepoint β).toMonoidHom.comp (FundamentalGroup.map f x)

theorem markedMap_injective_iff (f : C(X, Y)) (x : X) {y : Y}
    (β : Path y (f x)) :
    Function.Injective (markedMap f x β) ↔ Function.Injective (FundamentalGroup.map f x) := by
  constructor
  · intro h a b hab
    exact h (congrArg (fundamentalGroupChangeBasepoint β) hab)
  · intro h
    exact (fundamentalGroupChangeBasepoint β).injective.comp h

theorem fundamentalGroup_map_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  ext p
  exact Path.Homotopic.Quotient.map_comp

theorem injective_inner_of_composite (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (h : Function.Injective (FundamentalGroup.map (g.comp f) x)) :
    Function.Injective (FundamentalGroup.map f x) := by
  rw [fundamentalGroup_map_comp] at h
  intro a b hab
  exact h (congrArg (FundamentalGroup.map g (f x)) hab)

theorem composite_kernel (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (hg : Function.Injective (FundamentalGroup.map g (f x))) :
    (FundamentalGroup.map (g.comp f) x).ker = (FundamentalGroup.map f x).ker := by
  ext p
  change FundamentalGroup.map (g.comp f) x p = 1 ↔ FundamentalGroup.map f x p = 1
  rw [fundamentalGroup_map_comp]
  change FundamentalGroup.map g (f x) (FundamentalGroup.map f x p) = 1 ↔ _
  rw [← map_one (FundamentalGroup.map g (f x)), hg.eq_iff]

theorem homotopy_track (f g : C(X, Y)) (H : f.Homotopy g) (x : X) :
    markedMap g x (H.evalAt x) = FundamentalGroup.map f x := by
  ext p
  have hn := (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality p
  change (FundamentalGroup.map f x p).trans (Path.Homotopic.Quotient.mk (H.evalAt x)) =
    Path.Homotopic.Quotient.trans ((Path.Homotopic.Quotient.mk (H.evalAt x)) : Path.Homotopic.Quotient (f x) (g x))
      (FundamentalGroup.map g x p) at hn
  change (Path.Homotopic.Quotient.trans ((Path.Homotopic.Quotient.mk (H.evalAt x)) : Path.Homotopic.Quotient (f x) (g x))
    (FundamentalGroup.map g x p)).trans
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk (H.evalAt x))) = _
  rw [← hn, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

theorem homotopic_injective_iff (f g : C(X, Y)) (H : f.Homotopy g) (x : X) :
    Function.Injective (FundamentalGroup.map f x) ↔
      Function.Injective (FundamentalGroup.map g x) := by
  rw [← homotopy_track f g H x, markedMap_injective_iff]

theorem common_core_kernel {T : Type*} [TopologicalSpace T]
    (a : C(T, X)) (jm : C(X, Y)) (jp : C(X, Z)) (t : T)
    (hm : Function.Injective (FundamentalGroup.map jm (a t)))
    (hp : Function.Injective (FundamentalGroup.map jp (a t))) :
    (FundamentalGroup.map (jm.comp a) t).ker =
      (FundamentalGroup.map (jp.comp a) t).ker := by
  rw [composite_kernel a jm t hm, composite_kernel a jp t hp]

end
end GC.Topology
