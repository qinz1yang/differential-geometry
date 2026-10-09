import DifferentialGeometry.Topology.GroupAction.Quotient
import Mathlib.Topology.Homotopy.Basic

namespace ContinuousMap

variable {G K X Y : Type*} [Group G] [Group K]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X] [MulAction K Y]

namespace Homotopy

variable {f g : C(X, Y)}

def orbitQuotient (H : Homotopy f g) (φ : G → K)
    (hH : ∀ t γ x, H (t, γ • x) = φ γ • H (t, x)) :
    Homotopy (f.orbitQuotientMap φ (fun γ x => by simpa using hH 0 γ x))
      (g.orbitQuotientMap φ (fun γ x => by simpa using hH 1 γ x)) where
  toFun p :=
    (⟨fun x => H (p.1, x), H.continuous.comp (continuous_const.prodMk continuous_id)⟩ :
      C(X, Y)).orbitQuotientMap φ (hH p.1) p.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp H.continuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (Quotient.mk (MulAction.orbitRel K Y)) (H.apply_zero x)
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (Quotient.mk (MulAction.orbitRel K Y)) (H.apply_one x)

@[simp]
theorem orbitQuotient_apply_mk (H : Homotopy f g) (φ : G → K)
    (hH : ∀ t γ x, H (t, γ • x) = φ γ • H (t, x)) (t : unitInterval) (x : X) :
    H.orbitQuotient φ hH (t, Quotient.mk (MulAction.orbitRel G X) x) =
      Quotient.mk (MulAction.orbitRel K Y) (H (t, x)) := rfl

end Homotopy

end ContinuousMap
