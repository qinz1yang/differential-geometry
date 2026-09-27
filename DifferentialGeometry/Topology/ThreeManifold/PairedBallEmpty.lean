import DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing
import DifferentialGeometry.Topology.Homeomorph.Sigma
import DifferentialGeometry.Topology.Homeomorph.QuotientDescent

set_option autoImplicit false
noncomputable section
open Set Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {V : Type v} {E : Type w} [IsEmpty E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (t : Bool) →
    OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)

def puncturedFactorHomeomorphOfIsEmpty (v : V) :
    PuncturedFactor N endpoint chart v ≃ₜ (N v).Carrier := by
  let h (x : (N v).Carrier) : (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 := by
    intro hx
    obtain ⟨p, _⟩ := mem_iUnion.mp hx
    exact isEmptyElim p.1
  exact
    { toFun := Subtype.val
      invFun := fun x => ⟨x, h x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk h }

@[simp] theorem puncturedFactorHomeomorphOfIsEmpty_apply (v : V)
    (x : PuncturedFactor N endpoint chart v) :
    puncturedFactorHomeomorphOfIsEmpty N endpoint chart v x = x.val := rfl

def quotientHomeomorphOfIsEmpty
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (attachment : E → BoundaryAttachment) :
    Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y) ≃ₜ
      (Σ v, (N v).Carrier) :=
  (Homeomorph.Quot.emptyRelation _ (fun _ _ ⟨e, _⟩ => isEmptyElim e)).trans
    (Homeomorph.sigmaCongrRight (puncturedFactorHomeomorphOfIsEmpty N endpoint chart))

@[simp] theorem quotientHomeomorphOfIsEmpty_mk
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
    (attachment : E → BoundaryAttachment) (v : V) (x : PuncturedFactor N endpoint chart v) :
    quotientHomeomorphOfIsEmpty N endpoint chart hdisj attachment (Quot.mk _ ⟨v, x⟩) =
      ⟨v, x.val⟩ := rfl

end DifferentialGeometry.Topology.PairedBallGluing
