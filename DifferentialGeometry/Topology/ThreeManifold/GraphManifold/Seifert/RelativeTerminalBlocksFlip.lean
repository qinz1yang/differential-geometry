import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksSolid

/-!
# Actual seam flips in mixed relative stages

Flipping uses the existing torus presentation and product-piece constructions. It preserves
frozen geometry, protected indices and terminality, with the exact Boolean side and filling
distance ledger. The canonical flip moves a nonfrozen right solid vertex to the left; its
protected signed collars and matching remain exactly the original maps.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

def flip (φ : Fin σ.toTorus.pairing.count → Bool) : MixedStage Q where
  toTorus := σ.toTorus.flipSeams φ
  prot := σ.prot
  frozen := σ.frozen
  hyperbolic := σ.hyperbolic
  kind := σ.kind
  kind_mem := σ.kind_mem
  piece i hi := (σ.piece i hi).flip φ
  left_prot j hi := by
    change (if φ j then σ.toTorus.rightPiece j else σ.toTorus.leftPiece j) ∈ σ.frozen at hi
    split_ifs at hi with hj
    · exact σ.right_prot j hi
    · exact σ.left_prot j hi
  right_prot j hi := by
    change (if φ j then σ.toTorus.leftPiece j else σ.toTorus.rightPiece j) ∈ σ.frozen at hi
    split_ifs at hi with hj
    · exact σ.left_prot j hi
    · exact σ.right_prot j hi

variable (φ : Fin σ.toTorus.pairing.count → Bool)

theorem prot_flip : (σ.flip φ).prot = σ.prot := rfl

theorem frozen_flip : (σ.flip φ).frozen = σ.frozen := rfl

theorem kind_flip (i : Fin σ.toTorus.components.count) : (σ.flip φ).kind i = σ.kind i := rfl

theorem seamPiece_flip (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.flip φ).seamPiece j b = σ.seamPiece j (b ^^ φ j) := by
  cases b <;> by_cases h : φ j = true <;>
    simp [seamPiece, flip, TorusPresentation.flipSeams, TorusPresentation.flipLeftPiece,
      TorusPresentation.flipRightPiece, h]

theorem hostPiece_flip (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.flip φ).hostPiece j b = σ.hostPiece j (b ^^ φ j) := by
  unfold hostPiece
  rw [seamPiece_flip]
  cases b <;> cases φ j <;> rfl

theorem fillingDistance_false (j : Fin σ.toTorus.pairing.count) :
    σ.fillingDistance j false = PrimitiveSlope.delta
      ((torusUnit (σ.toTorus.pairing.matching j))⁻¹ • meridianSlope) fiberSlope := by
  rw [PrimitiveSlope.delta_comm,
    ← PrimitiveSlope.delta_smul (torusUnit (σ.toTorus.pairing.matching j)), smul_inv_smul]
  rfl

theorem fillingDistance_flip (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.flip φ).fillingDistance j b = σ.fillingDistance j (b ^^ φ j) := by
  by_cases h : φ j = true
  · have hm : (σ.flip φ).toTorus.pairing.matching j =
        (σ.toTorus.pairing.matching j).symm := ite_eq_left h
    cases b
    · simp only [h, Bool.false_xor]
      change PrimitiveSlope.delta (torusUnit ((σ.flip φ).toTorus.pairing.matching j) •
        fiberSlope) meridianSlope = PrimitiveSlope.delta
          (torusUnit (σ.toTorus.pairing.matching j) • meridianSlope) fiberSlope
      rw [hm, ElementaryPresentation.torusUnit_symm, PrimitiveSlope.delta_comm,
        ← PrimitiveSlope.delta_smul (torusUnit (σ.toTorus.pairing.matching j)), smul_inv_smul]
    · simp only [h, Bool.true_xor, Bool.not_true]
      change PrimitiveSlope.delta (torusUnit ((σ.flip φ).toTorus.pairing.matching j) •
        meridianSlope) fiberSlope = _
      rw [hm, ElementaryPresentation.torusUnit_symm, fillingDistance_false]
  · have hm : (σ.flip φ).toTorus.pairing.matching j = σ.toTorus.pairing.matching j :=
      ite_eq_right h
    rw [Bool.not_eq_true] at h
    simp only [h, Bool.xor_false]
    cases b
    · change PrimitiveSlope.delta (torusUnit ((σ.flip φ).toTorus.pairing.matching j) •
        fiberSlope) meridianSlope = PrimitiveSlope.delta
          (torusUnit (σ.toTorus.pairing.matching j) • fiberSlope) meridianSlope
      rw [hm]
    · change PrimitiveSlope.delta (torusUnit ((σ.flip φ).toTorus.pairing.matching j) •
        meridianSlope) fiberSlope = PrimitiveSlope.delta
          (torusUnit (σ.toTorus.pairing.matching j) • meridianSlope) fiberSlope
      rw [hm]

theorem isMergeSeam_flip (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.flip φ).IsMergeSeam j b ↔ σ.IsMergeSeam j (b ^^ φ j) := by
  unfold IsMergeSeam
  rw [seamPiece_flip, hostPiece_flip, fillingDistance_flip]
  rfl

theorem isSplitSeam_flip (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.flip φ).IsSplitSeam j b ↔ σ.IsSplitSeam j (b ^^ φ j) := by
  unfold IsSplitSeam
  rw [seamPiece_flip, hostPiece_flip, fillingDistance_flip]
  rfl

theorem isAbsorbSeam_flip (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.flip φ).IsAbsorbSeam j b ↔ σ.IsAbsorbSeam j (b ^^ φ j) := by
  unfold IsAbsorbSeam
  rw [seamPiece_flip, hostPiece_flip]
  rfl

theorem flip_isTerminal (ht : σ.IsTerminal) : (σ.flip φ).IsTerminal := by
  intro j b
  rw [σ.isMergeSeam_flip φ j b, σ.isSplitSeam_flip φ j b, σ.isAbsorbSeam_flip φ j b]
  exact ht j (b ^^ φ j)

theorem seam_flip_false {j : Fin σ.toTorus.pairing.count} (hj : φ j = false) :
    (σ.flip φ).toTorus.seam j = σ.toTorus.seam j := by
  change σ.toTorus.flipSeam φ j = σ.toTorus.seam j
  simp only [TorusPresentation.flipSeam, hj, Bool.false_eq_true, ↓reduceIte]

theorem seamTorus_flip_true {j : Fin σ.toTorus.pairing.count} (hj : φ j = true) :
    (σ.flip φ).toTorus.seamTorus j = (σ.toTorus.seamTorus j).comp
      ((σ.toTorus.pairing.matching j).symm.toHomeomorph : C(Torus, Torus)) := by
  ext t
  change σ.toTorus.flipSeam φ j (t, 0) = _
  rw [TorusPresentation.flipSeam, ite_eq_left hj, seamFlipChart_apply, neg_zero]
  rfl

theorem seamTorus_flip_false {j : Fin σ.toTorus.pairing.count} (hj : φ j = false) :
    (σ.flip φ).toTorus.seamTorus j = σ.toTorus.seamTorus j := by
  ext t
  exact congrArg (fun c => c (t, 0)) (σ.seam_flip_false φ hj)

theorem flip_protected_injective
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t)) :
    ∀ k : (σ.flip φ).ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map ((σ.flip φ).toTorus.seamTorus k.val) t) := by
  intro k t
  by_cases hj : φ k.val = true
  · rw [σ.seamTorus_flip_true φ hj]
    exact (forall_injective_comp_homeomorph_iff _
      (σ.toTorus.pairing.matching k.val).symm.toHomeomorph).mpr (hInc k) t
  · have hjf : φ k.val = false := by simpa only [Bool.not_eq_true] using hj
    rw [σ.seamTorus_flip_false φ hjf]
    exact hInc k t

def solidLeftFlip (j : Fin σ.toTorus.pairing.count) : Bool :=
  decide (σ.toTorus.rightPiece j ∉ σ.frozen ∧ σ.kind (σ.toTorus.rightPiece j) = 1)

theorem solidLeftFlip_protected
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (j : σ.ProtSeam) : σ.solidLeftFlip j.val = false := by
  apply decide_eq_false
  rintro ⟨hi, hk⟩
  exact σ.solid_seam_not_protected hInc false hi hk j.property

theorem solidLeftFlip_protected_seam
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (j : σ.ProtSeam) :
    (σ.flip σ.solidLeftFlip).toTorus.seam j.val = σ.toTorus.seam j.val :=
  σ.seam_flip_false σ.solidLeftFlip (σ.solidLeftFlip_protected hInc j)

theorem solidLeftFlip_protected_matching
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (j : σ.ProtSeam) :
    (σ.flip σ.solidLeftFlip).toTorus.pairing.matching j.val = σ.toTorus.pairing.matching j.val := by
  change (if σ.solidLeftFlip j.val then (σ.toTorus.pairing.matching j.val).symm
    else σ.toTorus.pairing.matching j.val) = _
  rw [σ.solidLeftFlip_protected hInc j]
  rfl

theorem solidLeftFlip_protected_leftCollar
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (j : σ.ProtSeam) :
    (σ.flip σ.solidLeftFlip).toTorus.pairing.leftCollar j.val =
      σ.toTorus.pairing.leftCollar j.val := by
  change (if σ.solidLeftFlip j.val then σ.toTorus.pairing.rightCollar j.val
    else σ.toTorus.pairing.leftCollar j.val) = _
  rw [σ.solidLeftFlip_protected hInc j]
  rfl

theorem solidLeftFlip_protected_rightCollar
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (j : σ.ProtSeam) :
    (σ.flip σ.solidLeftFlip).toTorus.pairing.rightCollar j.val =
      σ.toTorus.pairing.rightCollar j.val := by
  change (if σ.solidLeftFlip j.val then σ.toTorus.pairing.leftCollar j.val
    else σ.toTorus.pairing.rightCollar j.val) = _
  rw [σ.solidLeftFlip_protected hInc j]
  rfl

end GC.Seifert.RelativeNormalization.MixedStage
