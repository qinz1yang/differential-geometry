import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCappingCore

/-!
Each actual capped component recovers its original cut component after removal of the same
open cap balls. The whole homeomorphism retains the literal core map and its inverse square.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C) (D : C.Components)

def sphereCapPuncturedFactor (j : Fin D.count) : Set B.sphereCapCarrier.Carrier :=
  (B.sphereCapComponents D).piece j ∩ B.sphereCapRelativeCapping.capInteriorImageᶜ

private def puncturedFactorForward (j : Fin D.count) (x : D.piece j) :
    B.sphereCapPuncturedFactor D j :=
  ⟨B.sphereCapCore x.val,
    (B.sphereCapComponents_core_mem D j x.val).mpr x.property,
    B.sphereCapRelativeCapping.core_range_eq_capInteriorImage_compl.subset ⟨x.val, rfl⟩⟩

private def puncturedFactorInverse (j : Fin D.count)
    (x : B.sphereCapPuncturedFactor D j) : D.piece j := by
  let e := B.sphereCapRelativeCapping.corePunctureHomeomorph
  let y := e.symm ⟨x.val, x.property.2⟩
  have hy : B.sphereCapCore y = x.val := congrArg Subtype.val (e.apply_symm_apply _)
  exact ⟨y, (B.sphereCapComponents_core_mem D j y).mp (hy.symm ▸ x.property.1)⟩

private theorem puncturedFactorInverse_square (j : Fin D.count)
    (x : B.sphereCapPuncturedFactor D j) :
    B.sphereCapCore (B.puncturedFactorInverse D j x).val = x.val := by
  exact congrArg Subtype.val
    (B.sphereCapRelativeCapping.corePunctureHomeomorph.apply_symm_apply
      ⟨x.val, x.property.2⟩)

def sphereCapPuncturedFactorHomeomorph (j : Fin D.count) :
    D.piece j ≃ₜ B.sphereCapPuncturedFactor D j where
  toFun := B.puncturedFactorForward D j
  invFun := B.puncturedFactorInverse D j
  left_inv x := by
    apply Subtype.ext
    apply B.sphereCapCore_injective
    exact B.puncturedFactorInverse_square D j (B.puncturedFactorForward D j x)
  right_inv x := by
    apply Subtype.ext
    exact B.puncturedFactorInverse_square D j x
  continuous_toFun :=
    (B.sphereCapCore.continuous.comp continuous_subtype_val).subtype_mk
      (fun x => (B.puncturedFactorForward D j x).property)
  continuous_invFun := by
    let e := B.sphereCapRelativeCapping.corePunctureHomeomorph
    have hc : Continuous (fun x : B.sphereCapPuncturedFactor D j =>
        (⟨x.val, x.property.2⟩ : ↥(B.sphereCapRelativeCapping.capInteriorImageᶜ))) :=
      continuous_subtype_val.subtype_mk (fun x => x.property.2)
    exact (e.symm.continuous.comp hc).subtype_mk
      (fun x => (B.puncturedFactorInverse D j x).property)

theorem sphereCapPuncturedFactorHomeomorph_apply (j : Fin D.count) (x : D.piece j) :
    (B.sphereCapPuncturedFactorHomeomorph D j x).val = B.sphereCapCore x.val := rfl

theorem sphereCapPuncturedFactorHomeomorph_symm_apply (j : Fin D.count)
    (x : B.sphereCapPuncturedFactor D j) :
    B.sphereCapCore ((B.sphereCapPuncturedFactorHomeomorph D j).symm x).val = x.val :=
  B.puncturedFactorInverse_square D j x

end GC.GraphManifold.MixedBoundaryCertificate
