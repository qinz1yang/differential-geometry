import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutFactorMaps

/-!
The full half collars of the two actual capped punctures glue back to the original signed
sphere chart, with its genuine local smooth inverse also at the common zero sphere.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {W : CompactCarrier.{u}} (c : SphereCutSignedCollars W)
  (hs : ∀ j, (c j).source = sphereSignedCollarSource)
  (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
  (A : Bool → Set W.Carrier)
  (hconnected : ∀ b, IsConnected (A b)) (hopen : ∀ b, IsOpen (A b))
  (hdisjoint : Disjoint (A false) (A true))
  (hcover : (sphereCutAmbientZero c)ᶜ = A false ∪ A true)
  (hgerm : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ ∀ b z s, 0 < s → s < η →
    c 0 (z, sphereCutSign b s) ∈ A b)

local notation "D" => sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm

variable (B : MixedBoundaryCertificate (sphereCutCarrier c hs hd))

def sphereCutPuncturedFactorHalf (i : Fin 2) (p : sphereHalfCollarSource) :
    B.sphereCapPuncturedFactor (D) i :=
  B.sphereCapPuncturedFactorHomeomorph (D) i
    ⟨sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i) p.val,
      sphereCutComponents_fullCollar_owned c hs hd A hconnected hopen hdisjoint hcover hgerm i
        ((sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i)).map_source
          ((sphereCutFullCollar_source c hs hd 0 (sphereCutBoundarySide i)).symm ▸ p.property))⟩

theorem sphereCutPuncturedFactorHalf_map (i : Fin 2) (p : sphereHalfCollarSource) :
    sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B i
      (sphereCutPuncturedFactorHalf c hs hd A hconnected hopen hdisjoint hcover hgerm B i p) =
      c 0 (sphereCutHalfSigned (sphereCutBoundarySide i) p.val) := by
  unfold sphereCutPuncturedFactorMap sphereCutPuncturedFactorHalf
  rw [Homeomorph.symm_apply_apply]
  exact sphereCutFullCollar_fold c hs hd 0 (sphereCutBoundarySide i) p.val p.property

private theorem factor_positive_half_mem (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ sphereSignedCollarSource) (h : 0 ≤ p.2) :
    (p.1, halfSpaceOneLift p.2) ∈ sphereHalfCollarSource := by
  change max p.2 0 < 1
  rw [max_eq_left h]
  exact hp.2.2

private theorem factor_negative_half_mem (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ sphereSignedCollarSource) (h : p.2 < 0) :
    (p.1, halfSpaceOneLift (-p.2)) ∈ sphereHalfCollarSource := by
  change max (-p.2) 0 < 1
  rw [max_eq_left (by linarith : 0 ≤ -p.2)]
  linarith [hp.2.1]

def sphereCutPuncturedFactorCollar (p : ClosureSphere.{u} × ℝ) : W.Carrier := by
  classical
  exact if hp : p ∈ sphereSignedCollarSource then
    if h : p.2 < 0 then
      sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B 1
        (sphereCutPuncturedFactorHalf c hs hd A hconnected hopen hdisjoint hcover hgerm B 1
          ⟨(p.1, halfSpaceOneLift (-p.2)), factor_negative_half_mem p hp h⟩)
    else
      sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B 0
        (sphereCutPuncturedFactorHalf c hs hd A hconnected hopen hdisjoint hcover hgerm B 0
          ⟨(p.1, halfSpaceOneLift p.2), factor_positive_half_mem p hp (le_of_not_gt h)⟩)
  else c 0 p

theorem sphereCutPuncturedFactorCollar_eq (p : ClosureSphere.{u} × ℝ) :
    sphereCutPuncturedFactorCollar c hs hd A hconnected hopen hdisjoint hcover hgerm B p =
      c 0 p := by
  unfold sphereCutPuncturedFactorCollar
  split_ifs with hp h
  · rw [sphereCutPuncturedFactorHalf_map]
    congr 1
    apply Prod.ext
    · rfl
    · change -max (-p.2) 0 = p.2
      rw [max_eq_left (by linarith : 0 ≤ -p.2)]
      exact neg_neg p.2
  · rw [sphereCutPuncturedFactorHalf_map]
    congr 1
    apply Prod.ext
    · rfl
    · change max p.2 0 = p.2
      exact max_eq_left (le_of_not_gt h)
  · rfl

theorem sphereCutPuncturedFactorCollar_local (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ sphereSignedCollarSource) :
    IsLocalDiffeomorphAt sphereSignedCollarModel W.model ∞
      (sphereCutPuncturedFactorCollar c hs hd A hconnected hopen hdisjoint hcover hgerm B) p := by
  have he : sphereCutPuncturedFactorCollar c hs hd A hconnected hopen hdisjoint hcover hgerm B =
      c 0 := funext (sphereCutPuncturedFactorCollar_eq c hs hd A hconnected hopen hdisjoint
        hcover hgerm B)
  rw [he]
  exact (c 0).isLocalDiffeomorphAt sphereSignedCollarModel W.model ∞ ((hs 0).symm ▸ hp)

end GC.GraphManifold
