import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredTorusCollarCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal

/-!
Matching the actual physical half collars to one signed seam gives a local diffeomorphism.
The conclusion follows at the glued torus from the same two-sided normal scale.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold

variable (M : ConnectedClosedOrientedManifold.{u} 3) {N : CompactCarrier.{u}}
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
  (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
  (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
  (S : CompactCarrier.{u}) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
  (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool) (E : BoundaryTori S 1)
  (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
  (hg : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    g (solidCollar.{u} 1 (p.1, halfSpaceScale hσ p.2)) =
      E.collar 0 (ψ p.1, halfSpaceScale hσ p.2))
  (F : M.Carrier → N.Carrier)
  (q : PartialDiffeomorph signedCollarModel N.model (Torus × ℝ) N.Carrier ∞)
  (hq : q.source = signedCollarSource)
  (α : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (a : ℝ) (ha : 0 < a)
  (η : ℝ) (hη : 0 < η)
  (hL : ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < η →
    F (ι (Γ.collar 0 (t, halfPoint s hs))) = q (α t, -(s / a)))
  (hR : ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < η →
    F (markedRestorationFill M φ S g ε
      (E.collar 0 (markedRestorationMatching ψ ε t, halfPoint s hs))) = q (α t, s / a))

include h3 hΓ hσ hσ1 hg hq ha hη hL hR in
theorem restoredTorusFactor_isLocalDiffeomorphAt (t : Torus) :
    IsLocalDiffeomorphAt (𝓡 3) N.model ∞ F
      (regularFibreRestorationSignedTube M φ (t, 0)) := by
  let R := regularFibreRestorationSignedTube M φ
  let A : (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) :=
    α.prodCongr ((realScale ha).symm.trans negDiffeomorph)
  have hA (p : Torus × ℝ) : A p = (α p.1, -(p.2 / a)) := by
    apply Prod.ext
    · rfl
    · change -(a⁻¹ * p.2) = -(p.2 / a)
      rw [div_eq_mul_inv, mul_comm]
  let qA := A.toPartialDiffeomorph.trans q
  have hqA : (t, (0 : ℝ)) ∈ qA.source := by
    change (t, (0 : ℝ)) ∈ univ ∧ A (t, 0) ∈ q.source
    rw [hA, hq]
    exact ⟨mem_univ _, by change -1 < -(0 / a) ∧ -(0 / a) < 1; norm_num⟩
  have hloc := qA.isLocalDiffeomorphAt signedCollarModel N.model ∞ hqA
  have heq : (F ∘ R) =ᶠ[𝓝 (t, (0 : ℝ))] qA := by
    have hμ : 0 < min σ η := lt_min hσ hη
    have hv : {p : Torus × ℝ | p.2 ∈ Ioo (-(min σ η)) (min σ η)} ∈
        𝓝 (t, (0 : ℝ)) :=
      (isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, hμ⟩
    filter_upwards [hv] with p hp
    change F (R p) = q (A p)
    rw [hA]
    by_cases hs : 0 ≤ p.2
    · have hsσ : p.2 < σ := hp.2.trans_le (min_le_left σ η)
      have hsη : p.2 < η := hp.2.trans_le (min_le_right σ η)
      have hr := restoredTorusCollar_positive M φ K ι Γ hΓ p.1 p.2 hs
        (hsσ.trans_le hσ1)
      change F (regularFibreRestorationSignedTube M φ p) = _
      rw [← hr]
      exact hL p.1 p.2 hs hsη
    · have hs0 : 0 ≤ -p.2 := (neg_pos.mpr (lt_of_not_ge hs)).le
      have hsσ : -p.2 < σ := by have hm := min_le_left σ η; linarith [hp.1]
      have hsη : -p.2 < η := by have hm := min_le_right σ η; linarith [hp.1]
      have hr := restoredTorusCollar_negative M φ S g ψ ε E σ hσ hσ1 hg
        p.1 (-p.2) hs0 hsσ
      rw [neg_neg] at hr
      change F (regularFibreRestorationSignedTube M φ p) = _
      rw [← hr, hR p.1 (-p.2) hs0 hsη, neg_div]
  have hcomp := DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq hloc
  apply isLocalDiffeomorphAt_of_comp hcomp
  apply R.isLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞
  rw [regularFibreRestorationSignedTube_source M φ h3]
  change -1 < (0 : ℝ) ∧ 0 < 1
  norm_num

end GC.GraphManifold
