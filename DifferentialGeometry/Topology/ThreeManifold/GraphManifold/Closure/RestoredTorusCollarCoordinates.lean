import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MarkedRestorationOrientation

/-!
Actual compressed marked collars on both sides have the same regular-fibre signed coordinates.
The inverse coordinates follow from the source of that same signed tube.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.Seifert.ElementaryPresentation
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem restoredCompressedCollar_eq (S : CompactCarrier.{u})
    (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (E : BoundaryTori S 1)
    (σ : ℝ) (hσ : 0 < σ)
    (hg : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
      g (solidCollar.{u} 1 (p.1, halfSpaceScale hσ p.2)) =
        E.collar 0 (ψ p.1, halfSpaceScale hσ p.2))
    (t : Torus) (s : ℝ) (hs : 0 ≤ s) (hsσ : s < σ) :
    g (solidCollar.{u} 1 (t, halfPoint s hs)) = E.collar 0 (ψ t, halfPoint s hs) := by
  let q := (halfSpaceScale hσ).symm (halfPoint s hs)
  have hq : halfSpaceScale hσ q = halfPoint s hs :=
    (halfSpaceScale hσ).apply_symm_apply _
  have hcoord : σ * q.val 0 = s := by
    rw [← halfSpaceScale_coord hσ, hq]
    rfl
  have hp : (t, q) ∈ halfCollarSource := by
    change q.val 0 < 1
    nlinarith [hcoord]
  have he := hg (t, q) hp
  simpa only [hq] using he

theorem restoredTorusCollar_positive (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
    (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
      ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (t : Torus) (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    ι (Γ.collar 0 (t, halfPoint s hs)) =
      regularFibreRestorationSignedTube M φ (t, s) := by
  have hp : (t, halfPoint s hs) ∈ halfCollarSource := hs1
  rw [hΓ _ hp, regularFibreRestorationSignedTube_apply]
  rfl

theorem restoredTorusCollar_negative (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (S : CompactCarrier.{u}) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool) (E : BoundaryTori S 1)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hg : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
      g (solidCollar.{u} 1 (p.1, halfSpaceScale hσ p.2)) =
        E.collar 0 (ψ p.1, halfSpaceScale hσ p.2))
    (t : Torus) (s : ℝ) (hs : 0 ≤ s) (hsσ : s < σ) :
    markedRestorationFill M φ S g ε
        (E.collar 0 (markedRestorationMatching ψ ε t, halfPoint s hs)) =
      regularFibreRestorationSignedTube M φ (t, -s) := by
  have hp : (t, halfPoint s hs) ∈ halfCollarSource := hsσ.trans_le hσ1
  have he : markedRestorationSolidMap S g ε (solidCollar.{u} 1 (t, halfPoint s hs)) =
      E.collar 0 (markedRestorationMatching ψ ε t, halfPoint s hs) := by
    cases ε
    · exact restoredCompressedCollar_eq S g ψ E σ hσ hg t s hs hsσ
    · change g (boundedPlugSolidReflection (solidCollar.{u} 1 (t, halfPoint s hs))) =
        E.collar 0 (boundaryPortMarkedReflection ψ (ψ t), halfPoint s hs)
      rw [boundedPlugSolidReflection_collar, boundaryPortMarkedReflection_apply,
        ψ.symm_apply_apply]
      exact restoredCompressedCollar_eq S g ψ E σ hσ hg (t.1, t.2⁻¹) s hs hsσ
  rw [← he]
  change regularFibreRestorationFill M φ
    ((markedRestorationSolidMap S g ε).symm
      (markedRestorationSolidMap S g ε (solidCollar.{u} 1 (t, halfPoint s hs)))) = _
  rw [(markedRestorationSolidMap S g ε).symm_apply_apply,
    regularFibreRestorationFill_collar M φ hp, regularFibreRestorationSignedTube_apply]
  congr 2
  apply ULift.ext
  change (1 - s / 2) • (t.1 : ℂ) = (1 + -s / 2) • (t.1 : ℂ)
  congr 1
  ring

theorem exists_restoredTorusCollarCoordinates (M : ConnectedClosedOrientedManifold.{u} 3)
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
        E.collar 0 (ψ p.1, halfSpaceScale hσ p.2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ →
      ι (Γ.collar 0 (t, halfPoint s hs)) =
          regularFibreRestorationSignedTube M φ (t, s) ∧
      markedRestorationFill M φ S g ε
          (E.collar 0 (markedRestorationMatching ψ ε t, halfPoint s hs)) =
        regularFibreRestorationSignedTube M φ (t, -s) ∧
      (regularFibreRestorationSignedTube M φ).symm
          (ι (Γ.collar 0 (t, halfPoint s hs))) = (t, s) ∧
      (regularFibreRestorationSignedTube M φ).symm
          (markedRestorationFill M φ S g ε
            (E.collar 0 (markedRestorationMatching ψ ε t, halfPoint s hs))) = (t, -s) := by
  refine ⟨σ, hσ, hσ1, ?_⟩
  intro t s hs hsσ
  have hs1 := hsσ.trans_le hσ1
  have hl := restoredTorusCollar_positive M φ K ι Γ hΓ t s hs hs1
  have hr := restoredTorusCollar_negative M φ S g ψ ε E σ hσ hσ1 hg t s hs hsσ
  have hp : (t, s) ∈ (regularFibreRestorationSignedTube M φ).source := by
    rw [regularFibreRestorationSignedTube_source M φ h3]
    exact ⟨by linarith, hs1⟩
  have hn : (t, -s) ∈ (regularFibreRestorationSignedTube M φ).source := by
    rw [regularFibreRestorationSignedTube_source M φ h3]
    exact ⟨by linarith, by linarith⟩
  refine ⟨hl, hr, ?_, ?_⟩
  · rw [hl]
    exact (regularFibreRestorationSignedTube M φ).symm_apply_apply hp
  · rw [hr]
    exact (regularFibreRestorationSignedTube M φ).symm_apply_apply hn

theorem restoredTorusNativeSolidCoordinates
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
    (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
      ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) :
    let S := regularFibreRestorationSolid (solidAtlas.orientation planeCircleOrientation)
    let E := regularFibreRestorationBoundary (solidAtlas.orientation planeCircleOrientation)
    let g := Diffeomorph.refl (𝓡∂ 3) solidSet.{u} ∞
    let ψ := Diffeomorph.refl torusModel Torus ∞
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ →
      ι (Γ.collar 0 (t, halfPoint s hs)) =
          regularFibreRestorationSignedTube M φ (t, s) ∧
      markedRestorationFill M φ S g true
          (E.collar 0 (markedRestorationMatching ψ true t, halfPoint s hs)) =
        regularFibreRestorationSignedTube M φ (t, -s) ∧
      (regularFibreRestorationSignedTube M φ).symm
          (ι (Γ.collar 0 (t, halfPoint s hs))) = (t, s) ∧
      (regularFibreRestorationSignedTube M φ).symm
          (markedRestorationFill M φ S g true
            (E.collar 0 (markedRestorationMatching ψ true t, halfPoint s hs))) = (t, -s) := by
  apply exists_restoredTorusCollarCoordinates M φ h3 K ι Γ hΓ
    (regularFibreRestorationSolid (solidAtlas.orientation planeCircleOrientation))
    (Diffeomorph.refl (𝓡∂ 3) solidSet.{u} ∞)
    (Diffeomorph.refl torusModel Torus ∞) true
    (regularFibreRestorationBoundary (solidAtlas.orientation planeCircleOrientation))
    (1 / 2) (by norm_num) (by norm_num)
  intro p hp
  rfl

end GC.GraphManifold
