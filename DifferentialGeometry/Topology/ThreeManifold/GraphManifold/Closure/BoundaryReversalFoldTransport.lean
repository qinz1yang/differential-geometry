import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierSum
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal

/-!
Actual oriented folds transport the opposite boundary orientations of smooth collar maps.
The physical first quotient is retained when forming the subsequent boundary gluing.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology

universe u
namespace GC.GraphManifold

theorem reversesBoundaryOrientation_of_orientedFold {C N : CompactCarrier.{u}}
    {F : C.Carrier → N.Carrier} (hF : IsOrientedFold F)
    (hsm : ContMDiff C.model N.model ∞ F)
    {l r : Torus × EuclideanHalfSpace 1 → C.Carrier}
    (hrev : ReversesBoundaryOrientation C l r)
    (hl : ∀ t, MDifferentiableAt halfCollarModel C.model l (t, halfZero))
    (hr : ∀ t, MDifferentiableAt halfCollarModel C.model r (t, halfZero)) :
    ReversesBoundaryOrientation N (F ∘ l) (F ∘ r) := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := hrev t
  obtain ⟨A, hA, hoA⟩ := hF (l (t, halfZero))
  obtain ⟨B, hB, hoB⟩ := hF (r (t, halfZero))
  refine ⟨L.trans A, R.trans B, ?_, ?_, ?_⟩
  · intro v
    change A (L v) = _
    rw [hA, hL]
    exact (mfderiv_comp_apply (t, halfZero)
      (hsm.mdifferentiable (by simp) _) (hl t) v).symm
  · intro v
    change B (R v) = _
    rw [hB, hR]
    exact (mfderiv_comp_apply (t, halfZero)
      (hsm.mdifferentiable (by simp) _) (hr t) v).symm
  · have hOL : Orientation.map (Fin 3) (L.trans A).symm
        (N.orientation.orientation (F (l (t, halfZero)))) =
        Orientation.map (Fin 3) L.symm (C.orientation.orientation (l (t, halfZero))) := by
      rw [LinearEquiv.trans_symm, orientation_map_trans_fin_three, ← hoA]
      exact congrArg (Orientation.map (Fin 3) L.symm)
        ((Orientation.map (Fin 3) A).symm_apply_apply _)
    have hOR : Orientation.map (Fin 3) (R.trans B).symm
        (N.orientation.orientation (F (r (t, halfZero)))) =
        Orientation.map (Fin 3) R.symm (C.orientation.orientation (r (t, halfZero))) := by
      rw [LinearEquiv.trans_symm, orientation_map_trans_fin_three, ← hoB]
      exact congrArg (Orientation.map (Fin 3) R.symm)
        ((Orientation.map (Fin 3) B).symm_apply_apply _)
    exact hOL.trans (ho.trans (congrArg Neg.neg hOR.symm))

private theorem orientedFold_comp {A B C : CompactCarrier.{u}}
    {f : B.Carrier → C.Carrier} {g : A.Carrier → B.Carrier}
    (hf : IsOrientedFold f) (hg : IsOrientedFold g)
    (hsf : ContMDiff B.model C.model ∞ f) (hsg : ContMDiff A.model B.model ∞ g) :
    IsOrientedFold (f ∘ g) := by
  intro x
  obtain ⟨L, hL, hoL⟩ := hg x
  obtain ⟨R, hR, hoR⟩ := hf (g x)
  refine ⟨L.trans R, ?_, ?_⟩
  · intro v
    change R (L v) = _
    rw [hR, hL]
    exact (mfderiv_comp_apply x (hsf.mdifferentiable (by simp) _)
      (hsg.mdifferentiable (by simp) _) v).symm
  · rw [orientation_map_trans_fin_three, hoL]
    exact hoR

private theorem sumInl_smooth (C D : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary) :
    ContMDiff C.model (C.withBoundarySum D hC hD).model ∞
      (Sum.inl : C.Carrier → (C.withBoundarySum D hC hD).Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact ContMDiff.inl

private theorem sumInr_smooth (C D : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary) :
    ContMDiff D.model (C.withBoundarySum D hC hD).model ∞
      (Sum.inr : D.Carrier → (C.withBoundarySum D hC hD).Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact ContMDiff.inr

private theorem sumElim_smooth (C D N : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    (f : C.Carrier → N.Carrier) (g : D.Carrier → N.Carrier)
    (hf : ContMDiff C.model N.model ∞ f) (hg : ContMDiff D.model N.model ∞ g) :
    ContMDiff (C.withBoundarySum D hC hD).model N.model ∞ (Sum.elim f g) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact hf.sumElim hg

private theorem sumElim_positive (C D N : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    (f : C.Carrier → N.Carrier) (g : D.Carrier → N.Carrier)
    (hf : IsOrientedFold f) (hg : IsOrientedFold g)
    (hsf : ContMDiff C.model N.model ∞ f) (hsg : ContMDiff D.model N.model ∞ g) :
    IsOrientedFold (C := C.withBoundarySum D hC hD) (Sum.elim f g) := by
  let H : (C.withBoundarySum D hC hD).Carrier → N.Carrier := Sum.elim f g
  have hH := sumElim_smooth C D N hC hD f g hsf hsg
  intro x
  cases x with
  | inl y =>
    let A := C.withBoundarySumInlTangentEquiv D hC hD y
    obtain ⟨R, hR, hoR⟩ := hf y
    refine ⟨A.toLinearEquiv.symm.trans R, ?_, ?_⟩
    · intro v
      have hd := mfderiv_comp_apply y (hH.mdifferentiable (by simp) _)
        ((sumInl_smooth C D hC hD).mdifferentiable (by simp) y) (A.symm v)
      change mfderiv C.model N.model f y (A.symm v) =
        mfderiv (C.withBoundarySum D hC hD).model N.model H (Sum.inl y)
          (A (A.symm v)) at hd
      change R (A.symm v) = _
      rw [hR]
      exact hd.trans (congrArg
        (mfderiv (C.withBoundarySum D hC hD).model N.model H (Sum.inl y))
        (A.apply_symm_apply v))
    · exact (orientation_map_trans_fin_three A.toLinearEquiv.symm R _).trans
        ((congrArg (Orientation.map (Fin 3) R)
          ((congrArg (Orientation.map (Fin 3) A.toLinearEquiv.symm)
            (C.withBoundarySumInl_positive D hC hD y).symm).trans
            ((Orientation.map (Fin 3) A.toLinearEquiv).symm_apply_apply _))).trans hoR)
  | inr y =>
    let A := C.withBoundarySumInrTangentEquiv D hC hD y
    obtain ⟨R, hR, hoR⟩ := hg y
    refine ⟨A.toLinearEquiv.symm.trans R, ?_, ?_⟩
    · intro v
      have hd := mfderiv_comp_apply y (hH.mdifferentiable (by simp) _)
        ((sumInr_smooth C D hC hD).mdifferentiable (by simp) y) (A.symm v)
      change mfderiv D.model N.model g y (A.symm v) =
        mfderiv (C.withBoundarySum D hC hD).model N.model H (Sum.inr y)
          (A (A.symm v)) at hd
      change R (A.symm v) = _
      rw [hR]
      exact hd.trans (congrArg
        (mfderiv (C.withBoundarySum D hC hD).model N.model H (Sum.inr y))
        (A.apply_symm_apply v))
    · exact (orientation_map_trans_fin_three A.toLinearEquiv.symm R _).trans
        ((congrArg (Orientation.map (Fin 3) R)
          ((congrArg (Orientation.map (Fin 3) A.toLinearEquiv.symm)
            (C.withBoundarySumInr_positive D hC hD y).symm).trans
            ((Orientation.map (Fin 3) A.toLinearEquiv).symm_apply_apply _))).trans hoR)

theorem boundarySum_reversal_of_orientedFold
    (C D W : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
    (hD : D.kind = .withBoundary) (hW : W.kind = .withBoundary)
    (F : D.Carrier → W.Carrier) (hF : IsOrientedFold F)
    (hsm : ContMDiff D.model W.model ∞ F)
    (l : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (r : PartialDiffeomorph halfCollarModel D.model
      (Torus × EuclideanHalfSpace 1) D.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    let instC : Nonempty C.Carrier := ⟨l (torusBase, halfZero)⟩
    let instD : Nonempty D.Carrier := ⟨r (torusBase, halfZero)⟩
    ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
      (l.trans (@withBoundarySumLeft C D hC hD instC))
      (fun p => (r.trans (@withBoundarySumRight C D hC hD instD)) (f p.1, p.2)) →
    ReversesBoundaryOrientation (C.withBoundarySum W hC hW)
      (l.trans (@withBoundarySumLeft C W hC hW instC))
      (fun p => Sum.inr (F (r (f p.1, p.2)))) := by
  let instC : Nonempty C.Carrier := ⟨l (torusBase, halfZero)⟩
  let instD : Nonempty D.Carrier := ⟨r (torusBase, halfZero)⟩
  dsimp only
  intro hrev
  let H : (C.withBoundarySum D hC hD).Carrier → (C.withBoundarySum W hC hW).Carrier :=
    Sum.elim Sum.inl (Sum.inr ∘ F)
  have hsH : ContMDiff (C.withBoundarySum D hC hD).model
      (C.withBoundarySum W hC hW).model ∞ H :=
    sumElim_smooth C D (C.withBoundarySum W hC hW) hC hD _ _
      (sumInl_smooth C W hC hW) ((sumInr_smooth C W hC hW).comp hsm)
  have hpH : IsOrientedFold H := by
    apply sumElim_positive
    · intro x
      exact ⟨(C.withBoundarySumInlTangentEquiv W hC hW x).toLinearEquiv,
        fun v => rfl, C.withBoundarySumInl_positive W hC hW x⟩
    · exact orientedFold_comp (A := D) (B := W) (C := C.withBoundarySum W hC hW)
        (fun x => ⟨(C.withBoundarySumInrTangentEquiv W hC hW x).toLinearEquiv,
          fun v => rfl, C.withBoundarySumInr_positive W hC hW x⟩)
        hF (sumInr_smooth C W hC hW) hsm
    · exact sumInl_smooth C W hC hW
    · exact (sumInr_smooth C W hC hW).comp hsm
  let L0 := l.trans (C.withBoundarySumLeft D hC hD)
  let R0 := r.trans (C.withBoundarySumRight D hC hD)
  let Φ : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) :=
    f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  have hL0 : L0.source = halfCollarSource := by
    ext p
    change (p ∈ l.source ∧ l p ∈ (C.withBoundarySumLeft D hC hD).source) ↔ _
    rw [hl, withBoundarySumLeft_source]
    simp
  have hR0 : R0.source = halfCollarSource := by
    ext p
    change (p ∈ r.source ∧ r p ∈ (C.withBoundarySumRight D hC hD).source) ↔ _
    rw [hr, withBoundarySumRight_source]
    simp
  have hLD : ∀ t, MDifferentiableAt halfCollarModel
      (C.withBoundarySum D hC hD).model L0 (t, halfZero) := fun t =>
    L0.mdifferentiableAt (by simp) (hL0.symm ▸ zero_mem_halfCollarSource t)
  have hRD : ∀ t, MDifferentiableAt halfCollarModel
      (C.withBoundarySum D hC hD).model (R0 ∘ Φ) (t, halfZero) := by
    intro t
    exact (R0.mdifferentiableAt (by simp)
      (hR0.symm ▸ zero_mem_halfCollarSource (f t))).comp (t, halfZero)
        (Φ.mdifferentiable (by simp) (t, halfZero))
  have hfold := reversesBoundaryOrientation_of_orientedFold hpH hsH hrev hLD hRD
  apply reversesBoundaryOrientation_congrOn hfold
  · intro p hp
    change H (C.withBoundarySumLeft D hC hD (l p)) =
      C.withBoundarySumLeft W hC hW (l p)
    rw [withBoundarySumLeft_apply, withBoundarySumLeft_apply]
    rfl
  · intro p hp
    change H (C.withBoundarySumRight D hC hD (r (f p.1, p.2))) = _
    rw [withBoundarySumRight_apply]
    rfl

private theorem cutMap_recast_smooth {N A : CompactCarrier.{u}} (T : TorusPresentation N)
    (he : A = T.cutCarrier) :
    ContMDiff A.model N.model ∞ (fun x : A.Carrier => T.cutMap (he ▸ x)) := by
  cases he
  exact T.quotient_smooth

private theorem cutMap_recast_positive {N A : CompactCarrier.{u}} (T : TorusPresentation N)
    (he : A = T.cutCarrier) :
    IsOrientedFold (C := A) (fun x : A.Carrier => T.cutMap (he ▸ x)) := by
  cases he
  exact T.isOrientedFold_cutMap

variable (C W D N : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
  (hW : W.kind = .withBoundary) (hD : D.kind = .withBoundary)
  (hN : N.kind = .withBoundary) (T : TorusPresentation N)
  (hcut : T.cutCarrier = C.withBoundarySum W hC hW)

def firstQuotientSecondFold :
    (D.withBoundarySum W hD hW).Carrier → (N.withBoundarySum D hN hD).Carrier :=
  Sum.elim Sum.inr (fun w => Sum.inl (T.cutMap (hcut.symm ▸ Sum.inr w)))

theorem firstQuotientSecondFold_smooth :
    ContMDiff (D.withBoundarySum W hD hW).model (N.withBoundarySum D hN hD).model ∞
      (firstQuotientSecondFold C W D N hC hW hD hN T hcut) := by
  apply sumElim_smooth
  · exact sumInr_smooth N D hN hD
  · exact (sumInl_smooth N D hN hD).comp
      ((cutMap_recast_smooth T hcut.symm).comp (sumInr_smooth C W hC hW))

theorem firstQuotientSecondFold_positive :
    IsOrientedFold (firstQuotientSecondFold C W D N hC hW hD hN T hcut) := by
  apply sumElim_positive
  · intro x
    exact ⟨(N.withBoundarySumInrTangentEquiv D hN hD x).toLinearEquiv,
      fun v => rfl, N.withBoundarySumInr_positive D hN hD x⟩
  · apply orientedFold_comp
    · intro x
      exact ⟨(N.withBoundarySumInlTangentEquiv D hN hD x).toLinearEquiv,
        fun v => rfl, N.withBoundarySumInl_positive D hN hD x⟩
    · exact orientedFold_comp (A := W) (B := C.withBoundarySum W hC hW) (C := N)
        (cutMap_recast_positive T hcut.symm)
        (fun x => ⟨(C.withBoundarySumInrTangentEquiv W hC hW x).toLinearEquiv,
          fun v => rfl, C.withBoundarySumInr_positive W hC hW x⟩)
        (cutMap_recast_smooth T hcut.symm) (sumInr_smooth C W hC hW)
    · exact sumInl_smooth N D hN hD
    · exact (cutMap_recast_smooth T hcut.symm).comp (sumInr_smooth C W hC hW)
  · exact sumInr_smooth N D hN hD
  · exact (sumInl_smooth N D hN hD).comp
      ((cutMap_recast_smooth T hcut.symm).comp (sumInr_smooth C W hC hW))

variable (Γ : BoundaryTori D 1) (EW : BoundaryTori W 2) (EN : BoundaryTori N 1)

theorem firstQuotientSecondFold_reversal :
    let instD : Nonempty D.Carrier := ⟨Γ.torusMap 0 torusBase⟩
    let instW : Nonempty W.Carrier := ⟨EW.torusMap 0 torusBase⟩
    let instN : Nonempty N.Carrier := ⟨EN.torusMap 0 torusBase⟩
    ∀ {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
      (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      (∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
        EN.collar 0 p = T.cutMap (hcut.symm ▸
          Sum.inr (EW.collar 1 (p.1, halfSpaceScale hδ p.2)))) →
      ReversesBoundaryOrientation (D.withBoundarySum W hD hW)
        (@boundaryPortLeftCollar D W hD hW instD Γ)
        (fun p => @boundaryPortRightCollar D W hD hW instW 1 EW 1 (f p.1, p.2)) →
      ReversesBoundaryOrientation (N.withBoundarySum D hN hD)
        (@boundaryPortLeftCollar N D hN hD instN EN)
        (fun p => boundaryPortRightCollar N D hN hD (Γ.shrink hδ hδ1) 0
          (f.symm p.1, p.2)) := by
  let instD : Nonempty D.Carrier := ⟨Γ.torusMap 0 torusBase⟩
  let instW : Nonempty W.Carrier := ⟨EW.torusMap 0 torusBase⟩
  let instN : Nonempty N.Carrier := ⟨EN.torusMap 0 torusBase⟩
  dsimp only
  intro δ hδ hδ1 f hport hrev
  let L0 := boundaryPortLeftCollar D W hD hW Γ
  let R0 := boundaryPortRightCollar D W hD hW EW 1
  let L1 := boundaryPortRightCollar N D hN hD (Γ.shrink hδ hδ1) 0
  let R1 := boundaryPortLeftCollar N D hN hD EN
  let S : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) := halfShrink (IX := torusModel) hδ
  let Φ : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) :=
    f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  let F := firstQuotientSecondFold C W D N hC hW hD hN T hcut
  have hL0 : L0.source = halfCollarSource := boundaryPortLeftCollar_source D W hD hW Γ
  have hR0 : R0.source = halfCollarSource := boundaryPortRightCollar_source D W hD hW EW 1
  have hL1 : L1.source = halfCollarSource :=
    boundaryPortRightCollar_source N D hN hD (Γ.shrink hδ hδ1) 0
  have hR1 : R1.source = halfCollarSource := boundaryPortLeftCollar_source N D hN hD EN
  have hL : ∀ t, MDifferentiableAt halfCollarModel
      (D.withBoundarySum W hD hW).model L0 (t, halfZero) := fun t =>
    L0.mdifferentiableAt (by simp) (hL0.symm ▸ zero_mem_halfCollarSource t)
  have hR : ∀ t, MDifferentiableAt halfCollarModel
      (D.withBoundarySum W hD hW).model (R0 ∘ Φ) (t, halfZero) := by
    intro t
    exact (R0.mdifferentiableAt (by simp)
      (hR0.symm ▸ zero_mem_halfCollarSource (f t))).comp (t, halfZero)
        (Φ.mdifferentiable (by simp) (t, halfZero))
  have hSz : ∀ t, S (t, halfZero) = (t, halfZero) := fun t =>
    Prod.ext rfl (halfSpaceScale_halfZero hδ)
  have hshr := reversesBoundaryOrientation_comp hrev S id hSz hL hR
  have hLS : ∀ t, MDifferentiableAt halfCollarModel
      (D.withBoundarySum W hD hW).model (L0 ∘ S) (t, halfZero) := by
    intro t
    exact ((hSz t).symm ▸ hL t).comp (t, halfZero)
      (S.mdifferentiable (by simp) (t, halfZero))
  have hRS : ∀ t, MDifferentiableAt halfCollarModel
      (D.withBoundarySum W hD hW).model ((R0 ∘ Φ) ∘ S) (t, halfZero) := by
    intro t
    exact ((hSz t).symm ▸ hR t).comp (t, halfZero)
      (S.mdifferentiable (by simp) (t, halfZero))
  have hfold := reversesBoundaryOrientation_of_orientedFold
    (firstQuotientSecondFold_positive C W D N hC hW hD hN T hcut)
    (firstQuotientSecondFold_smooth C W D N hC hW hD hN T hcut) hshr hLS hRS
  have hshape : ReversesBoundaryOrientation (N.withBoundarySum D hN hD) L1
      (fun p => R1 (f p.1, p.2)) := by
    apply reversesBoundaryOrientation_congrOn hfold
    · intro p hp
      change F (L0 (S p)) = L1 p
      rw [boundaryPortLeftCollar_apply, boundaryPortRightCollar_apply]
      rfl
    · intro p hp
      change F (R0 (Φ (S p))) = R1 (f p.1, p.2)
      rw [boundaryPortRightCollar_apply, boundaryPortLeftCollar_apply]
      change Sum.inl (T.cutMap (hcut.symm ▸
        Sum.inr (EW.collar 1 (f p.1, halfSpaceScale hδ p.2)))) =
          Sum.inl (EN.collar 0 (f p.1, p.2))
      exact congrArg Sum.inl (hport (f p.1, p.2) hp).symm
  exact reversesBoundaryOrientation_swap L1 R1 hL1 hR1 f hshape

end GC.GraphManifold
