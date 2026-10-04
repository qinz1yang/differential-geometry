import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingGerms
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingConnected
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalencePieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceGluing
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceOrientation

/-!
# Comparison of actual primitive fillings

Arbitrary primitive slopes determine meridian-preserving solid corrections. Actual extensions of
those corrections and the supplied positive host map combine on the cut pieces, then descend
smoothly to the actual compact carriers. Both quotient squares and every free-port germ are kept.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u

namespace GC.Seifert

private theorem primitiveFillingComparison_of_pieceGerms
    {W W' : CompactCarrier.{u}} {n r : ℕ}
    (B : PrimitiveFillingPresentation W n r) (B' : PrimitiveFillingPresentation W' n r)
    (ψ : Fin r ⊕ Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (g : (i : Option (Fin n)) →
      B.presentation.components.piece (B.piece i) ≃ₘ⟮B.presentation.cutCarrier.model,
        B'.presentation.cutCarrier.model⟯ B'.presentation.components.piece (B'.piece i))
    (ho : (g none).preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none))))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgerm : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
      g none (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2))
    (hsolid : ∀ m p, p ∈ halfCollarSource → p.2.val 0 < δ →
      g (some m) (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p) =
        B'.presentation.pieceCollar (B'.piece (some m)) ((B'.solid m).port 0)
          (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
            (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2)) :
    ∃ (H : B.presentation.cutCarrier.Carrier ≃ₘ⟮B.presentation.cutCarrier.model,
          B'.presentation.cutCarrier.model⟯ B'.presentation.cutCarrier.Carrier)
      (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
      (q : B.presentation.pairing.QuotientSpace ≃ₜ B'.presentation.pairing.QuotientSpace),
      F.preservesOrientation W.orientation W'.orientation ∧
      (∀ x : B.presentation.components.piece (B.piece none), H x.val = (g none x).val) ∧
      (∀ i : Option (Fin n), H '' (B.presentation.components.piece (B.piece i) : Set _) =
        (B'.presentation.components.piece (B'.piece i) : Set _)) ∧
      (∀ m p, p ∈ halfCollarSource → p.2.val 0 < δ →
        H (B.presentation.pairing.leftCollar (B.seam m) p) =
          B'.presentation.pairing.leftCollar (B'.seam m)
            (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
              (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2)) ∧
      (∀ x, q (B.presentation.pairing.quotientMap x) =
        B'.presentation.pairing.quotientMap (H x)) ∧
      (∀ z, F (B.presentation.reconstruction z) = B'.presentation.reconstruction (q z)) ∧
      (∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
        F (B.presentation.external.collar (B.free a) p) =
          B'.presentation.external.collar (B'.free a) (ψ (.inl a) p.1, p.2)) := by
  let T := B.presentation
  let D := B'.presentation
  let H := B.cutDiffeomorph B' g
  let e := B.seam.symm.trans B'.seam
  let A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) := fun k =>
    primitiveFillingCorrection (T.pairing.matching k)
      (D.pairing.matching (e k)) (ψ (.inr (B.seam.symm k)))
  have hl : ∀ k t s (hs : 0 ≤ s), s < δ →
      H (T.pairing.leftCollar k (t, halfPoint s hs)) =
        D.pairing.leftCollar (e k) (A k t, halfPoint s hs) := by
    intro k t s hs hlt
    have hp : (t, halfPoint s hs) ∈ halfCollarSource := lt_of_lt_of_le hlt hδ1
    have hh := B.cutDiffeomorph_solid_germ B' g ψ δ hsolid (B.seam.symm k)
      (t, halfPoint s hs) hp hlt
    simpa only [e, A, Equiv.trans_apply, Equiv.apply_symm_apply] using hh
  have hr : ∀ k t s (hs : 0 ≤ s), s < δ →
      H (T.pairing.rightCollar k (T.pairing.matching k t, halfPoint s hs)) =
        D.pairing.rightCollar (e k) (D.pairing.matching (e k) (A k t), halfPoint s hs) := by
    intro k t s hs hlt
    have hp : (T.pairing.matching k t, halfPoint s hs) ∈ halfCollarSource :=
      lt_of_lt_of_le hlt hδ1
    have hh := B.cutDiffeomorph_host_germ B' g ψ δ hgerm (.inr (B.seam.symm k))
      (T.pairing.matching k t, halfPoint s hs) hp hlt
    rw [B.filled_port, B'.filled_port] at hh
    have hc : D.pairing.matching (e k) (A k t) =
        ψ (.inr (B.seam.symm k)) (T.pairing.matching k t) :=
      primitiveFillingCorrection_square _ _ _ t
    rw [hc]
    simpa only [TorusPresentation.sideCollar, e, Equiv.trans_apply,
      Equiv.apply_symm_apply] using hh
  let F := T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr
  have hcomm (x : T.cutCarrier.Carrier) : F (T.cutMap x) = D.cutMap (H x) :=
    T.fillingComparisonDiffeomorph_cutMap D H e A δ hδ hδ1 hl hr x
  let q := (T.reconstruction.trans F.toHomeomorph).trans D.reconstruction.symm
  have hq (z : T.pairing.QuotientSpace) : F (T.reconstruction z) = D.reconstruction (q z) :=
    (D.reconstruction.apply_symm_apply _).symm
  let : ConnectedSpace W.Carrier := B.connectedSpace
  let x : T.components.piece (B.piece none) :=
    Classical.choice (T.components.connected (B.piece none)).toNonempty
  have hpositive : F.preservesOrientation W.orientation W'.orientation :=
    fillingComparison_oriented_of_cutPoint T D H F hcomm x.val
      (B.cutDiffeomorph_host_orientation B' g ho x)
  let eE := B.free.symm.trans B'.free
  let ψE : Fin T.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) := fun a =>
    ψ (.inl (B.free.symm a))
  have hE : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
      H (T.cutExternal.collar a p) = D.cutExternal.collar (eE a) (ψE a p.1, p.2) := by
    intro a p hp hlt
    have hh := B.cutDiffeomorph_host_germ B' g ψ δ hgerm (.inl (B.free.symm a)) p hp hlt
    rw [B.free_port, B'.free_port] at hh
    simpa only [TorusPresentation.sideCollar, eE, ψE, Equiv.trans_apply,
      Equiv.apply_symm_apply] using hh
  refine ⟨H, F, q, hpositive, ?_, ?_, ?_, ?_, hq, ?_⟩
  · exact fun y => B.cutDiffeomorph_piece B' g none y
  · exact fun i => B.cutDiffeomorph_image_piece B' g i
  · exact fun m p hp hlt => B.cutDiffeomorph_solid_germ B' g ψ δ hsolid m p hp hlt
  · intro y
    apply D.reconstruction.injective
    rw [← hq]
    exact hcomm y
  · intro a p hp hlt
    have hh := T.fillingComparisonDiffeomorph_free_germ D H e A δ hδ hδ1 hl hr
      eE ψE hE (B.free a) p hp hlt
    simpa only [eE, ψE, Equiv.trans_apply, Equiv.symm_apply_apply] using hh

theorem exists_primitiveFillingComparison_of_mappingClassLinear
    (hT : TorusMappingClassLinear) {W W' : CompactCarrier.{u}} {n r : ℕ}
    (B : PrimitiveFillingPresentation W n r) (B' : PrimitiveFillingPresentation W' n r)
    (ψ : Fin r ⊕ Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (h : B.presentation.components.piece (B.piece none) ≃ₘ⟮B.presentation.cutCarrier.model,
      B'.presentation.cutCarrier.model⟯
        B'.presentation.components.piece (B'.piece none))
    (ho : h.preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none))))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hgerm : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ₀ →
      h (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2))
    (hslope : ∀ m, torusUnit (ψ (.inr m)) • B.slope m = B'.slope m) :
    ∃ (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
      ∃ (H : B.presentation.cutCarrier.Carrier ≃ₘ⟮B.presentation.cutCarrier.model,
          B'.presentation.cutCarrier.model⟯
            B'.presentation.cutCarrier.Carrier)
        (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
        (q : B.presentation.pairing.QuotientSpace ≃ₜ B'.presentation.pairing.QuotientSpace),
      F.preservesOrientation W.orientation W'.orientation ∧
      (∀ x : B.presentation.components.piece (B.piece none), H x.val = (h x).val) ∧
      (∀ i : Option (Fin n), H '' (B.presentation.components.piece (B.piece i) : Set _) =
        (B'.presentation.components.piece (B'.piece i) : Set _)) ∧
      (∀ m p, p ∈ halfCollarSource → p.2.val 0 < δ →
        H (B.presentation.pairing.leftCollar (B.seam m) p) =
          B'.presentation.pairing.leftCollar (B'.seam m)
            (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
              (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2)) ∧
      (∀ x, q (B.presentation.pairing.quotientMap x) =
        B'.presentation.pairing.quotientMap (H x)) ∧
      (∀ z, F (B.presentation.reconstruction z) = B'.presentation.reconstruction (q z)) ∧
      (∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
        F (B.presentation.external.collar (B.free a) p) =
          B'.presentation.external.collar (B'.free a) (ψ (.inl a) p.1, p.2)) := by
  have hext : ∀ m : Fin n, ∃ δ > (0 : ℝ),
      ∃ f : B.presentation.components.piece (B.piece (some m)) ≃ₘ⟮B.presentation.cutCarrier.model,
        B'.presentation.cutCarrier.model⟯
          B'.presentation.components.piece (B'.piece (some m)),
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        f (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p) =
          B'.presentation.pieceCollar (B'.piece (some m)) ((B'.solid m).port 0)
            (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
              (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2) := by
    intro m
    exact SolidTorusPiece.exists_comparison_germ_of_mappingClassLinear hT (B.solid m)
      (B'.solid m) _ (B.correction_preserves_meridian B' ψ hslope m)
  choose δ hδ f hf using hext
  obtain ⟨ε, hε, hbounds⟩ := exists_primitiveFilling_common_width δ₀ δ hδ₀ hδ
  have hε₀ : ε ≤ δ₀ := hbounds.2.1
  have hεm : ∀ m, ε ≤ δ m := hbounds.2.2
  have hε1 : ε ≤ 1 := hε₀.trans hδ₀1
  let g : (i : Option (Fin n)) →
      B.presentation.components.piece (B.piece i) ≃ₘ⟮B.presentation.cutCarrier.model,
        B'.presentation.cutCarrier.model⟯ B'.presentation.components.piece (B'.piece i) :=
    fun i => match i with
    | none => h
    | some m => f m
  have hh : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < ε →
      g none (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2) := fun a p hp hlt => hgerm a p hp (lt_of_lt_of_le hlt hε₀)
  have hs : ∀ m p, p ∈ halfCollarSource → p.2.val 0 < ε →
      g (some m) (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p) =
        B'.presentation.pieceCollar (B'.piece (some m)) ((B'.solid m).port 0)
          (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
            (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2) :=
    fun m p hp hlt => hf m p hp (lt_of_lt_of_le hlt (hεm m))
  exact ⟨ε, hε, hε1, primitiveFillingComparison_of_pieceGerms B B' ψ g ho ε hε hε1 hh hs⟩

theorem exists_primitiveFillingComparison_of_linearCorrection
    {W W' : CompactCarrier.{u}} {n r : ℕ}
    (B : PrimitiveFillingPresentation W n r) (B' : PrimitiveFillingPresentation W' n r)
    (ψ : Fin r ⊕ Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (h : B.presentation.components.piece (B.piece none) ≃ₘ⟮B.presentation.cutCarrier.model,
      B'.presentation.cutCarrier.model⟯
        B'.presentation.components.piece (B'.piece none))
    (ho : h.preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none))))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hgerm : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ₀ →
      h (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2))
    (hslope : ∀ m, torusUnit (ψ (.inr m)) • B.slope m = B'.slope m)
    (hlinear : ∀ m,
      primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
        (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) =
      linearTorusDiffeomorph (torusUnit (primitiveFillingCorrection
        (B.presentation.pairing.matching (B.seam m))
        (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m))))) :
    ∃ (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
      ∃ (H : B.presentation.cutCarrier.Carrier ≃ₘ⟮B.presentation.cutCarrier.model,
          B'.presentation.cutCarrier.model⟯
            B'.presentation.cutCarrier.Carrier)
        (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
        (q : B.presentation.pairing.QuotientSpace ≃ₜ B'.presentation.pairing.QuotientSpace),
      F.preservesOrientation W.orientation W'.orientation ∧
      (∀ x : B.presentation.components.piece (B.piece none), H x.val = (h x).val) ∧
      (∀ i : Option (Fin n), H '' (B.presentation.components.piece (B.piece i) : Set _) =
        (B'.presentation.components.piece (B'.piece i) : Set _)) ∧
      (∀ m p, p ∈ halfCollarSource → p.2.val 0 < δ →
        H (B.presentation.pairing.leftCollar (B.seam m) p) =
          B'.presentation.pairing.leftCollar (B'.seam m)
            (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
              (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2)) ∧
      (∀ x, q (B.presentation.pairing.quotientMap x) =
        B'.presentation.pairing.quotientMap (H x)) ∧
      (∀ z, F (B.presentation.reconstruction z) = B'.presentation.reconstruction (q z)) ∧
      (∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
        F (B.presentation.external.collar (B.free a) p) =
          B'.presentation.external.collar (B'.free a) (ψ (.inl a) p.1, p.2)) := by
  have hext : ∀ m : Fin n, ∃ δ > (0 : ℝ),
      ∃ f : B.presentation.components.piece (B.piece (some m)) ≃ₘ⟮B.presentation.cutCarrier.model,
        B'.presentation.cutCarrier.model⟯
          B'.presentation.components.piece (B'.piece (some m)),
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        f (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p) =
          B'.presentation.pieceCollar (B'.piece (some m)) ((B'.solid m).port 0)
            (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
              (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2) := by
    intro m
    obtain ⟨δ, hδ, f, hf⟩ := SolidTorusPiece.exists_linear_comparison_germ (B.solid m)
      (B'.solid m) _ (B.correction_preserves_meridian B' ψ hslope m)
    refine ⟨δ, hδ, f, ?_⟩
    rw [← hlinear m] at hf
    exact hf
  choose δ hδ f hf using hext
  obtain ⟨ε, hε, hbounds⟩ := exists_primitiveFilling_common_width δ₀ δ hδ₀ hδ
  have hε₀ : ε ≤ δ₀ := hbounds.2.1
  have hεm : ∀ m, ε ≤ δ m := hbounds.2.2
  have hε1 : ε ≤ 1 := hε₀.trans hδ₀1
  let g : (i : Option (Fin n)) →
      B.presentation.components.piece (B.piece i) ≃ₘ⟮B.presentation.cutCarrier.model,
        B'.presentation.cutCarrier.model⟯ B'.presentation.components.piece (B'.piece i) :=
    fun i => match i with
    | none => h
    | some m => f m
  have hh : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < ε →
      g none (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2) := fun a p hp hlt => hgerm a p hp (lt_of_lt_of_le hlt hε₀)
  have hs : ∀ m p, p ∈ halfCollarSource → p.2.val 0 < ε →
      g (some m) (B.presentation.pieceCollar (B.piece (some m)) ((B.solid m).port 0) p) =
        B'.presentation.pieceCollar (B'.piece (some m)) ((B'.solid m).port 0)
          (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
            (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2) :=
    fun m p hp hlt => hf m p hp (lt_of_lt_of_le hlt (hεm m))
  exact ⟨ε, hε, hε1, primitiveFillingComparison_of_pieceGerms B B' ψ g ho ε hε hε1 hh hs⟩


end GC.Seifert
