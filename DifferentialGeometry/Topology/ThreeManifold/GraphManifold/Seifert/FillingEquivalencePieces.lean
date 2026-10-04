import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceSolid
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierModels

/-!
# Actual piece maps for filling equivalence

The canonical product piece map is straightened by an orientation preserving collar correction.
Its genuine host orientation is retained, and all ports share one positive collar germ width.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u v
namespace GC.Seifert

variable {W W' : CompactCarrier.{u}} {T : TorusPresentation W} {D : TorusPresentation W'}
    {i : Fin T.components.count} {i' : Fin D.components.count} {k : ℕ}

theorem ProductFibredPiece.exists_positive_comparison_germ (P : ProductFibredPiece T i k)
    (Q : ProductFibredPiece D i' k)
    (ho : (P.pieceDiffeomorph Q).preservesOrientation
      (T.cutCarrier.orientation.restrictOpen (T.components.piece i))
      (D.cutCarrier.orientation.restrictOpen (D.components.piece i'))) :
    ∃ δ > (0 : ℝ), ∃ H : T.components.piece i ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯
      D.components.piece i',
      H.preservesOrientation (T.cutCarrier.orientation.restrictOpen (T.components.piece i))
        (D.cutCarrier.orientation.restrictOpen (D.components.piece i')) ∧
      ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
        H (T.pieceCollar i (P.port j) p) = D.pieceCollar i' (Q.port j) p := by
  let F := P.pieceDiffeomorph Q
  let Θ := P.trivialization.trans F
  let ψ := Function.const (Fin k) (Diffeomorph.refl torusModel Torus ∞)
  have h0 : ∀ j (t : Torus), D.pieceCollar i' (Q.port j) (ψ j t, halfZero) =
      Θ (P.base.collar j (t.1, halfZero), t.2) := by
    intro j t
    change D.pieceCollar i' (Q.port j) (t, halfZero) = _
    rw [Q.collar_eq j (t, halfZero) (zero_mem_halfCollarSource t)]
    change Q.trivialization (Q.base.collar j (t.1, halfZero), t.2) =
      F (P.trivialization (P.base.collar j (t.1, halfZero), t.2))
    change Q.trivialization (Q.base.collar j (t.1, halfZero), t.2) =
      Q.trivialization (P.base.diffeomorph Q.base
        ((P.trivialization.symm (P.trivialization
          (P.base.collar j (t.1, halfZero), t.2))).1),
        (P.trivialization.symm (P.trivialization
          (P.base.collar j (t.1, halfZero), t.2))).2)
    rw [P.trivialization.symm_apply_apply]
    congr 1
    apply Prod.ext
    · apply Q.base.isSmoothEmbedding.isEmbedding.injective
      rw [PlanarBase.embedding_diffeomorph, Q.base.embedding_collar, P.base.embedding_collar]
    · rfl
  obtain ⟨δ, hδ, Φ, hΦo, hagree, hfix⟩ := exists_boundaryTori_straightening
    (D.trivBoundaryTori i' P.base Q.port ψ Θ h0) (D.pieceBoundaryTori i')
    (fun r => ψ (Q.port.symm ((Fintype.equivFin _).symm r)))
    (D.trivBoundaryTori_collar_zero i' P.base Q.port ψ Θ h0)
  refine ⟨δ, hδ, F.trans Φ, Diffeomorph.preservesOrientation_trans ho hΦo, ?_⟩
  intro j p hp hlt
  rw [P.collar_eq j p hp]
  change Φ (Θ (P.base.collar j (p.1.1, p.2), p.1.2)) = _
  have hh := hagree (Fintype.equivFin _ (Q.port j)) p hp hlt
  have e1 : Q.port.symm ((Fintype.equivFin _).symm (Fintype.equivFin _ (Q.port j))) = j := by
    simp
  have e2 : (Fintype.equivFin _).symm (Fintype.equivFin _ (Q.port j)) = Q.port j := by
    simp
  change Φ (Θ (P.base.collar
    (Q.port.symm ((Fintype.equivFin _).symm (Fintype.equivFin _ (Q.port j))))
      (p.1.1, p.2), p.1.2)) =
    D.pieceCollar i' ((Fintype.equivFin _).symm (Fintype.equivFin _ (Q.port j)))
      (ψ (Q.port.symm ((Fintype.equivFin _).symm (Fintype.equivFin _ (Q.port j)))) p.1,
        p.2) at hh
  rw [e1, e2] at hh
  exact hh

section SolidPieces

variable {V : CompactCarrier.{v}} {E : TorusPresentation V}
    {l : Fin E.components.count}

theorem SolidTorusPiece.exists_comparison_germ_of_solidExtension
    (P : SolidTorusPiece T i) (Q : SolidTorusPiece E l)
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (F : solidTorusSet.{0} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{0})
    (δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
      F (solidTorusCollar p) = solidTorusCollar (φ p.1, p.2)) :
    ∃ η > (0 : ℝ), ∃ H : T.components.piece i ≃ₘ⟮T.cutCarrier.model, E.cutCarrier.model⟯
      E.components.piece l,
      ∀ p ∈ halfCollarSource, p.2.val 0 < η →
        H (T.pieceCollar i (P.port 0) p) = E.pieceCollar l (Q.port 0) (φ p.1, p.2) := by
  obtain ⟨δP, hδP, ΘP, hP⟩ := SolidTorusPiece.exists_lensUnitDisc_germ.{u, 0} P
  obtain ⟨δQ, hδQ, ΘQ, hQ⟩ := SolidTorusPiece.exists_lensUnitDisc_germ.{v, 0} Q
  let G := (solidTorusDiscCircle.{0}.symm.trans F).trans solidTorusDiscCircle
  let H := (ΘP.symm.trans G).trans ΘQ
  refine ⟨min δP (min δQ δ), lt_min hδP (lt_min hδQ hδ), H, ?_⟩
  intro p hp hlt
  have hpP := lt_of_lt_of_le hlt (min_le_left δP (min δQ δ))
  have hpQ := lt_of_lt_of_le hlt
    ((min_le_right δP (min δQ δ)).trans (min_le_left δQ δ))
  have hpF := lt_of_lt_of_le hlt
    ((min_le_right δP (min δQ δ)).trans (min_le_right δQ δ))
  have hφp : (φ p.1, p.2) ∈ halfCollarSource := by
    exact hp
  rw [hP p hp hpP, hQ (φ p.1, p.2) hφp hpQ]
  change ΘQ (G (ΘP.symm (ΘP (cliffordDiscCollarMap (p.1.1, p.2), p.1.2)))) = _
  rw [ΘP.symm_apply_apply]
  apply congrArg ΘQ
  change solidTorusDiscCircle
    (F (solidTorusDiscCircle.symm (cliffordDiscCollarMap (p.1.1, p.2), p.1.2))) = _
  rw [← solidTorusCollar_eq_symm, hF p hp hpF, solidTorusCollar_eq_symm,
    solidTorusDiscCircle.apply_symm_apply]

theorem SolidTorusPiece.exists_linear_comparison_germ
    (P : SolidTorusPiece T i) (Q : SolidTorusPiece E l) (A : GL (Fin 2) ℤ)
    (hA : A • meridianSlope = meridianSlope) :
    ∃ δ > (0 : ℝ), ∃ H : T.components.piece i ≃ₘ⟮T.cutCarrier.model, E.cutCarrier.model⟯
      E.components.piece l,
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        H (T.pieceCollar i (P.port 0) p) =
          E.pieceCollar l (Q.port 0) (linearTorusDiffeomorph A p.1, p.2) := by
  obtain ⟨F, δ, hδ, _, hF⟩ := exists_linear_meridianPreserving_solidTorusDiffeomorph A hA
  exact P.exists_comparison_germ_of_solidExtension Q (linearTorusDiffeomorph A) F δ hδ hF

theorem SolidTorusPiece.exists_comparison_germ_of_mappingClassLinear
    (hT : TorusMappingClassLinear) (P : SolidTorusPiece T i) (Q : SolidTorusPiece E l)
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hμ : torusUnit φ • meridianSlope = meridianSlope) :
    ∃ δ > (0 : ℝ), ∃ H : T.components.piece i ≃ₘ⟮T.cutCarrier.model, E.cutCarrier.model⟯
      E.components.piece l,
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        H (T.pieceCollar i (P.port 0) p) = E.pieceCollar l (Q.port 0) (φ p.1, p.2) := by
  obtain ⟨F, δ, hδ, _, hF⟩ :=
    exists_meridianPreserving_solidTorusDiffeomorph_of_mappingClassLinear hT φ hμ
  exact P.exists_comparison_germ_of_solidExtension Q φ F δ hδ hF

end SolidPieces

end GC.Seifert
