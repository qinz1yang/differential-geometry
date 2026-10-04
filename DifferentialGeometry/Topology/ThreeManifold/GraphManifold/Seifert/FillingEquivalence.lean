import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceSign
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingComparison

/-!
# Equivalence of actual positive Seifert fillings

Equal positive slope data and port assignments determine a full smooth filling comparison.
The actual host orientation is retained, and every free port has a common product collar germ.
The general boundary correction uses the explicitly supplied smooth mapping class input.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

theorem exists_collarFillingDiffeomorph_of_mappingClassLinear
    (hT : TorusMappingClassLinear) {W W' : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (B' : SeifertBlock W' d) (hport : B.port = B'.port)
    (ho : (B.product.pieceDiffeomorph B'.product).preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none)))) :
    ∃ F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier,
      F.preservesOrientation W.orientation W'.orientation ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        ∀ r p, p ∈ halfCollarSource → p.2.val 0 < δ →
          F (B.presentation.external.collar (B.free r) p) =
            B'.presentation.external.collar (B'.free r) p := by
  obtain ⟨η, hη, H, hHo, hHgerm⟩ :=
    B.product.exists_positive_comparison_germ B'.product ho
  let δ₀ := min η 1
  have hδ₀ : 0 < δ₀ := lt_min hη zero_lt_one
  have hδ₀1 : δ₀ ≤ 1 := min_le_right η 1
  let ψ := Function.const (Fin d.ports ⊕ Fin d.fillingCount)
    (Diffeomorph.refl torusModel Torus ∞)
  have hgerm : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ₀ →
      H (B.toPrimitiveFilling.presentation.pieceCollar (B.toPrimitiveFilling.piece none)
        (B.toPrimitiveFilling.product.port (B.toPrimitiveFilling.port a)) p) =
      B'.toPrimitiveFilling.presentation.pieceCollar (B'.toPrimitiveFilling.piece none)
        (B'.toPrimitiveFilling.product.port (B'.toPrimitiveFilling.port a))
          (ψ a p.1, p.2) := by
    intro a p hp hlt
    change H (B.presentation.pieceCollar (B.piece none)
      ((B.product.fillingCast d.ports_add_fillingCount.symm).port
        (Fin.cast d.ports_add_fillingCount.symm (B.port a))) p) =
      B'.presentation.pieceCollar (B'.piece none)
        ((B'.product.fillingCast d.ports_add_fillingCount.symm).port
          (Fin.cast d.ports_add_fillingCount.symm (B'.port a))) p
    rw [ProductFibredPiece.fillingCast_port, ProductFibredPiece.fillingCast_port, ← hport]
    exact hHgerm (B.port a) p hp (lt_of_lt_of_le hlt (min_le_left η 1))
  have hslope : ∀ m, torusUnit (ψ (.inr m)) • B.toPrimitiveFilling.slope m =
      B'.toPrimitiveFilling.slope m := by
    intro m
    have hunit : torusUnit (Diffeomorph.refl torusModel Torus ∞) = 1 := by
      apply Units.ext
      exact torusMatrix_refl
    change torusUnit (Diffeomorph.refl torusModel Torus ∞) • _ = _
    rw [hunit, one_smul]
    rfl
  obtain ⟨δ, hδ, hδ1, K, F, q, hFo, hhost, himage, hsolid, hq, hFq, hfree⟩ :=
    exists_primitiveFillingComparison_of_mappingClassLinear hT B.toPrimitiveFilling
      B'.toPrimitiveFilling ψ H hHo δ₀ hδ₀ hδ₀1 hgerm hslope
  exact ⟨F, hFo, δ, hδ, hδ1, fun r p hp hlt => hfree r p hp hlt⟩

end GC.Seifert
