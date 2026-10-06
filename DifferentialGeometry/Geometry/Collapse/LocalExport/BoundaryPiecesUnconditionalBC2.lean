import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemainderInSourceBC2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesRestBC2

/-!
# BCF02 pieces, part 4: the unconditional conjuncts of `bcf02_pieces_BCF02` (lane S-BCF02b, G4)

Everything of the frozen `bcf02_pieces_BCF02` that holds with no input from the open rim clauses
(`hV`, `hF`, `hsat`, external review 81):

* `isCompact_remainder_BC2`: `R_c` is compact (closed in the compact carrier `W`);
* `M₂_eq_edgePiece_union_remainder_BC2`: `M₂ = P_e ∪ R_c` on the v2 objects;
* **`bcf02_pieces_unconditional_BC2`**: conjunct 1 (`P_e` compact, `isCompact_edgePiece_BCF`),
  conjunct 2, conjunct 3, conjunct 4 (`R_c ⊆ X₁`, `remainder_subset_source_BC2`), the easy halves of
  conjuncts 5 and 6 (`P_e ∩ R_c ⊆ V_e`, `∂M₂ ∖ int H_e ⊆ R_c ∩ ∂M₂`) and the last conjunct (corner
  depth ≤ 2). Premises: the register block of `isCompact_edgePiece_BCF` and `γ ≤ 3/4` (needed by
  the circle cover of `hX1`, as in the BCF03 row).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryCompactSlimChoiceV2

/-- **`R_c` is compact**: it is closed in the compact carrier. -/
theorem isCompact_remainder_BC2 (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    IsCompact Kc.remainder :=
  (isClosed_sdiff_relInterior_BCF Kc.isClosed_M₂_BCF Kc.edgePiece).isCompact

/-- **`M₂ = P_e ∪ R_c`** on the v2 objects. -/
theorem M₂_eq_edgePiece_union_remainder_BC2 (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    Kc.M₂ = Kc.edgePiece ∪ Kc.remainder := by
  refine Subset.antisymm (fun x hx => ?_) (union_subset (fun x hx => hx.1) fun x hx => hx.1)
  by_cases h : x ∈ relInterior_BIF Kc.M₂ Kc.edgePiece
  · exact Or.inl (relInterior_subset_BIF _ _ h)
  · exact Or.inr ⟨hx, h⟩

/-- **The unconditional conjuncts of `bcf02_pieces_BCF02`**: compactness of `P_e` and `R_c`,
`M₂ = P_e ∪ R_c`, `R_c ⊆ X₁`, the easy halves `P_e ∩ R_c ⊆ V_e` and
`∂M₂ ∖ int H_e ⊆ R_c ∩ ∂M₂`, and the corner depth. -/
theorem bcf02_pieces_unconditional_BC2 (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) (hγ34 : γ ≤ 3 / 4) :
    IsCompact Kc.edgePiece ∧ IsCompact Kc.remainder ∧ Kc.M₂ = Kc.edgePiece ∪ Kc.remainder ∧
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace ∧
      frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ⊆
        Kc.remainder ∩ frontier Kc.M₂ ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.stageMap 1 p) = 0 :=
  ⟨Kc.isCompact_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ,
    Kc.isCompact_remainder_BC2, Kc.M₂_eq_edgePiece_union_remainder_BC2,
    Kc.remainder_subset_source_BC2 Z (by linarith) hΛ hμ hσc hσs hσs1 hγ34 hLΛ,
    Kc.edgePiece_inter_remainder_subset_BC2, Kc.frontier_sdiff_subset_remainder_BC2,
    fun _ hp => er.corner_unique_BC2 hp⟩

end BoundaryCompactSlimChoiceV2

end DifferentialGeometry.Geometry.Collapse
