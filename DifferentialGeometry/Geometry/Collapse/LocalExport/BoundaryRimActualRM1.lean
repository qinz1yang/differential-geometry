import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimVerticalRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemainderSaturatedRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemainderInSourceBC2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRestrictionBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStrongCertificateHeadOBDg

/-!
# BCF02 rim clauses, G5: `hG6` assembled and `hrim` removed from the boundary heads (lane S-RIM81)

External review 81 (e), D81-11. On the actual chain, every input of `bcf02_pieces_of_rest_BC2` is
produced: `hX1` (`remainder_subset_source_BC2`), `hV`, `hF` (G2) and `hsat` (G4).

* `BoundaryGaf02ChainE.bcf02_pieces_actual_RM1`: the five-conjunct `hG6` of BCF02, exact type of
  `bcf02_pieces_of_rest_BC2`, nothing but the interface objects and register numerics as inputs;
* `BoundaryGaf02ChainE.rim3_actual_RM1`: the rim conjunction `hV ∧ hF ∧ hsat` for EVERY v2b
  decomposition `(Bs, WF, Z, Kc)` (the `hrim` of the V32 heads); the labelled edge restriction `er`
  of each `Kc` is the G4 producer's (`exists_boundaryRelativeEdgeRestrictionV2_BG4`);
* `boundary_rows_of_actual_decomposition74_V32_RM1`, `boundary_graphPresentation_V32_A4_RM1`,
  `boundary_strongCertificate_V32_A4_RM1`: the `_OBDg` heads with `hrim` removed; the only inputs
  left are the register numerics.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCF02's `hG6`, every atomic input produced** (review 81, D81-11): `hX1` from the register
numerics (`remainder_subset_source_BC2`), `hV`, `hF` (`_RM1`, G2) and `hsat`
(`remainder_saturated_actual_RM1`, G4) in `bcf02_pieces_of_rest_BC2`. -/
theorem bcf02_pieces_actual_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) (hγ34 : γ ≤ 3 / 4) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) :
    Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0 :=
  Kc.bcf02_pieces_of_rest_BC2 er (Kc.remainder_subset_source_BC2 Z hΔ hΛ hμ hσc hσs hσs1 hγ34 hLΛ)
    (C.verticalFace_subset_remainder_RM1 WF Kc er) (C.remainder_inter_frontier_subset_RM1 WF Kc er)
    (Kc.remainder_saturated_actual_RM1 WF Z
      (Kc.remainder_subset_source_BC2 Z hΔ hΛ hμ hσc hσs hσs1 hγ34 hLΛ))

/-- **The rim conjunction `hV ∧ hF ∧ hsat` for every v2b decomposition** (the `hrim` of the V32
heads), produced: the labelled edge restriction of `Kc` is the G4 producer's. -/
theorem rim3_actual_RM1 {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hγ34 : γ ≤ 3 / 4)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder := by
  intro Bs WF Z Kc
  obtain ⟨er, -⟩ := C.exists_boundaryRelativeEdgeRestrictionV2_BG4 WF Z hrd hrd4 hrdc hprem hθ Kc
  exact ⟨C.verticalFace_subset_remainder_RM1 WF Kc er,
    C.remainder_inter_frontier_subset_RM1 WF Kc er,
    Kc.remainder_saturated_actual_RM1 WF Z
      (Kc.remainder_subset_source_BC2 Z hΔ hΛ hμ hσc hσs hσs1 hγ34 hLΛ)⟩

include C in
/-- **The V32 rows head with `hrim` produced** (`_OBDg` with `hrim := rim3_actual_RM1`): the
register numerics are the only inputs. -/
theorem boundary_rows_of_actual_decomposition74_V32_RM1
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec ∧
      ∃ Et : BoundaryTori W S.packet.cusp.count,
        (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
        ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw := by
  exact C.boundary_rows_of_actual_decomposition74_V32_OBDg hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε
    hγc hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs
    hσs1 hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0
    (C.rim3_actual_RM1 hrd hrd4 hrdc hprem hθ (by linarith) hΛ hμ hσc hσs hσs1 (by linarith) hLΛ)

include C in
/-- **G8 (separated branch) with `hrim` produced**: the register numerics are the only
inputs. -/
theorem boundary_graphPresentation_V32_A4_RM1
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  exact C.boundary_graphPresentation_V32_A4_OBDg hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε hγc
    hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs
    hσs1 hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0
    (C.rim3_actual_RM1 hrd hrd4 hrdc hprem hθ (by linarith) hΛ hμ hσc hσs hσs1 (by linarith) hLΛ)

include C in
/-- **§R final shape on V2b / V32 with NO non-register input**: the decomposition with its V32
exports, the packet-labelled tori, the linked rows and the strong certificate on the SAME rows;
the only inputs are the register numerics (`_OBDg` with `hrim := rim3_actual_RM1`). -/
theorem boundary_strongCertificate_V32_A4_RM1
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec ∧
      ∃ Et : BoundaryTori W S.packet.cusp.count,
        (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
        ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw ∧
          Nonempty (StrongCertificate W Et) := by
  exact C.boundary_strongCertificate_V32_A4_OBDg hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε hγc
    hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs
    hσs1 hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0
    (C.rim3_actual_RM1 hrd hrd4 hrdc hprem hθ (by linarith) hΛ hμ hσc hσs hσs1 (by linarith) hLΛ)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
