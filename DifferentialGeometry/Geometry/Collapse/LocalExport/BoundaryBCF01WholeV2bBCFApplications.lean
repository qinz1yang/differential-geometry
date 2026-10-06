import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF01WholeV2bBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF03RowBCFApplications

/-!
# Consumer of G30 + G31: the V32 exports with A4 produced and G7, `hdisk` DISCHARGED (lane S-BCF03c)

`exists_boundaryGeometricExports74V32_A4_BCF`: `∃ dec : BoundaryActualDecompositionV2b C.toChain,
BoundaryGeometricExports74V32 C.toChain dec`, where `(Bs, WF v2b, Z, Kc)` is produced by
`exists_bcf01_of_A4_BCF` (A4 whole + F3 + BCF01), `er` by `hG4`, and the two fields `partition` and
`cuspFace` by the BCF03 whole row (`boundaryGeometricExports74V32_of_rows_BCF`). Compared with
`exists_boundaryGeometricExports74b_A4_OBD` (O-BD2b G5) the quantified inputs `hG7` and `hdisk` are
gone; the remaining row inputs are `hG4` (G4 / G4s), `hG6` (G6) and `hG6c` (G6c, V32 record), each
quantified over the produced objects, plus F1's numerics.
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The V32 exports with A4 produced, G7 and `hdisk` discharged by the BCF03 row.** -/
theorem exists_boundaryGeometricExports74V32_A4_BCF
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
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ)
    (hG4 : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      ∃ er : BoundaryRelativeEdgeRestrictionV2 Kc, ∀ ℓ, ∀ y ∈ Bs.base 1, er.faceFun ℓ y = 0 →
        ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
          y ∈ O ∧ ContDiffOn ℝ ∞ (er.faceFun ℓ) O)
    (hG6 : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ (Kc : BoundaryCompactSlimChoiceV2 Bs)
      (er : BoundaryRelativeEdgeRestrictionV2 Kc),
      Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder =
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      BoundaryRelativeEdgeRestrictionV2 Kc → CircleBaseCornersV32 Kc) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec := by
  have hn' : 1140 * Δ ≤ 35 * (n : ℝ) := by linarith
  have hβ2' : β 2 < 1 / 1000000 := by linarith
  have hγ34 : γ ≤ 3 / 4 := by linarith
  obtain ⟨Bs, WF, Z, Kc, -⟩ := C.exists_bcf01_of_A4_BCF hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε
    hγc hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ
  obtain ⟨er, her⟩ := hG4 Bs WF Z Kc
  let dec : BoundaryActualDecompositionV2b C.toChain :=
    { bases := Bs, fibres := WF, zero := Z, slim := Kc, edge := er }
  exact ⟨dec, C.boundaryGeometricExports74V32_of_rows_BCF dec hεr hrd hrd4 hrdc hprem hθ hΔ hΛ hμ
    hτ hσc hn' hT hσs hσs1 hb hs hβ2' hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0 hγ34 hC her
    (hG6 Bs WF Z Kc er) (hG6c Bs WF Z Kc er)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
