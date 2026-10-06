import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentBasesOBDg
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRestrictionBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF01WholeV2bBCFApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersProducerG6C

/-!
# The V32 exports producer with the edge parent in the interior (obstruction O1)

Lane O-BD1 (by S-BD2f, suffix `_OBDg`), group G12b.
`exists_boundaryGeometricExports74V32_A4_rim3_BG4` (HEADPLUG) produces `dec` with its V32 exports
from the register numerics and `hrim`, but forgets the bases it chose. This is the same
construction with the A4 bases of `exists_boundaryGaf02BasesV2b_edgeParent_OBDg` (edge parent
`C.edgeParentSet_OWF`, which lies in `W°`): the conclusion carries `dec.bases.edgeParent ⊆ W°`.
The three supplies are the ones of the layers G6C / BC3d / BC3e / BG4 (`hG4` =
`exists_boundaryRelativeEdgeRestrictionV2_BG4`, `hG6 = bcf02_pieces_of_rest_BC2`,
`hG6c = circleBaseCornersV32_G6C`).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Producer

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The V32 exports with A4 produced and the edge parent in the interior**: inputs as in
`exists_boundaryGeometricExports74V32_A4_rim3_BG4` (the register numerics and `hrim`). -/
theorem exists_boundaryGeometricExports74V32_A4_rim3_interior_OBDg
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
    (hrim : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec ∧
        dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier) := by
  have hn' : 1140 * Δ ≤ 35 * (n : ℝ) := by linarith
  have hβ2' : β 2 < 1 / 1000000 := by linarith
  have hγ34 : γ ≤ 3 / 4 := by linarith
  obtain ⟨Bs, WF, hBs⟩ := C.exists_boundaryGaf02BasesV2b_edgeParent_OBDg hβ2 hγ hd hK hn hμ hτ hσc
    hbA C.validity.c_two_lt_E4 hC hε0 hε hγc hγc1 hβc1
  obtain ⟨Z⟩ := C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ
  obtain ⟨Kc, -⟩ := C.exists_boundaryCompactSlimChoiceV2_clauses_V2b_BCF WF Z hεr hrd hrd4 hrdc
    hprem hθ
  obtain ⟨er, her⟩ := C.exists_boundaryRelativeEdgeRestrictionV2_BG4 WF Z hrd hrd4 hrdc hprem hθ Kc
  have hX1 : Kc.remainder ⊆ Bs.source 0 :=
    Kc.remainder_subset_source_BC2 Z (by linarith) hΛ hμ hσc hσs hσs1 (by linarith) hLΛ
  obtain ⟨hV, hF, hsat⟩ := hrim Bs WF Z Kc
  have hG6 := Kc.bcf02_pieces_of_rest_BC2 er hX1 hV hF hsat
  have hG6c : CircleBaseCornersV32 Kc := by
    obtain ⟨hrem, hRPeq, -, hsat', -⟩ := hG6
    exact C.circleBaseCornersV32_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er hrem hsat' hRPeq.subset
      (Kc.isClosed_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn' hT hσs hσs1 hb hs hβ2' hσL hbη h3b hbH
        hLΛ hμΔ)
  let dec : BoundaryActualDecompositionV2b C.toChain :=
    { bases := Bs, fibres := WF, zero := Z, slim := Kc, edge := er }
  refine ⟨dec, C.boundaryGeometricExports74V32_of_rows_BCF dec hεr hrd hrd4 hrdc hprem hθ hΔ hΛ hμ
    hτ hσc hn' hT hσs hσs1 hb hs hβ2' hσL hbη h3b hbH hLΛ hμΔ h3βc hγ0 hγ34 hC her hG6 hG6c, ?_⟩
  change Bs.edgeParent ⊆ _
  rw [hBs]
  exact C.edgeParentSet_subset_interior_OBDg C.validity.c_two_lt_E4 hC

end BoundaryGaf02ChainE

end Producer

end DifferentialGeometry.Geometry.Collapse
