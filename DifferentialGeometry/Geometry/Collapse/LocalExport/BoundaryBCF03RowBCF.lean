import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPartitionBCFApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsV32OBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgePieceCompactBCF

/-!
# BCF03 G7, the whole row on `(Bs, WF v2b, Z, Kc, er)` (lane S-BCF03c, G30)

`BoundaryGaf02ChainE.bcf03_face_partition_of_rows_BCF`: both conjuncts of the frozen
`bcf03_face_partition_BCF03` (`TargetsBoundary-v3.2`, section ChainE2):

* conjunct 1 (the embedded face partition of every component of `∂M₂`) is
  `bcf03_face_partition_part1_BCF` (G28);
* conjunct 2 (the cusp dichotomy) is `cuspFace_V2b_OBD` (O-BD1) with `hPe := isClosed_edgePiece_BCF
  …` (G20, the eighteen register premises) and `hdisk := hdisk_of_partition_BCF` (G27/G28, the
  FC40 torus count on the partition of the torus component).

Inputs (all of existing shapes, each with its source; nothing is a conclusion of this theorem):
* the frozen premises of the row: E4's block `hrd … hθ` and the eighteen BCF2K register premises;
* F1's call numerics (D77-12) `h3βc : 3βc ≤ β₂`, `hγ : 0 ≤ γ`, `hγ34 : γ ≤ 3/4`,
  `hC : 100(bder + 1)(1 + bcut + cw₀/Σ₀)ΛΔ < 10⁻⁶` (`β₂ < 10⁻⁶` is the register premise `hβ2`,
  hence `< 1`; `c₂ < 10⁻⁵` is `C.validity.c_two_lt_E4`);
* `hG6`: BCF02's five remaining conjuncts (G6, the output of `bcf02_pieces_BCF02`);
* `hG6c : CircleBaseCornersV32 Kc`: the V32 corner record of the circle base (G6c, the output of
  `circle_corners_BCF02`; the label completeness of review 77 R9 is a clause of the record, not
  proved here).

Consumers: `bcf03_counts_of_rows_BCF` (the counts G7' on the partitions produced by the row) and
`boundaryGeometricExports74V32_of_rows_BCF` (the exports of ANY v2b decomposition, with `hG7` and
`hdisk` discharged by the row).
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

/-- **BCF03 G7, the whole row** (see the module docstring for the inputs). -/
theorem bcf03_face_partition_of_rows_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hG6 : Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩
        C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : CircleBaseCornersV32 Kc) :
    (∀ x ∈ frontier Kc.M₂, ∃ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier Kc.M₂) x),
      (∀ i, ∃ y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace,
        Subtype.val '' P.disk i = connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y) ∧
      Subtype.val '' (⋃ j, P.piece j) = connectedComponentIn (frontier Kc.M₂) x ∩ Kc.remainder) ∧
    ∀ i : Fin S.packet.cusp.count,
      (∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
        C.toChain.cuspFront_BIF i ⊆ Kc.piece) ∨
        (∃ x ∈ Kc.remainder, C.toChain.cuspFront_BIF i =
            connectedComponentIn (frontier Kc.remainder) x ∧
          Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :=
  ⟨C.bcf03_face_partition_part1_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er h3βc hβ2 hγ hγ34 hC hG6
      hG6c,
    C.cuspFace_V2b_OBD WF Z hrd hrd4 hrdc hprem hθ Kc
      (Kc.isClosed_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ
        hμΔ)
      (C.hdisk_of_partition_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er h3βc hβ2 hγ hγ34 hC hG6
        hG6c)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
