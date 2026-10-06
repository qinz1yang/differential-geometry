import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPartitionBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspTorusNoDiskBCF

/-!
# Consumer of the BCF03 G7 partition: `hdisk` PROVED on this route (lane S-BCF03b, G27 / G28)

`BoundaryGaf02ChainE.hdisk_of_partition_BCF`: the input `hdisk` of the cusp dichotomy (a cusp
front off `X₃` misses `P_e`), proved from the first conjunct of G7
(`bcf03_face_partition_part1_BCF`, whose inputs are the F1 numerics, BCF02's five remaining
conjuncts and the strengthened corner record) and the torus count of FC40
(`cuspFront_disjoint_edgePiece_BCF`). It is not an assumption of the final theorem; the cusp
branch `cuspFace_V2b_OBD` (O-BD1) consumes it together with the closedness of `P_e` (G20).
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

/-- **`hdisk` proved on the BCF03 route**: a cusp front off `X₃` misses the edge piece. -/
theorem hdisk_of_partition_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1 / 1000000)
    (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hG6 : Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩
        C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hG6c : ∀ y ∈ C.toChain.stageMap 0 '' Kc.remainder,
      y ∉ relInterior_BIF (Bs.base 0) (C.toChain.stageMap 0 '' Kc.remainder) →
      ∃ (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (L : Finset (CircleFaceLabel74 Kc))
        (φ : CircleFaceLabel74 Kc →
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
        IsOpen O ∧ y ∈ O ∧ 1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0 ∧
          {y' | y' ∈ O ∧ y' ∈ C.toChain.stageMap 0 '' Kc.remainder ∧ φ f y' = 0} =
            {y' | y' ∈ O ∧ y' ∈ C.toChain.stageMap 0 '' Kc.remainder ∧
              Bs.fibre 0 y' ⊆ circleFaceSet74 Kc f}) ∧
        (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
          fun f : L => mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v) ∧
        (C.toChain.stageMap 0 '' Kc.remainder) ∩ O =
          {y' | y' ∈ O ∩ Bs.base 0 ∧ ∀ f ∈ L, φ f y' ≤ 0} ∧
        (∀ f, Bs.fibre 0 y ⊆ circleFaceSet74 Kc f → f ∈ L)) :
    ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ →
      Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece := fun i hi =>
  C.cuspFront_disjoint_edgePiece_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er hG6.2.1
    (C.bcf03_face_partition_part1_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er h3βc hβ2 hγ hγ34 hC hG6
      hG6c) i hi

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
