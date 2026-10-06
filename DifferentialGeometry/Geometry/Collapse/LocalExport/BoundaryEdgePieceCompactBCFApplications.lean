import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgePieceCompactBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspFrontComponentBCFApplications

/-!
# Consumer of G20: the cusp dichotomy with `hPe` discharged (lane S-BCF03)

`BoundaryGaf02ChainE.cuspDichotomy_of_registers_BCF`: `cuspDichotomy_BCF03` (G18) with its explicit
hypothesis `hPe : IsClosed Kc.edgePiece` replaced by BCF02's compactness on the v2 objects
(`isClosed_edgePiece_BCF`, G20) under BCF2K's register premises. The only remaining input is the
torus disk count `hdisk` (G7 part 1).
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

/-- **BCF03's cusp dichotomy with `hPe` discharged**: BCF02's compactness of the edge piece on the
v2 objects (G20) replaces the explicit closedness hypothesis of `cuspDichotomy_BCF03`. -/
theorem cuspDichotomy_of_registers_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hΔ : 2 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (hdisk : ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ →
      Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :
    ∀ i : Fin S.packet.cusp.count,
      (∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
        C.toChain.cuspFront_BIF i ⊆ Kc.piece) ∨
      (∃ x ∈ Kc.remainder, C.toChain.cuspFront_BIF i =
          connectedComponentIn (frontier Kc.remainder) x ∧
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :=
  C.cuspDichotomy_BCF03 WF Z hrd hrd4 hrdc hprem hθ Kc
    (Kc.isClosed_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ)
    hdisk

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
