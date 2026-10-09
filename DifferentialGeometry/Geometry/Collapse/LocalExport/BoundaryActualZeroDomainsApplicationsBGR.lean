import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualZeroDomainsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimDomainFrontierBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceV2Corollaries

/-!
# Consumers of the produced actual zero domains (S-BCG-ROWS2 G32)

With `exists_boundaryActualZeroDomains_BGR` the structure `BoundaryActualZeroDomains_BIFc` is
produced on the enhanced chain; its existing consumers apply: BIFACEd's
`slimSource_inter_preimage_BIF` (`X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`, F4d) and B-BCF134's
`relFrontier_slimBaseDomain_subset_BCF` (`D₃ ∖ int D₃ ⊆ f₃(∂M₁ ∩ X₃)`, BCF01 G1a input).

* **`slim_baseDomain_facts_of_zeroDomains_BGR`**.
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
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {Bs : BoundaryGaf02BasesV2 C.toChain}

/-- **The produced `Z` feeds BIFACEd's and B-BCF134's consumers**: `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃` and
`D₃ ∖ int_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)`. -/
theorem slim_baseDomain_facts_of_zeroDomains_BGR (WF : BoundaryWholeFiberSpecV2b C.toChain Bs)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
        C.toChain.M₁_BIFc ∩ Bs.source 2 ∧
      Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
        C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) := by
  obtain ⟨Z⟩ := C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ
  exact ⟨Z.slimSource_inter_preimage_BIF, Z.relFrontier_slimBaseDomain_subset_BCF⟩

end DifferentialGeometry.Geometry.Collapse
