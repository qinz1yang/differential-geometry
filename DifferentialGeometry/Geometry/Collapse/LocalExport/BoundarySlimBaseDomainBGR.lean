import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimDomainFrontierBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFaceSaturatedApplicationsBGR

/-!
# The relative frontier of `D₃` without the standard face parametrization (S-BCG-ROWS2 G29)

B-BCF134's `relFrontier_slimBaseDomain_subset_BCF` takes the structure
`Z : BoundaryActualZeroDomains_BIFc` but uses only its field `face_saturated`. With G25's
`face_saturated_actual_BGR` (from the analytic half of the actual zero domains and the connected
whole fibres) the statement holds on the enhanced chain from `Bs`, `WF` and E4's premises:

* **`relFrontier_slimBaseDomain_of_chain_BGR`**: `D₃ ∖ int_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)` (BCF01 G1a
  input).
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

/-- **`D₃ ∖ int_{B₃} D₃ ⊆ f₃(∂M₁ ∩ X₃)` on the enhanced chain** (properness of `f₃|X₃` and the
saturation of `M₁`, `face_saturated_actual_BGR`; premises `hεr : εr < 1/2` of ZSP02 and E4's). -/
theorem relFrontier_slimBaseDomain_of_chain_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
      C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact relFrontier_image_subset_BCF (Bs.continuousOn_stageMap_BCF 2) (Bs.image_eq 2)
    (Bs.proper 2) C.toChain.isClosed_M₁_BCF fun p hp q hq hpq hpM =>
    C.face_saturated_actual_BGR WF Zd hrd hrd4 hrdc hprem hθ 2 (by decide) p hp q hq hpq hpM

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
