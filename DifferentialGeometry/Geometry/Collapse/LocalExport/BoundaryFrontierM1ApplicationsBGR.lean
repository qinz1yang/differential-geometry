import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR

/-!
# Consumers of F4c / F5 / F5z (point-set halves) on the enhanced chain (lane B-BCG-ROWS)

The saturation identities `face ∩ X₃ = X₃ ∩ f₃⁻¹(f₃(face ∩ X₃))` and
`front ∩ X₃ = X₃ ∩ f₃⁻¹(f₃(front ∩ X₃))` — the `hSX` input of the closed chapter's
`eq_fiber_of_isPreconnected_of_isolated` (ZSP03 `j = 3`), whose remaining input for F5 / F5z is the
isolation of the base value.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

/-- **A zero face is saturated over `X₃`**: `(ZF)_k ∩ X₃ = X₃ ∩ f₃⁻¹(f₃((ZF)_k ∩ X₃))`. -/
theorem zeroFace_inter_source_eq_preimage_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (k : S.ZeroIdx_BAUGC) :
    C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2 = Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
      (C.toChain.stageMap 2 '' (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2)) := by
  ext q
  constructor
  · rintro ⟨hq, hqX⟩
    exact ⟨hqX, q, ⟨hq, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hp, hpX⟩, hpq⟩
    exact ⟨C.zeroFace_fibre_subset_BGR WF Z hrd hrd4 hrdc hprem hθ k hp hpX ⟨hqX, hpq.symm⟩, hqX⟩

/-- **A cusp front is saturated over `X₃`**: `H_b ∩ X₃ = X₃ ∩ f₃⁻¹(f₃(H_b ∩ X₃))`. -/
theorem cuspFront_inter_source_eq_preimage_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    C.toChain.cuspFront_BIF i ∩ Bs.source 2 = Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
      (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2)) := by
  ext q
  constructor
  · rintro ⟨hq, hqX⟩
    exact ⟨hqX, q, ⟨hq, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hp, hpX⟩, hpq⟩
    exact ⟨C.cuspFront_fibre_subset_BGR WF Z hrd hrd4 hrdc hprem hθ i hp hpX ⟨hqX, hpq.symm⟩, hqX⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
