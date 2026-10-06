import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFaceSaturatedBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainDefiningBGR

/-!
# Consumer of the v2 `face_saturated` (S-BCG-ROWS2 G25)

* **`M₁_saturated_unconditional_BGR`**: BCG07 F4d (`M₁ ∩ X_st` saturated, `st ≠ 1`) on the enhanced
  chain from the v2 bases `Bs` and whole-fibre layer `WF` alone (the analytic half of the actual
  zero domains is G22's `exists_boundaryZeroDefining_BGR`; no `face_param`, no `Z`).
* `slimSource_inter_preimage_unconditional_BGR`: `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`.
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

/-- **F4d on the enhanced chain, unconditional** (premises: `εr < 1/2` of ZSP02, E4's `r_∂` block,
`θ < 1/100`; inputs: the v2 bases and the whole-fibre layer). -/
theorem M₁_saturated_unconditional_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ st : Fin 3, st ≠ 1 → C.toChain.M₁_BIFc ∩ Bs.source st =
      Bs.source st ∩ C.toChain.stageMap st ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
        Bs.source st)) := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact C.M₁_saturated_of_defining_BGR WF Zd hrd hrd4 hrdc hprem hθ

/-- **`X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`** (the slim base domain `D₃ = f₃(M₁ ∩ X₃)`), unconditional. -/
theorem slimSource_inter_preimage_unconditional_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
      C.toChain.M₁_BIFc ∩ Bs.source 2 :=
  (C.M₁_saturated_unconditional_BGR WF hεr hrd hrd4 hrdc hprem hθ 2 (by decide)).symm

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
