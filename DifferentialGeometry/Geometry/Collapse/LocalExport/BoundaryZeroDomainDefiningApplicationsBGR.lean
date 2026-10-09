import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainDefiningBGR

/-!
# Consumers of the analytic half of the actual zero domains (lane S-BCG-ROWS)

`frontier_M₁_unconditional_BGR`: F4c (`∂M₁ = ⋃ (ZF)_k ∪ ⋃ H_b`) on the enhanced chain from
`exists_boundaryZeroDefining_BGR` — the defining functions are produced, no analytic half and no
v2 bases (A4) are needed as data. `zeroDefining_domain_frontier_BGR`: `∂Z_k = face` and
`{F_k ≤ 0} = Z_k` for the produced defining functions.
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

/-- **F4c without the analytic half as data**: on the enhanced chain with `εr < 1/2` and the
premises of E4, `∂M₁ = ⋃ (ZF)_k ∪ ⋃ H_b` (the defining functions come from
`exists_boundaryZeroDefining_BGR`). -/
theorem frontier_M₁_unconditional_BGR (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    frontier C.toChain.M₁_BIFc =
      (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact C.frontier_M₁_of_defining_BGR Zd hrd hrd4 hrdc hprem hθ

/-- **The produced defining functions**: each actual zero domain is the sublevel `{F_k ≤ 0}` of a
smooth function regular on `{F_k = 0}`, whose frontier is the actual face. -/
theorem zeroDefining_domain_frontier_BGR (hεr : εr < 1 / 2) :
    ∃ F : S.ZeroIdx_BAUGC → W.Carrier → ℝ, (∀ k, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (F k)) ∧
      (∀ k, C.toChain.actualZeroDomain_BIFc k = {p | F k p ≤ 0}) ∧
      ∀ k, frontier (C.toChain.actualZeroDomain_BIFc k) = {p | F k p = 0} := by
  obtain ⟨Zd⟩ := C.exists_boundaryZeroDefining_BGR hεr
  exact ⟨Zd.defFn, Zd.defFn_smooth, Zd.domain_eq, fun k => (Zd.frontier_eq k).trans (Zd.face_eq k)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
