import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR

/-!
# Consumers of the v2b row consumers (S-BCG-ROWS2 G31)

The v2 forms (G25, G28, G29) follow from the v2b forms through `toV2b_OWF` (every v2 layer is a v2b
layer): the v2b theorems are strictly more general. Examples below.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

/-- v2 `face_saturated` (G25) from v2b. -/
example (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Zd : BoundaryZeroDefining_BIFc C.toChain)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ st : Fin 3, st ≠ 1 → ∀ p ∈ Bs.source st, ∀ q ∈ Bs.source st,
      C.toChain.stageMap st q = C.toChain.stageMap st p →
      p ∉ interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) →
      q ∉ interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) :=
  C.face_saturated_actual_V2b_BGR WF.toV2b_OWF Zd hrd hrd4 hrdc hprem hθ

/-- v2 F5 (G28) from v2b. -/
example (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y :=
  C.cuspFront_eq_slimFibre_direct_V2b_BGR WF.toV2b_OWF hrd hrd4 hrdc hprem hθ

/-- v2 `D₃` frontier (G29) from v2b. -/
example (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
      C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) :=
  C.relFrontier_slimBaseDomain_of_chain_V2b_BGR WF.toV2b_OWF hεr hrd hrd4 hrdc hprem hθ

end DifferentialGeometry.Geometry.Collapse
