import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimSurjective
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentAssembly

/-!
# G12 / G16 (part b): the open edge parent on the enhanced boundary chain (S-BAUG-D)

`BoundaryGaf02ChainE.exists_edgeParent_of_core_BAUGD`: given the core of the BASES exit (G11's
product, here as an explicit DATA argument `Bc`, its edge localization clause being the only
field read), an open parent domain `U` with `X₂ = U ∩ {T ≤ 4Δ}`, `U ⊆ f₂⁻¹ B₂` and rank one on
`U` (G11's stage-1 submersion), the open edge parent structure `BoundaryEdgeParent_BIFc` exists:
smoothness is free (A3a), and the rank-two field at `T = 4Δ` is the rim surjectivity of
`LE/BoundaryEdgeRimSurjective.lean` (closed twin `Gaf02Chain.edge_vertical_rank_EDPE`) applied
at the localization given by `Bc.edge_localization`.

Numerical premises (all parameters only; `hC` is the N76-9 candidate): `c₃ = c 2 < 10⁻⁵`
(SE), `C_ρΛΔ < 10⁻⁶` with `C_ρ = 100(b_der + 1)(1 + b_cut + c_w(0)/Σ₀)` (closed `hϑ`),
`0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵` (as in the closed `edge_vertical_rank_EDPE`).
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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The open edge parent from the core of the BASES exit** (D69-7; G12 with G11's core as data):
`U` open with `X₂ = U ∩ {T ≤ 4Δ}`, `U ⊆ f₂⁻¹ B₂`, `rank df₂ = 1` on `U`; the rank-two field is
discharged by the rim surjectivity at the localization of `X₂` (`Bc.edge_localization`). -/
theorem exists_edgeParent_of_core_BAUGD (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (Bc : BoundaryGaf02BasesCore_BIFc C.toChain) (U : Set W.Carrier) (hU : IsOpen U)
    (hcut : Bc.source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' Bc.base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1) :
    Nonempty (BoundaryEdgeParent_BIFc C.toChain Bc.source Bc.base) := by
  refine ⟨C.edgeParentOfRim_BAUGD Bc.source Bc.base U hU hcut hsub hrk fun p hp hT => ?_⟩
  have hpX : p ∈ Bc.source 1 := by
    rw [hcut]
    exact ⟨hp, le_of_eq hT⟩
  obtain ⟨q, rfl, j, hj, hd, hη, ht⟩ := Bc.edge_localization p hpX
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  exact C.rim_surjective_BAUGD hc hC hε0 hε hγc hγc1 hβc1
    ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩ hd hη ht hT

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
