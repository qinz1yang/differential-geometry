import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimSurjective
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarExitsBC7C
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBasesV2

/-!
# BCG07 F1, conjunct 1: the rim of the edge source lies in `X₁` (lane O-F1, G1)

Boundary twin of EDP06's first clause (blueprint `master207B.tex`, B:7102–7108; closed lanes
S-EDP-FDC `rim_localization_EFC`, C14-EDP-E `eventually_edp06_final_rim_circle_EDPE`, C14-FDCb
`circle_ball_mem_X₁_FDC`). On the enhanced boundary chain `C` and ANY v2 BASES exit `Bs` of it:

* (ELoc) `Bs.edge_localization`: a point `p ∈ X₂` has a revised edge centre `j` with
  `d(q, j) < 100Δρ_j`, `|η_j| < 4.01Δ`, `t < 4.01Δ` (`q = p` in `W°`);
* EDP04/(EH) `BoundaryGaf02ChainE.rim_region_BAUGD`: with `T(p) = 4Δ`, `3.9Δ < t < 4.1Δ`;
* BCG7-COLLAR exit 3 `LocalPacketsOnBFRZ.edgeB_collar_coveredByCircle_BC7C` on the SAME stored
  family `S.family` (the LFR38 band `Δ/10 ≤ t ≤ 10Δ`, `|η_j| ≤ 10Δ`): a circle centre `a` with
  `d(q, a) < 2ρ_a`, `‖η_a(q)‖ < 2(1 + γ)`;
* GAF07 `Bs.circle_original_subset` (`2ρ_a ≤ 200ρ_a`, `2(1 + γ) ≤ 7/2`): `p ∈ X₁`.

**`BoundaryGaf02ChainE.rim_mem_source_zero_OF1`**: `p ∈ X₂`, `T(p) = 4Δ` ⟹ `p ∈ X₁`.
Numerical premises (parameters only): `3βc ≤ β 2 < 1`, `0 ≤ γ ≤ 3/4` (EDP06 side of register V4,
`BoundaryRegisterV4.edp06_side_BC7C`, and LPA06's `γ`), `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`
(`rim_region_BAUGD`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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

/-- **EDP06's first clause on the boundary: the rim of `X₂` lies in `X₁`.** A point `p` of the
edge source `X₂` with `T(p) = 4Δ` lies in the circle source `X₁` of the SAME v2 BASES exit. -/
theorem rim_mem_source_zero_OF1 (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ)
    (hγ34 : γ ≤ 3 / 4) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (Bs : BoundaryGaf02BasesV2 C.toChain) {p : W.Carrier} (hp : p ∈ Bs.source 1)
    (hT : C.toChain.heightRatio p = 4 * Δ) : p ∈ Bs.source 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨-, hΔ0, -⟩ := C.std
  obtain ⟨q, rfl, j, hj, hd, hη, ht⟩ := Bs.edge_localization p hp
  have hjB : j ∈ S.family.edgeB.centres := hj
  obtain ⟨-, -, h39, h41, -, -⟩ :=
    C.rim_region_BAUGD hc hC ⟨j, (Set.Finite.mem_toFinset _).mpr hjB⟩ hd hη ht hT
  have hηj : S.edgeEta_BIF j q = S.family.edgeB.coord_BCG1 j hjB q := by
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left hjB]
  have hηc : |S.family.edgeB.coord_BCG1 j hjB q| ≤ 10 * Δ := by
    rw [← hηj]
    linarith
  have hraw : S.edgeHeightRaw q = S.family.edgeB.smoothing q / S.rho q.val := rfl
  obtain ⟨-, a, ha, -, hqa, hca, -⟩ := S.family.edgeB_collar_coveredByCircle_BC7C h3βc hβ2 hγ hjB
    hd hηc (by rw [← hraw]; linarith) (by rw [← hraw]; linarith)
  refine Bs.circle_original_subset q a ha (by linarith [S.rho_pos a.val]) ?_
  have hηa : S.circleEta_BIF a q = (let c := S.family.circle.chart a ha
      letI := (inducedMetricSpace S.completion.metric).rescale (S.rho a)⁻¹
        (inv_pos.mpr (S.rho_pos a))
      c.coord) q := by
    unfold BoundarySupplyCore.circleEta_BIF
    rw [dite_eq_left ha]
  rw [hηa]
  have h2 : 2 * (1 + γ) ≤ 7 / 2 := by linarith
  exact (lt_of_lt_of_le hca h2).le

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
