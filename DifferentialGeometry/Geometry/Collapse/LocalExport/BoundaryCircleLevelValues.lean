import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesFinalSubmersion
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEScaleB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEExits

/-!
# G17 circle level (a): the value clause `‖g_j − η_j‖ < 1/800` on the plateau (S-BAUG-D2)

Closed twin `Gaf02Chain.gaf07_circle_coordinate_G47` (GAF07's value clause). On the circle chart
`j`'s original threshold-`6` plateau, the adjusted coordinate `g_j = κ_j ∘ f₀` of the FINAL stage
map is `1/800`-close to the original chart coordinate `η_j`: `κ_j (F_∂ q) = η_j q`
(`circleKappa_boundaryOriginalMap_eventuallyEq_BBP`), `f₀ = π₀ ∘ E = E` (`π₀ = id` on the v2 slot,
`stageProj_zero_V2_BAUGD`), `‖E q − F_∂ q‖ < c₂ ρ(q)` (A3b), `‖κ_j‖ ≤ ρ_j⁻¹`, and `ρ(q) ≤ 5/4 ρ_j`
on the chart ball (`ρ` is `Λ`-Lipschitz, `200 Λ ≤ 1/4`). Register premise: `c₂ < 1/1000`
(GAF01's `c₃`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **GAF07's value clause on the boundary chain** (closed `gaf07_circle_coordinate_G47`): on the
circle plateau `‖κ_j (f₀ q) − η_j q‖ < 1/800`. -/
theorem circle_final_value_close_BAUGD (hc : c 2 < 1 / 1000) (j : S.CircleIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    ‖S.circleKappa_BBP j (C.toChain.stageMap 0 q.val) - S.circleEta_BIF j.1 q‖ < 1 / 800 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, h1Δ, hΔΛ', -⟩ := C.std
  have hr := S.rho_pos j.1
  -- `κ_j (F q) = η_j q`
  have hF : S.circleKappa_BBP j (S.boundaryOriginalMap q.val) = S.circleEta_BIF j.1 q :=
    (S.circleKappa_boundaryOriginalMap_eventuallyEq_BBP j hq hη).self_of_nhds
  -- `f₀ q = E q`
  have hf : C.toChain.stageMap 0 q.val = C.toChain.stage (2 : Fin 3).succ q.val :=
    stageProj_zero_V2_BAUGD S _
  have hE := C.stage_error_lt_BAUGD 2 q.val
  -- `ρ q ≤ 5/4 ρ_j`
  have hρq : S.rho q.val ≤ 5 / 4 * S.rho j.1 := by
    have h := S.rho_sub_le_circle_BAUGD hΛ hΔ hV hβ1 hb j q hq
    have hd : (letI := inducedMetricSpace S.completion.metric; dist q j.1) <
        200 * S.rho j.1 := hq
    have hΛ200 : Λ * 200 ≤ 1 / 4 := by nlinarith
    have : Λ * (letI := inducedMetricSpace S.completion.metric; dist q j.1) ≤
        1 / 4 * S.rho j.1 := by
      calc _ ≤ Λ * (200 * S.rho j.1) := mul_le_mul_of_nonneg_left hd.le hΛ
        _ = (Λ * 200) * S.rho j.1 := by ring
        _ ≤ 1 / 4 * S.rho j.1 := mul_le_mul_of_nonneg_right hΛ200 hr.le
    have h2 := (abs_le.mp h).2
    linarith
  rw [hf, ← hF, ← map_sub]
  have hk := (S.circleKappa_BBP j).le_opNorm (C.toChain.stage (2 : Fin 3).succ q.val -
    S.boundaryOriginalMap q.val)
  have hkn := S.norm_circleKappa_le_BBP j
  have hc2 : 0 < c 2 := by
    by_contra hneg
    push Not at hneg
    have h0 : c 2 * S.rho q.val ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (S.rho_pos q.val).le
    exact absurd (hE.trans_le h0) (not_lt.mpr (norm_nonneg _))
  have hstep : ‖S.circleKappa_BBP j (C.toChain.stage (2 : Fin 3).succ q.val -
      S.boundaryOriginalMap q.val)‖ < (S.rho j.1)⁻¹ * (c 2 * S.rho q.val) := by
    calc _ ≤ ‖S.circleKappa_BBP j‖ * ‖C.toChain.stage (2 : Fin 3).succ q.val -
          S.boundaryOriginalMap q.val‖ := hk
      _ ≤ (S.rho j.1)⁻¹ * ‖C.toChain.stage (2 : Fin 3).succ q.val -
          S.boundaryOriginalMap q.val‖ := mul_le_mul_of_nonneg_right hkn (norm_nonneg _)
      _ < (S.rho j.1)⁻¹ * (c 2 * S.rho q.val) :=
          mul_lt_mul_of_pos_left hE (inv_pos.mpr hr)
  refine hstep.trans_le ?_
  have h54 : (S.rho j.1)⁻¹ * (c 2 * S.rho q.val) ≤ (S.rho j.1)⁻¹ * (c 2 * (5 / 4 * S.rho j.1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hρq hc2.le) (inv_pos.mpr hr).le
  have h55 : (S.rho j.1)⁻¹ * (c 2 * (5 / 4 * S.rho j.1)) = 5 / 4 * c 2 := by
    field_simp
  rw [h55] at h54
  linarith

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
