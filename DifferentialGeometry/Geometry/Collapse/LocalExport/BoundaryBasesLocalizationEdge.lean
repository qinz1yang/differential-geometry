import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesLocalizationSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimSurjective
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeLimit
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRatio

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 4): marker route, edge stage

`edge_height_loc_BBP` (`T ≤ 4Δ` and `ζ_j > .897` give `t < 4.01Δ`: the height part of EDP02's
(ELoc), by the three cases `t ≤ .35Δ`, `.35Δ < t ≤ 8Δ` (`z_{E'} = 1`), `t > 8Δ` (`z_{E'} ≥ .6`)),
`edge_final_loc_BBP` (whole-preimage localization of the final map `f₁`), `edge_orig_piece_BBP`
(original points lie in the piece) and `edge_orig_height_BBP` (`t ≤ 3.5Δ ⟹ T < 4Δ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
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

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The edge chart coordinate of the clean value: `κ_j(F_∂ q) = ζ_j(q) · η_j(q)`. -/
theorem edgeKappa_boundaryOriginalMap_BBP (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeKappa_BBP j (S.boundaryOriginalMap q.val) =
      S.edgeCutoffW_BAUGP2 j q.val * S.edgeEta_BIF j.1 q := by
  have hblk := (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).1
  rw [S.edgeCoordW_val_BAUGP2] at hblk
  have hr := S.rho_pos j.1
  change (S.rho j.1)⁻¹ • (EuclideanSpace.proj (0 : Fin 2)) (S.edgeVector_BAUGD j
    (S.boundaryOriginalMap q.val)) = _
  rw [hblk, map_smul, planeAxis_apply, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    S.edgeEta_eq_coord_BAUGP2 j q]
  have hp : (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by simp
  rw [hp]
  field_simp

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The height part of (ELoc)**: `q` in the chart ball with `|η_j| < 8Δ`, `ζ_j(q) > .897` and
`T(q) ≤ 4Δ` has `t(q) < 4.01Δ`. -/
theorem edge_height_loc_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 8 * Δ) (hζ : 897 / 1000 < S.edgeCutoffW_BAUGP2 j q.val)
    (hT : C.toChain.heightRatio q.val ≤ 4 * Δ) : S.edgeHeightRaw q < 401 / 100 * Δ := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  have hρq := S.rho_pos q.val
  have hc0 : c 0 ≤ 1 / 512 := C.toChain.numbers.2.2.1
  have hc2 := C.c_two_le_BBP
  by_cases ht35 : S.edgeHeightRaw q ≤ 7 / 20 * Δ
  · linarith
  push Not at ht35
  obtain ⟨-, hsd, hspos⟩ := C.scale_pos_BAUGD q.val
  have hsρ : C.toChain.scale q.val < (1 + c 0) * S.rho q.val := by
    have := (abs_lt.mp hsd).2
    linarith
  have hAs : C.toChain.height q.val ≤ 4 * Δ * C.toChain.scale q.val := by
    have h : C.toChain.height q.val / C.toChain.scale q.val ≤ 4 * Δ := hT
    rwa [div_le_iff₀ hspos] at h
  have hAF := C.stage_error_lt_BAUGD 2 q.val
  have hAerr : |C.toChain.height q.val - S.heightCoord_BIF (S.boundaryOriginalMap q.val)| <
      c 2 * S.rho q.val := by
    have h1 := S.abs_heightFun_le_BAUGD (C.toChain.E q.val - S.boundaryOriginalMap q.val)
    rw [map_sub] at h1
    exact h1.trans_lt hAF
  have hA := (abs_lt.mp hAerr).1
  rw [S.heightCoord_boundaryOriginalMap_BAUGD] at hA
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hF : S.edgeHeightRaw q = S.family.edgeB.smoothing q / S.rho q.val := rfl
  by_cases ht8 : S.edgeHeightRaw q ≤ 8 * Δ
  · have hm := S.edgeBMarker_eq_one_BAUGD hΔ j q hd hη (by linarith) ht8
    rw [hm, one_mul] at hA
    have hlow := fdc02_height_low_numbers_FDC (F := S.family.edgeB.smoothing q) hΔ1 hρq hc0 hc2 (by linarith) hAs hsρ
    rw [hF, div_lt_iff₀ hρq]
    linarith
  · exfalso
    push Not at ht8
    have h3 : 3 / 10 ≤ S.family.edgeBHeight_BAUGA q / Δ := by
      rw [le_div_iff₀ hΔ]
      change 3 / 10 * Δ ≤ S.edgeHeightRaw q
      linarith
    have hH := cgpEdgeH_eq_of_le h3
    have hdom : q.val ∈ S.edgeDomW_BAUGP2 j := ⟨q, mem_ball.mpr hd, rfl⟩
    have hη' : ‖S.edgeCoordW_BAUGP2 j q.val‖ < 8 * Δ := by
      rw [S.norm_edgeCoordW_val_BAUGP2]; exact hη
    have hid := S.edgeCutoffW_identity_BAUGP2 hΔ j q.val hdom hη'
    rw [S.edgeHeightW_val_BAUGP2] at hid
    have hζ' : S.edgeCutoffW_BAUGP2 j q.val = S.family.edgeB.cutoff_BAUGA j.1 q :=
      S.edgeCutoffW_val_BAUGP2 j q
    have hsum : S.family.edgeB.cutoff_BAUGA j.1 q ≤ S.family.edgeBSum_BAUGA q := by
      unfold LocalPacketsOnB.edgeBSum_BAUGA
      exact Finset.single_le_sum
        (f := fun i : S.family.edgeB.finite_centres.toFinset => S.family.edgeB.cutoff_BAUGA i.1 q)
        (fun i _ => (S.family.edgeB.cutoff_mem_Icc_BAUGA hΔ i.1 q).1) (Finset.mem_univ j)
    have hramp := edgeSumRamp_ge_FDC (by linarith : 3 / 4 ≤ S.family.edgeBSum_BAUGA q)
    have hz6 : 6 / 10 ≤ S.family.edgeBMarker_BAUGA q := by
      unfold LocalPacketsOnB.edgeBMarker_BAUGA
      rw [hH]
      have hH' : 897 / 1000 ≤ 1 - cfsRamp lc87EdgeTransition 8 9
          (S.family.edgeBHeight_BAUGA q / Δ) := by
        have : S.edgeHeightRaw q / Δ = S.family.edgeBHeight_BAUGA q / Δ := rfl
        rw [← this] at *
        linarith
      have := mul_le_mul hH' hramp (by norm_num) (by linarith)
      linarith
    have hP8 : 8 * Δ * S.rho q.val < S.family.edgeB.smoothing q := by
      rw [hF] at ht8
      rwa [lt_div_iff₀ hρq] at ht8
    exact fdc02_height_high_numbers_weak_FDC (F := S.family.edgeB.smoothing q) hΔ1 hρq hc0 hc2 hz6 hP8 (by linarith) hAs hsρ

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
