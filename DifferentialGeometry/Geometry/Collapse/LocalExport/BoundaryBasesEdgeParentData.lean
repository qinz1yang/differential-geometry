import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCore

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3b: the open edge parent set `U` (partial) and the slim
embedding

* `edge_final_loc5_BBP`: the threshold-`5Δ` variant of the edge whole-preimage localization
  (`T ≤ 5Δ`, `f₁(p)` in the piece of chart `j` give `t < 6Δ`: `z_{E'} ≥ .67` on the high branch);
* `edgeParentSet_BBP` (`U = f₁⁻¹(O₁) ∩ {T < 5Δ}`): `isOpen_edgeParentSet_BBP`,
  `baseSource_one_eq_edgeParent_BBP` (`X₂ = U ∩ {T ≤ 4Δ}`), `edgeParent_rank_BBP` (`rank df₁ = 1` on
  `U`): the arguments `hU hcut hrk` of `exists_edgeParent_of_core_BAUGD`. The remaining argument
  `hsub : U ⊆ f₁⁻¹(B₁)` needs every fibre point over `U` to meet `{T ≤ 4Δ}` (group G4);
* `later_isEmbedding_two_BBP`: the embedding clause at the last stage (`Θ₂ = id`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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

/-- Low height numbers at threshold `5Δ`: `F − c₂r < A ≤ 5Δs`, `s < (1 + c₀)r` give `F < 6Δr`. -/
theorem edge_height_low5_numbers_BBP {Δ r F A s c₀ c₂ : ℝ} (hΔ : 1 ≤ Δ) (hr : 0 < r)
    (hc₀ : c₀ ≤ 1 / 512) (hc₂ : c₂ ≤ 1 / 512) (hA : F - c₂ * r < A) (hAs : A ≤ 5 * Δ * s)
    (hs : s < (1 + c₀) * r) : F < 6 * Δ * r := by
  have h1 : 5 * Δ * s ≤ 5 * Δ * ((1 + c₀) * r) :=
    mul_le_mul_of_nonneg_left hs.le (by positivity)
  have h2 : c₀ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₀ hr.le
  have h3 : c₂ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₂ hr.le
  have h4 : r ≤ Δ * r := by nlinarith
  have h5 : Δ * (c₀ * r) ≤ Δ * (1 / 512 * r) := mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

/-- High height numbers at threshold `5Δ`: `z ≥ .67`, `F > 8Δr`, `zF − c₂r < A ≤ 5Δs`,
`s < (1 + c₀)r` are contradictory. -/
theorem edge_height_high5_numbers_BBP {Δ r F A s c₀ c₂ z : ℝ} (hΔ : 1 ≤ Δ) (hr : 0 < r)
    (hc₀ : c₀ ≤ 1 / 512) (hc₂ : c₂ ≤ 1 / 512) (hz : 67 / 100 ≤ z)
    (hF : 8 * Δ * r < F) (hA : z * F - c₂ * r < A) (hAs : A ≤ 5 * Δ * s)
    (hs : s < (1 + c₀) * r) : False := by
  have h1 : 5 * Δ * s ≤ 5 * Δ * ((1 + c₀) * r) :=
    mul_le_mul_of_nonneg_left hs.le (by positivity)
  have h2 : c₀ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₀ hr.le
  have h3 : c₂ * r ≤ 1 / 512 * r := mul_le_mul_of_nonneg_right hc₂ hr.le
  have h4 : r ≤ Δ * r := by nlinarith
  have h5 : Δ * (c₀ * r) ≤ Δ * (1 / 512 * r) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : 67 / 100 * (8 * Δ * r) ≤ z * F := mul_le_mul hz hF.le (by positivity) (by linarith)
  nlinarith

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The height part of (ELoc) at threshold `5Δ`**: `ζ_j > .897`, `|η_j| < 8Δ` and `T ≤ 5Δ` give
`t < 6Δ`. -/
theorem edge_height_loc5_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 8 * Δ) (hζ : 897 / 1000 < S.edgeCutoffW_BAUGP2 j q.val)
    (hT : C.toChain.heightRatio q.val ≤ 5 * Δ) : S.edgeHeightRaw q < 6 * Δ := by
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
  have hAs : C.toChain.height q.val ≤ 5 * Δ * C.toChain.scale q.val := by
    have h : C.toChain.height q.val / C.toChain.scale q.val ≤ 5 * Δ := hT
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
    have hlow := edge_height_low5_numbers_BBP (F := S.family.edgeB.smoothing q) hΔ1 hρq hc0 hc2
      (by linarith) hAs hsρ
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
    have hz67 : 67 / 100 ≤ S.family.edgeBMarker_BAUGA q := by
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
    exact edge_height_high5_numbers_BBP (F := S.family.edgeB.smoothing q) hΔ1 hρq hc0 hc2 hz67
      hP8 (by linarith) hAs hsρ

include C in
/-- **Edge: localization of the whole preimage at threshold `5Δ`**: `f₁(p)` in the piece of chart
`j` and `T(p) ≤ 5Δ` put `p` in the chart domain with `|η_j| < 4.01Δ` and `t < 6Δ`. -/
theorem edge_final_loc5_BBP (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 1 p ∈ ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j)
      (S.rho j.1) Δ) (hT : C.toChain.heightRatio p ≤ 5 * Δ) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1) ∧
      |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ ∧ S.edgeHeightRaw q < 6 * Δ := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  have hm : S.edgeMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E p)) =
      S.edgeMarker_BAUGD j (C.toChain.E p) :=
    marker_stageProj_own_BBP (Sum.inr (Sum.inr j)) (C.toChain.E p)
  have hk : S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E p)) =
      S.edgeKappa_BBP j (C.toChain.E p) := edgeKappa_stageProj_BBP j _
  have hy : C.toChain.E p ∈ ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j)
      (S.rho j.1) Δ := by
    obtain ⟨h1, h2⟩ := hp
    change 9 / 10 * S.rho j.1 < S.edgeMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E p)) at h1
    change S.rho j.1 * ‖S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E p))‖ <
      39 / 10 * Δ * S.edgeMarker_BAUGD j
        ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E p)) at h2
    rw [hm] at h1 h2
    rw [hk] at h2
    exact ⟨h1, h2⟩
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inr (Sum.inr j)) p :=
    C.final_marker_pos_BBP (Sum.inr (Sum.inr j)) hy.1
  have herr := C.final_err_le_BBP (Sum.inr (Sum.inr j)) hζ
  obtain ⟨q, rfl⟩ := S.interior_of_markerCutoffW_pos_BAUGD (Sum.inr (Sum.inr j)) hζ
  have hζ' : 0 < S.edgeCutoffW_BAUGP2 j q.val := hζ
  have hR := S.rho_pos j.1
  have hzk : ‖S.edgeKappa_BBP j (S.boundaryOriginalMap q.val)‖ =
      S.edgeCutoffW_BAUGP2 j q.val * |S.edgeEta_BIF j.1 q| := by
    rw [S.edgeKappa_boundaryOriginalMap_BBP j q, Real.norm_eq_abs, abs_mul, abs_of_pos hζ']
  have hzv : S.edgeMarker_BAUGD j (S.boundaryOriginalMap q.val) =
      S.rho j.1 * S.edgeCutoffW_BAUGP2 j q.val :=
    (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).2
  have hv1 : ‖(S.edgeMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  obtain ⟨hζ97, ha⟩ := loc_of_piece_BBP hR hΔ1 (S.norm_edgeKappa_le_BBP j) hv1 herr hzv hzk hy
  have hη8 : |S.edgeEta_BIF j.1 q| < 8 * Δ := by linarith
  have hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1 := by
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    have hpos : 0 < S.family.edgeB.cutoff_BAUGA j.1 q := by
      rw [← S.edgeCutoffW_val_BAUGP2]; exact hζ'
    obtain ⟨-, hball, -, -⟩ := S.family.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hpos.ne'
    have hh := (inv_mul_lt_iff₀ hR).mp hball
    linarith
  exact ⟨q, rfl, hd, ha, C.edge_height_loc5_BBP j hd hη8 hζ97 hT⟩

/-- **The open edge parent set** `U = f₁⁻¹(O₁) ∩ {T < 5Δ}`. -/
def edgeParentSet_BBP : Set W.Carrier :=
  {p | C.toChain.stageMap 1 p ∈ S.ratioSet_BBP 1 ∧ C.toChain.heightRatio p < 5 * Δ}

include C in
/-- `U` is open. -/
theorem isOpen_edgeParentSet_BBP : IsOpen C.edgeParentSet_BBP :=
  ((S.isOpen_ratioSet_BBP 1).preimage (C.continuous_stageMap_V2_BAUGD 1)).inter
    (isOpen_lt C.continuous_heightRatio_BAUGD continuous_const)

include C in
/-- **`X₂ = U ∩ {T ≤ 4Δ}`** (the `hcut` argument of `exists_edgeParent_of_core_BAUGD`). -/
theorem baseSource_one_eq_edgeParent_BBP : C.baseSource_BBP 1 =
    C.edgeParentSet_BBP ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} := by
  obtain ⟨-, hΔ, -⟩ := C.std
  ext p
  constructor
  · rintro ⟨hp, hT⟩
    exact ⟨⟨hp, by linarith [hT rfl]⟩, hT rfl⟩
  · rintro ⟨⟨hp, -⟩, hT⟩
    exact ⟨hp, fun _ => hT⟩

include C in
/-- **`rank df₁ = 1` on `U`** (the `hrk` argument; G1c/G2 on the plateau, localization at
threshold `5Δ`). -/
theorem edgeParent_rank_BBP (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) {p : W.Carrier}
    (hp : p ∈ C.edgeParentSet_BBP) : C.toChain.stageRank_BIFc 1 p = 1 := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, rfl, hd, hη, ht⟩ := C.edge_final_loc5_BBP j hj hp.2.le
  exact C.stage_rank_eq_edge_BBP hσ hb j hd (by linarith) ht

include C in
/-- **The embedding clause at the last stage**: `Θ₂ = id`. -/
theorem later_isEmbedding_two_BBP :
    IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc 2 '' C.baseSource_BBP 2 =>
      C.toChain.laterV2_BAUGD 2 x) :=
  IsEmbedding.subtypeVal

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
