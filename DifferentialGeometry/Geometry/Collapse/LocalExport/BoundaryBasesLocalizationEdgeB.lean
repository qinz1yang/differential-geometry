import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesLocalizationEdge

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 5): marker route, edge stage (assembly)

`edge_final_loc_BBP` (whole-preimage localization of the final map `f₁` on `{T ≤ 4Δ}`),
`edge_orig_piece_BBP` (original points lie in the piece) and `edge_orig_height_BBP`
(`t ≤ 3.5Δ ⟹ T < 4Δ`).
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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **Edge: whole-preimage localization** of the final map on `{T ≤ 4Δ}`: `f₁(p)` in the ratio
piece of chart `j` and `T(p) ≤ 4Δ` put `p` in the chart domain `B(j, 100Δρ_j)` with
`|η_j| < 4.01Δ` and `t < 4.01Δ`. -/
theorem edge_final_loc_BBP (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 1 p ∈ ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j)
      (S.rho j.1) Δ) (hT : C.toChain.heightRatio p ≤ 4 * Δ) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1) ∧
      |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ ∧ S.edgeHeightRaw q < 401 / 100 * Δ := by
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
  exact ⟨q, rfl, hd, ha, C.edge_height_loc_BBP j hd hη8 hζ97 hT⟩

include C in
/-- **Edge: original points lie in the piece** (`t ≤ 7Δ` keeps the chart on its plateau). -/
theorem edge_orig_piece_BBP (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 7 / 2 * Δ) (hh : S.edgeHeightRaw q ≤ 7 * Δ) :
    C.toChain.stageMap 1 q.val ∈ ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j)
      (S.rho j.1) Δ := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  have hone : S.edgeCutoffW_BAUGP2 j q.val = 1 :=
    S.markerCutoffW_eq_one_of_core7_BAUGD hΔ (Sum.inr (Sum.inr j))
      ⟨hq, by nlinarith, hh⟩
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inr (Sum.inr j)) q.val := by
    change 0 < S.edgeCutoffW_BAUGP2 j q.val
    rw [hone]; exact one_pos
  have herr := C.final_err_le_BBP (Sum.inr (Sum.inr j)) hζ
  have hR := S.rho_pos j.1
  have hzk : ‖S.edgeKappa_BBP j (S.boundaryOriginalMap q.val)‖ =
      1 * |S.edgeEta_BIF j.1 q| := by
    rw [S.edgeKappa_boundaryOriginalMap_BBP j q, hone, one_mul, Real.norm_eq_abs, one_mul]
  have hzv : S.edgeMarker_BAUGD j (S.boundaryOriginalMap q.val) = S.rho j.1 * 1 := by
    rw [(S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).2, hone]
  have hv1 : ‖(S.edgeMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  have hy := piece_of_orig_BBP hR hΔ1 (S.norm_edgeKappa_le_BBP j) hv1 herr hzv hzk hη
  obtain ⟨h1, h2⟩ := hy
  have hm : S.edgeMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E q.val)) =
      S.edgeMarker_BAUGD j (C.toChain.E q.val) :=
    marker_stageProj_own_BBP (Sum.inr (Sum.inr j)) (C.toChain.E q.val)
  have hk : S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E q.val)) =
      S.edgeKappa_BBP j (C.toChain.E q.val) := edgeKappa_stageProj_BBP j _
  change 9 / 10 * S.rho j.1 < S.edgeMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E q.val)) ∧
    S.rho j.1 * ‖S.edgeKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E q.val))‖ <
      39 / 10 * Δ * S.edgeMarker_BAUGD j
        ((actualSlotsV2_BAUGD S).stageProj 1 (C.toChain.E q.val))
  rw [hm, hk]
  exact ⟨h1, h2⟩

include C in
/-- **An original edge point has `T < 4Δ`**: `t ≤ 3.5Δ` gives `A ≤ F + c₃ρ`, `s > (1 − c₀)ρ`. -/
theorem edge_orig_height_BBP {q : W.pieceInterior ⊤}
    (hh : S.edgeHeightRaw q ≤ 7 / 2 * Δ) : C.toChain.heightRatio q.val < 4 * Δ := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  have hρq := S.rho_pos q.val
  have hc0 : c 0 ≤ 1 / 512 := C.toChain.numbers.2.2.1
  have hc2 := C.c_two_le_BBP
  obtain ⟨-, hsd, hspos⟩ := C.scale_pos_BAUGD q.val
  have hsρ : (1 - c 0) * S.rho q.val < C.toChain.scale q.val := by
    have := (abs_lt.mp hsd).1
    linarith
  have hAF := C.stage_error_lt_BAUGD 2 q.val
  have hAerr : |C.toChain.height q.val - S.heightCoord_BIF (S.boundaryOriginalMap q.val)| <
      c 2 * S.rho q.val := by
    have h1 := S.abs_heightFun_le_BAUGD (C.toChain.E q.val - S.boundaryOriginalMap q.val)
    rw [map_sub] at h1
    exact h1.trans_lt hAF
  have hA := (abs_lt.mp hAerr).2
  have hAP := S.heightCoord_boundaryOriginalMap_le_BAUGD q
  have hF : S.edgeSmoothing_BAUGD q ≤ 7 / 2 * Δ * S.rho q.val := by
    have h := hh
    rw [S.edgeHeightRaw_eq_BAUGD, div_le_iff₀ hρq] at h
    exact h
  have h1 : c 2 * S.rho q.val ≤ 1 / 512 * S.rho q.val :=
    mul_le_mul_of_nonneg_right hc2 hρq.le
  have h2 : Δ * (c 0 * S.rho q.val) ≤ Δ * (1 / 512 * S.rho q.val) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc0 hρq.le) hΔ.le
  have h3 : 4 * Δ * ((1 - c 0) * S.rho q.val) < 4 * Δ * C.toChain.scale q.val :=
    mul_lt_mul_of_pos_left hsρ (by positivity)
  have h4 : S.rho q.val ≤ Δ * S.rho q.val := by nlinarith
  have hlt : C.toChain.height q.val < 4 * Δ * C.toChain.scale q.val := by nlinarith
  change C.toChain.height q.val / C.toChain.scale q.val < 4 * Δ
  rwa [div_lt_iff₀ hspos]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
