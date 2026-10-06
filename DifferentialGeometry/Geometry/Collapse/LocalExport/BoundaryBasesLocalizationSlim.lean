import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesLocalizationCircle

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a (part 3): marker route, slim stage

`slim_final_loc_BBP` (whole-preimage localization of the final map `f₂`) and
`slim_orig_piece_BBP` (original points lie in the piece); the stage-projection transfer
`marker_stageProj_own_BBP`. See `LE/BoundaryBasesLocalization.lean`.
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

/-- The slim chart coordinate of the clean value: `κ_j(F_∂ q) = ζ_j(q) · η_j(q)`. -/
theorem slimKappa_boundaryOriginalMap_BBP (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.slimKappa_BBP j (S.boundaryOriginalMap q.val) =
      S.slimCutoffW_BAUGP2 j q.val * S.slimEta_BIF j.1 q := by
  have hblk := (S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).1
  rw [S.slimCoordW_val_BAUGP2] at hblk
  have hr := S.rho_pos j.1
  change (S.rho j.1)⁻¹ • (EuclideanSpace.proj (0 : Fin 2)) (S.slimVector_BAUGD j
    (S.boundaryOriginalMap q.val)) = _
  rw [hblk, map_smul, planeAxis_apply, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    S.slimEta_eq_coord_BAUGP2 j q]
  have hp : (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by simp
  rw [hp]
  field_simp

end BoundarySupplyCore

section Stage

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

/-- A stage projection keeps the marker of a chart of its own stage. -/
theorem marker_stageProj_own_BBP (m : S.MarkerIdx_BAUGC)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).stageProj (S.markerStage_BAUGC m) y) =
      S.markerCLM_BAUGC m y := by
  rw [markerCLM_stageProj_BAUGD, ite_eq_left (S.markerTag_mem_stageTagsV2_BAUGD m)]

end Stage

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **Slim: whole-preimage localization** of the final map: `f₂(p)` in the ratio piece of chart
`j` puts `p` in the chart domain `B(j, 10⁶Δρ_j)` with `|η_j| < 4.01 · 10⁵Δ`. -/
theorem slim_final_loc_BBP (j : S.SlimIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 2 p ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j)
      (S.rho j.1) (10 ^ 5 * Δ)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧
      (letI := inducedMetricSpace S.completion.metric;
        dist q j.1 < 1000000 * Δ * S.rho j.1) ∧
      |S.slimEta_BIF j.1 q| < 401 / 100 * (10 ^ 5 * Δ) := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
  have hm : S.slimMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) =
      S.slimMarker_BAUGD j (C.toChain.E p) :=
    marker_stageProj_own_BBP (Sum.inr (Sum.inl j)) (C.toChain.E p)
  have hk : S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) =
      S.slimKappa_BBP j (C.toChain.E p) := slimKappa_stageProj_BBP j _
  have hy : C.toChain.E p ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j)
      (S.rho j.1) (10 ^ 5 * Δ) := by
    obtain ⟨h1, h2⟩ := hp
    change 9 / 10 * S.rho j.1 < S.slimMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) at h1
    change S.rho j.1 * ‖S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p))‖ <
      39 / 10 * (10 ^ 5 * Δ) * S.slimMarker_BAUGD j
        ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) at h2
    rw [hm] at h1 h2
    rw [hk] at h2
    exact ⟨h1, h2⟩
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inr (Sum.inl j)) p :=
    C.final_marker_pos_BBP (Sum.inr (Sum.inl j)) hy.1
  have herr := C.final_err_le_BBP (Sum.inr (Sum.inl j)) hζ
  obtain ⟨q, rfl⟩ := S.interior_of_markerCutoffW_pos_BAUGD (Sum.inr (Sum.inl j)) hζ
  have hζ' : 0 < S.slimCutoffW_BAUGP2 j q.val := hζ
  have hR := S.rho_pos j.1
  have hzk : ‖S.slimKappa_BBP j (S.boundaryOriginalMap q.val)‖ =
      S.slimCutoffW_BAUGP2 j q.val * |S.slimEta_BIF j.1 q| := by
    rw [S.slimKappa_boundaryOriginalMap_BBP j q, Real.norm_eq_abs, abs_mul, abs_of_pos hζ']
  have hzv : S.slimMarker_BAUGD j (S.boundaryOriginalMap q.val) =
      S.rho j.1 * S.slimCutoffW_BAUGP2 j q.val :=
    (S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).2
  have hv1 : ‖(S.slimMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  obtain ⟨-, ha⟩ := loc_of_piece_BBP hR hℓ (S.norm_slimKappa_le_BBP j) hv1 herr hzv hzk hy
  refine ⟨q, rfl, ?_, ha⟩
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hpos : 0 < S.family.slim.cutoff_BCNT j.1 q := by
    rw [← S.slimCutoffW_val_BAUGP2]; exact hζ'
  exact S.mem_ball_of_mem_tsupport_slim_BAUGP2 hΔ j (subset_tsupport _ hpos.ne')

include C in
/-- **Slim: original points lie in the piece**. -/
theorem slim_orig_piece_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| ≤ 7 / 2 * (10 ^ 5 * Δ)) :
    C.toChain.stageMap 2 q.val ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j)
      (S.rho j.1) (10 ^ 5 * Δ) := by
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
  have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
  have hone : S.slimCutoffW_BAUGP2 j q.val = 1 :=
    S.markerCutoffW_eq_one_of_core7_BAUGD hΔ (Sum.inr (Sum.inl j))
      ⟨hq, by nlinarith⟩
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inr (Sum.inl j)) q.val := by
    change 0 < S.slimCutoffW_BAUGP2 j q.val
    rw [hone]; exact one_pos
  have herr := C.final_err_le_BBP (Sum.inr (Sum.inl j)) hζ
  have hR := S.rho_pos j.1
  have hzk : ‖S.slimKappa_BBP j (S.boundaryOriginalMap q.val)‖ =
      1 * |S.slimEta_BIF j.1 q| := by
    rw [S.slimKappa_boundaryOriginalMap_BBP j q, hone, one_mul, Real.norm_eq_abs, one_mul]
  have hzv : S.slimMarker_BAUGD j (S.boundaryOriginalMap q.val) = S.rho j.1 * 1 := by
    rw [(S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).2, hone]
  have hv1 : ‖(S.slimMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  have hy := piece_of_orig_BBP hR hℓ (S.norm_slimKappa_le_BBP j) hv1 herr hzv hzk hη
  obtain ⟨h1, h2⟩ := hy
  have hm : S.slimMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E q.val)) =
      S.slimMarker_BAUGD j (C.toChain.E q.val) :=
    marker_stageProj_own_BBP (Sum.inr (Sum.inl j)) (C.toChain.E q.val)
  have hk : S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E q.val)) =
      S.slimKappa_BBP j (C.toChain.E q.val) := slimKappa_stageProj_BBP j _
  change 9 / 10 * S.rho j.1 < S.slimMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E q.val)) ∧
    S.rho j.1 * ‖S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E q.val))‖ <
      39 / 10 * (10 ^ 5 * Δ) * S.slimMarker_BAUGD j
        ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E q.val))
  rw [hm, hk]
  exact ⟨h1, h2⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
