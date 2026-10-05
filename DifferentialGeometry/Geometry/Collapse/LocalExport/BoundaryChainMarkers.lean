import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffTwo
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainSmoothV2
import DifferentialGeometry.Geometry.Metric.ActualStageMarkersUnrolled
import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers

/-!
# BCG03: the marker data of the boundary chain on `W` and CFS29/CFS30's stage inputs (BAUG-Dc)

Part (b) of target A2-mk (`TargetsBoundary-A-v3.lean.txt`; review 69 D69-5): the zero-marker input
(ZM) / (AM0) of the stage outputs needs, on the WHOLE original carrier `X = W`, the marker data of
`F_∂` (closed `gafMarker_data_GAF7`) and the stage inputs of CFS29/CFS30 on the actual v2 slot
(closed `gafStage_marker_inputs_GAF5`).

* `markerCutoffW_BAUGD m` — the W-extended cutoff of a marker chart (circle: BAUG-D G4's
  `circleCutoffW_BAUGD`; slim / `edgeB`: BAUG-PSI's `slimCutoffW_BAUGP2`, `edgeCutoffW_BAUGP2`);
* `markerCLM_boundaryOriginalMap_BAUGD` (`v_m(F_∂ p) = ρ(c_m) ζ_m(p)` on all of `W`),
  `markerCutoffW_nonneg_BAUGD`, `marker_scale_comparable_BAUGD` (`ζ_m > 0 ⟹ 3R/4 ≤ ρ ≤ 5R/4`),
  `markerCutoffW_eq_one_of_core7_BAUGD` (a threshold-`7` core point is in the plateau);
* on the v2 slot: `markerCLM_stageProj_BAUGD`, `markerTag_mem_stageTagsV2_BAUGD`,
  `stage_marker_retained_BAUGD` (hret), `stage_marker_support_BAUGD` (hsup),
  `stage_marker_full_BAUGD` (hfull).
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

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **The W-extended cutoff of a marker chart**: circle `circleCutoffW_BAUGD`, slim
`slimCutoffW_BAUGP2`, `edgeB` `edgeCutoffW_BAUGP2` (zero extensions from `W°`). -/
def markerCutoffW_BAUGD : S.MarkerIdx_BAUGC → W.Carrier → ℝ
  | .inl j => S.circleCutoffW_BAUGD j
  | .inr (.inl j) => S.slimCutoffW_BAUGP2 j
  | .inr (.inr j) => S.edgeCutoffW_BAUGP2 j

/-- The circle cutoff on `W` takes values in `[0, 1]`. -/
theorem circleCutoffW_mem_Icc_BAUGD (j : S.CircleIdx_BAUGD) (p : W.Carrier) :
    S.circleCutoffW_BAUGD j p ∈ Icc (0 : ℝ) 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hq
    rw [S.circleCutoffW_val_BAUGD]
    exact S.family.circle.cutoff_mem_Icc j.1 ((Set.Finite.mem_toFinset _).mp j.2) q
  · rw [S.circleCutoffW_of_notMem_BAUGD j hq]
    exact ⟨le_rfl, zero_le_one⟩

/-- **The marker blocks of `F_∂` on `W`**: `v_m(F_∂ p) = ρ(c_m) ζ_m(p)`. -/
theorem markerCLM_boundaryOriginalMap_BAUGD (m : S.MarkerIdx_BAUGC) (p : W.Carrier) :
    S.markerCLM_BAUGC m (S.boundaryOriginalMap p) =
      S.rho (S.markerCentre_BAUGC m) * S.markerCutoffW_BAUGD m p := by
  rcases m with j | j | j
  · exact (S.circleBlock_boundaryOriginalMap_BAUGD j p).2
  · exact (S.slimBlock_boundaryOriginalMap_BAUGP2 j p).2
  · exact (S.edgeBlock_boundaryOriginalMap_BAUGP2 j p).2

/-- The marker cutoffs are nonnegative. -/
theorem markerCutoffW_nonneg_BAUGD (hΔ : 0 < Δ) (m : S.MarkerIdx_BAUGC) (p : W.Carrier) :
    0 ≤ S.markerCutoffW_BAUGD m p := by
  rcases m with j | j | j
  · exact (S.circleCutoffW_mem_Icc_BAUGD j p).1
  · exact (S.slimCutoffW_mem_Icc_BAUGP2 j p).1
  · exact (S.edgeCutoffW_mem_Icc_BAUGP2 hΔ j p).1

/-- **Comparability on the marker supports**: `ζ_m(p) > 0 ⟹ 3ρ(c_m)/4 ≤ ρ(p) ≤ 5ρ(c_m)/4`. -/
theorem marker_scale_comparable_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (m : S.MarkerIdx_BAUGC) (p : W.Carrier) (hpos : 0 < S.markerCutoffW_BAUGD m p) :
    3 / 4 * S.rho (S.markerCentre_BAUGC m) ≤ S.rho p ∧
      S.rho p ≤ 5 / 4 * S.rho (S.markerCentre_BAUGC m) := by
  rcases m with j | j | j
  · exact S.circle_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb j p hpos
  · exact (S.slim_scale_comparable_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb j p hpos).imp_right And.left
  · exact (S.edge_scale_comparable_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb j p hpos).imp_right And.left

/-- **A threshold-`7` core point is in the plateau** of its marker chart: `ζ_m(q) = 1`. -/
theorem markerCutoffW_eq_one_of_core7_BAUGD (hΔ : 0 < Δ) (m : S.MarkerIdx_BAUGC)
    {q : W.pieceInterior ⊤} (hq : q ∈ S.markerCore7_BAUGC m) :
    S.markerCutoffW_BAUGD m q.val = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  rcases m with j | j | j
  · obtain ⟨hd, hη⟩ := hq
    change S.circleCutoffW_BAUGD j q.val = 1
    rw [S.circleCutoffW_val_BAUGD]
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hd' := inv_mul_dist_lt_of_mem_ball_LC87 (X := W.pieceInterior ⊤)
      (ρ := fun x : W.pieceInterior ⊤ => S.rho x) (S.rho_pos j.1) (mem_ball.mpr hd)
    have hη' : ‖S.circleCoordW_BAUGD j q.val‖ ≤ 7 := by
      rw [← S.circleEta_eq_circleCoordW_BAUGD]
      exact hη
    rw [S.circleCoordW_val_BAUGD] at hη'
    simp only [CircleFamilyOn.coord_BAUGA, hj, ↓reduceDIte] at hη'
    exact S.family.circle.cutoff_eq_one j.1 hj q hd' (hη'.trans (by norm_num))
  · obtain ⟨hd, hη⟩ := hq
    change S.slimCutoffW_BAUGP2 j q.val = 1
    rw [S.slimCutoffW_val_BAUGP2]
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    rw [S.family.slim.cutoff_BCNT_of_mem hj]
    refine (S.family.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le_BAUGP2 ?_ ?_
    · rw [mem_ball]
      convert hd using 2
      norm_num
    · rw [← S.slimEta_eq_coord_BAUGP2 j q]
      have : (7 : ℝ) * (100000 * Δ) ≤ 8 * 10 ^ 5 * Δ := by nlinarith
      linarith
  · obtain ⟨hd, hη, ht⟩ := hq
    change S.edgeCutoffW_BAUGP2 j q.val = 1
    have hdom : q.val ∈ S.edgeDomW_BAUGP2 j := ⟨q, mem_ball.mpr hd, rfl⟩
    have hc : ‖S.edgeCoordW_BAUGP2 j q.val‖ < 8 * Δ := by
      rw [S.norm_edgeCoordW_val_BAUGP2]
      linarith
    rw [S.edgeCutoffW_identity_BAUGP2 hΔ j q.val hdom hc, S.edgeHeightW_val_BAUGP2]
    have ht' : S.edgeHeightRaw q / Δ ≤ 8 := by
      rw [div_le_iff₀ hΔ]
      linarith
    rw [cfsRamp_eq_zero (fun _ ht => lc87EdgeTransition_eq_zero ht) (by norm_num) ht', sub_zero]

/-- A point where some marker cutoff is positive is an interior point. -/
theorem interior_of_markerCutoffW_pos_BAUGD (m : S.MarkerIdx_BAUGC) {p : W.Carrier}
    (hpos : 0 < S.markerCutoffW_BAUGD m p) : ∃ q : W.pieceInterior ⊤, q.val = p := by
  by_contra hp
  rcases m with j | j | j
  · exact absurd hpos (by
      change ¬ 0 < S.circleCutoffW_BAUGD j p
      rw [S.circleCutoffW_of_notMem_BAUGD j hp]; exact lt_irrefl 0)
  · exact absurd hpos (by
      change ¬ 0 < S.slimCutoffW_BAUGP2 j p
      rw [S.slimCutoffW_of_notMem_BAUGP2 j hp]; exact lt_irrefl 0)
  · exact absurd hpos (by
      change ¬ 0 < S.edgeCutoffW_BAUGP2 j p
      rw [S.edgeCutoffW_of_notMem_BAUGP2 j hp]; exact lt_irrefl 0)

/-- The marker tag of a marker chart of stage `st` is a stage tag of `st` (v2 slot). -/
theorem markerTag_mem_stageTagsV2_BAUGD (m : S.MarkerIdx_BAUGC) :
    S.markerTag_BAUGC m ∈ S.stageTagsV2_BAUGD (S.markerStage_BAUGC m) := by
  rcases m with j | j | j
  · exact Finset.mem_univ _
  · exact S.slimTag_mem_stageTagsV2_BAUGD 2 j
  · exact mem_stageTagsV2_one_BAUGD.mpr rfl

end BoundarySupplyCore

section Stage

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

/-- The marker of a stage projection: kept if the tag is a stage tag, zero otherwise. -/
theorem markerCLM_stageProj_BAUGD (st : Fin 3) (m : S.MarkerIdx_BAUGC)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.markerCLM_BAUGC m ((actualSlotsV2_BAUGD S).stageProj st y) =
      if S.markerTag_BAUGC m ∈ S.stageTagsV2_BAUGD st then S.markerCLM_BAUGC m y else 0 := by
  have hiff : (Sum.inl (S.markerTag_BAUGC m) : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug st ↔
        S.markerTag_BAUGC m ∈ S.stageTagsV2_BAUGD st :=
    Finset.inl_mem_disjSum
  by_cases h : S.markerTag_BAUGC m ∈ S.stageTagsV2_BAUGD st
  · rw [ite_eq_left h]
    simp only [BoundarySupplyCore.markerCLM_BAUGC, blockMarkerCLM_apply,
      BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hiff.mpr h, ite_true]
  · rw [ite_eq_right h]
    have h' := mt hiff.mp h
    simp only [BoundarySupplyCore.markerCLM_BAUGC, blockMarkerCLM_apply,
      BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, h', ite_false]
    rfl

/-- (hret) on the v2 slot: the marker line of every chart lies in `Q_st` or in `Q_stᗮ`. -/
theorem stage_marker_retained_BAUGD (st : Fin 3) (m : S.MarkerIdx_BAUGC) :
    (LinearMap.ker (S.markerCLM_BAUGC m :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ))ᗮ ≤
        (actualSlotsV2_BAUGD S).stageQ st ∨
      (LinearMap.ker (S.markerCLM_BAUGC m :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ))ᗮ ≤
        ((actualSlotsV2_BAUGD S).stageQ st)ᗮ :=
  blockMarker_retained_GAF4 _ _

/-- (hsup) on the v2 slot: a positive marker of `π_st F_∂(q)` gives `3R/4 ≤ ρ(q) ≤ 5R/4`. -/
theorem stage_marker_support_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (st : Fin 3) (m : S.MarkerIdx_BAUGC) (q : W.Carrier)
    (hq : 0 < S.markerCLM_BAUGC m (((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (S.boundaryOriginalMap q))) :
    3 * S.rho (S.markerCentre_BAUGC m) / 4 ≤ S.rho q ∧
      S.rho q ≤ 5 * S.rho (S.markerCentre_BAUGC m) / 4 := by
  rw [stageQ_starProjection_BAUGD, markerCLM_stageProj_BAUGD] at hq
  split_ifs at hq with h
  · rw [S.markerCLM_boundaryOriginalMap_BAUGD] at hq
    have hR := S.rho_pos (S.markerCentre_BAUGC m)
    have hζ : 0 < S.markerCutoffW_BAUGD m q := by
      by_contra hn
      have : S.rho (S.markerCentre_BAUGC m) * S.markerCutoffW_BAUGD m q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hR.le (not_lt.mp hn)
      linarith
    have := S.marker_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb m q hζ
    constructor <;> linarith [this.1, this.2]
  · exact absurd hq (lt_irrefl 0)

/-- (hfull) on the v2 slot: a stage-cloud point carries a full marker of its stage. -/
theorem stage_marker_full_BAUGD (hΔ : 0 < Δ) (st : Fin 3) (q : W.Carrier)
    (hq : ((actualSlotsV2_BAUGD S).stageQ st).starProjection (S.boundaryOriginalMap q) ∈
      (actualSlotsV2_BAUGD S).stageCloud st) :
    ∃ m : S.MarkerIdx_BAUGC, S.markerCLM_BAUGC m (((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (S.boundaryOriginalMap q)) = S.rho (S.markerCentre_BAUGC m) := by
  rw [stageQ_starProjection_BAUGD] at hq ⊢
  obtain ⟨q', hq', hx⟩ := hq
  rw [actualSlotsV2_stageCore_BAUGD, Set.mem_iUnion₂] at hq'
  obtain ⟨m, hm, hqm⟩ := hq'
  refine ⟨m, ?_⟩
  have hm' : S.markerStage_BAUGC m = st := hm
  have htag : S.markerTag_BAUGC m ∈ S.stageTagsV2_BAUGD st := by
    rw [← hm']; exact S.markerTag_mem_stageTagsV2_BAUGD m
  rw [← hx, markerCLM_stageProj_BAUGD, ite_eq_left htag, S.markerCLM_boundaryOriginalMap_BAUGD,
    S.markerCutoffW_eq_one_of_core7_BAUGD hΔ m hqm, mul_one]

/-- Every preimage of a stage-cloud point is an INTERIOR point (it carries a full marker). -/
theorem interior_of_stageCloud_BAUGD (hΔ : 0 < Δ) (st : Fin 3) (q : W.Carrier)
    (hq : ((actualSlotsV2_BAUGD S).stageQ st).starProjection (S.boundaryOriginalMap q) ∈
      (actualSlotsV2_BAUGD S).stageCloud st) : ∃ q' : W.pieceInterior ⊤, q'.val = q := by
  obtain ⟨m, hm⟩ := stage_marker_full_BAUGD hΔ st q hq
  rw [stageQ_starProjection_BAUGD, markerCLM_stageProj_BAUGD] at hm
  have hR := S.rho_pos (S.markerCentre_BAUGC m)
  split_ifs at hm with h
  · rw [S.markerCLM_boundaryOriginalMap_BAUGD] at hm
    refine S.interior_of_markerCutoffW_pos_BAUGD m ?_
    by_contra hn
    have : S.rho (S.markerCentre_BAUGC m) * S.markerCutoffW_BAUGD m q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hR.le (not_lt.mp hn)
    linarith
  · linarith

end Stage

end DifferentialGeometry.Geometry.Collapse
