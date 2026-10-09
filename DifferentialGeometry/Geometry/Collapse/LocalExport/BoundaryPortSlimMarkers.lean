import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlotV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffTwo
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets

/-!
# The slim markers of the actual stage-`2` clouds of a boundary supply (lane B-PORT-SLIMb)

The marker layer of `port_slim_interior_table_BAUGP` on the ACTUAL slot `actualSlotsV2_BAUGD S`
(`f(q) = π₂ F_∂(q)` for `q ∈ W°`; `S₂ = f(A₂)`, `S̃₂ = f(Ã₂)`, `A₂`, `Ã₂` the threshold-`7` / `8` cores of
the slim charts of the stored family). Closed twins: `sgp05_full_marker`, `fc27_slim_cloud_scale`
(`projected_cloud_scale_KA3`), `gafCloud_preimage_ratio_GAF4`; the boundary differences are only that
the preimages lie in `W°` (distances `d_ĝ`) and that the slim blocks of `F_∂` are read through
BAUG-PSI's `slimBlock_boundaryOriginalMap_BAUGP2`.

* `slimMarker_stageTwo_BPS`, `slimVector_stageTwo_BPS`: the slim block `j` of `f(q)` is
  `(ρ_jζ_j(q) η_j(q), ρ_jζ_j(q))`;
* `slim_cutoff_eq_one_BPS` (plateau), `slim_dist_le_of_cutoff_ne_zero_BPS` (support);
* `exists_core_of_mem_stageCloud_two_BPS`, `exists_core_of_mem_stageCloudEnlarged_two_BPS`,
  `stageProj_mem_stageCloudEnlarged_two_BPS`: points of `S₂`, `S̃₂` and their core preimages;
* `slim_full_marker_BPS` (full marker at points of `S̃₂`), `slim_marker_scale_BPS` ((AS));
* **`slim_scale_ratio_BPS`** (CFS07's (MC) for ANY preimages of points of `S̃₂`, `3/5 … 5/3`);
* `norm_inl_sub_le_augIntProj_BPS`, `augIntProj_stageTwo_BPS` (`pr_int ∘ π₂ ∘ F_∂ = π_{Q₃} ∘ F_int` on
  `W°`).
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

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- A single interior block is controlled by the interior projection: `‖y_t − x_t‖ ≤ ‖pr_int(y − x)‖`. -/
theorem norm_inl_sub_le_augIntProj_BPS (y x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (t : ι) :
    ‖y (Sum.inl t) - x (Sum.inl t)‖ ≤ ‖augIntProjCLM_BAUGC (y - x)‖ := by
  have h : augIntProjCLM_BAUGC (y - x) t = y (Sum.inl t) - x (Sum.inl t) := by
    rw [augIntProjCLM_apply_BAUGC]
    rfl
  rw [← h]
  exact PiLp.norm_apply_le _ _

/-- A single block is controlled by the distance: `‖y_t − x_t‖ ≤ ‖y − x‖`. -/
theorem norm_inl_sub_le_BPS (y x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (t : ι) :
    ‖y (Sum.inl t) - x (Sum.inl t)‖ ≤ ‖y - x‖ :=
  (norm_inl_sub_le_augIntProj_BPS y x t).trans (norm_augIntProj_le_BAUGC (y - x))

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- The interior slots of `F_∂` at an interior point are the interior formula. -/
theorem boundaryOriginalMap_inl_BPS (x : W.pieceInterior ⊤) (t : S.IntTag_BAUGA) :
    S.boundaryOriginalMap x.val (Sum.inl t) = S.interiorMapOn_BAUGA x t := by
  change S.interiorMapW_BAUGA x.val t = _
  rw [S.interiorMapW_val_BAUGA x]

/-- **`pr_int ∘ π₂ ∘ F_∂ = π_{Q₃} ∘ F_int` on `W°`.** -/
theorem augIntProj_stageTwo_BPS (x : W.pieceInterior ⊤) :
    augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap x.val)) =
      blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) := by
  refine PiLp.ext fun t => ?_
  rw [augIntProjCLM_apply_BAUGC]
  simp only [BoundaryInteriorSlots_BIF.stageProj, BoundaryInteriorSlots_BIF.stageTagsAug,
    blockRestrict_apply, Finset.inl_mem_disjSum, actualSlotsV2_stageTags_BAUGD]
  split_ifs
  · exact S.boundaryOriginalMap_inl_BPS x t
  · rfl

/-- The slim marker `j` of `f(q) = π₂F_∂(q)` is `ρ_j ζ_j(q)`. -/
theorem slimMarker_stageTwo_BPS (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.slimMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)) =
      S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        S.family.slim.cutoff_BCNT j.1 q) := by
  rw [slimMarker_stageProj_BAUGD S 2 j, (S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).2,
    S.slimCutoffW_val_BAUGP2]

/-- The slim vector `j` of `f(q) = π₂F_∂(q)` is `ρ_j ζ_j(q) η_j(q)`. -/
theorem slimVector_stageTwo_BPS (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.slimVector_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)) =
      (S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        S.family.slim.cutoff_BCNT j.1 q)) • planeAxis (S.slimEta_BIF j.1 q) := by
  rw [slimVector_stageProj_BAUGD S 2 j, (S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).1,
    S.slimCutoffW_val_BAUGP2, S.slimCoordW_val_BAUGP2, S.slimEta_eq_coord_BAUGP2]

/-- **The slim plateau**: `ζ_j(q) = 1` on the threshold-`8` core of `j`. -/
theorem slim_cutoff_eq_one_BPS (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| ≤ 8 * (100000 * Δ)) :
    (letI := inducedMetricSpace S.completion.metric
     letI := S.completion.complete
     S.family.slim.cutoff_BCNT j.1 q) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.family.slim.cutoff_BCNT_of_mem hj]
  rw [S.slimEta_eq_coord_BAUGP2] at hη
  refine (S.family.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le_BAUGP2 ?_ (by linarith)
  rw [mem_ball]
  have h : (10 : ℝ) ^ 6 * Δ * S.rho j.1 = 1000000 * Δ * S.rho j.1 := by norm_num
  rw [h]
  exact hd

/-- **The slim support**: `ζ_j(q) ≠ 0 ⟹ d(q, j) ≤ .91·10⁶Δρ_j`. -/
theorem slim_dist_le_of_cutoff_ne_zero_BPS (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.slim.cutoff_BCNT j.1 q) ≠ 0) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 ≤ 910000 * Δ * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have h := S.family.slim.tsupport_cutoff_subset_BCNT j.1 (subset_tsupport _ hq)
  rw [mem_closedBall] at h
  have he : 91 / 100 * (10 ^ 6 * Δ) * S.rho j.1 = 910000 * Δ * S.rho j.1 := by ring
  rw [he] at h
  exact h

/-- A point of the core cloud `S₂` has a threshold-`7` core preimage of a slim chart. -/
theorem exists_core_of_mem_stageCloud_two_BPS {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2) :
    ∃ (j : S.SlimIdx_BAUGD) (p : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist p j.1 < 1000000 * Δ * S.rho j.1) ∧
      |S.slimEta_BIF j.1 p| ≤ 7 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [actualSlotsV2_stageCore_BAUGD, mem_iUnion₂] at hp
  obtain ⟨m, hm, hpm⟩ := hp
  rcases m with j | j | j
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact ⟨j, p, hpm.1, hpm.2, rfl⟩
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])

/-- A point of the enlarged cloud `S̃₂` has a threshold-`8` core preimage of a slim chart. -/
theorem exists_core_of_mem_stageCloudEnlarged_two_BPS {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2) :
    ∃ (j : S.SlimIdx_BAUGD) (p : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist p j.1 < 1000000 * Δ * S.rho j.1) ∧
      |S.slimEta_BIF j.1 p| ≤ 8 * (100000 * Δ) ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [actualSlotsV2_stageEnlargement_BAUGD, mem_iUnion₂] at hp
  obtain ⟨m, hm, hpm⟩ := hp
  rcases m with j | j | j
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact ⟨j, p, hpm.1, hpm.2, rfl⟩
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])

/-- A threshold-`8` core point of a slim chart maps into `S̃₂`. -/
theorem stageProj_mem_stageCloudEnlarged_two_BPS (j : S.SlimIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 p| ≤ 8 * (100000 * Δ)) :
    (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 :=
  ⟨p, mem_iUnion₂.mpr ⟨.inr (.inl j), rfl, hd, hη⟩, rfl⟩

/-- A threshold-`7` core point of a slim chart maps into `S₂`. -/
theorem stageProj_mem_stageCloud_two_BPS (j : S.SlimIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 p| ≤ 7 * (100000 * Δ)) :
    (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 2 :=
  ⟨p, mem_iUnion₂.mpr ⟨.inr (.inl j), rfl, hd, hη⟩, rfl⟩

/-- **Full markers on `S̃₂`**: at a point of the enlarged cloud some slim marker is `ρ_j`. -/
theorem slim_full_marker_BPS {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2) :
    ∃ j : S.SlimIdx_BAUGD, S.slimMarker_BAUGD j x = S.rho j.1 := by
  obtain ⟨j, p, hd, hη, rfl⟩ := S.exists_core_of_mem_stageCloudEnlarged_two_BPS hx
  refine ⟨j, ?_⟩
  rw [S.slimMarker_stageTwo_BPS j p, S.slim_cutoff_eq_one_BPS j hd hη, mul_one]

/-- **(AS)**: a positive slim marker `j` at `f(q)` gives `3ρ_j/4 ≤ ρ(q) ≤ 5ρ_j/4`. -/
theorem slim_marker_scale_BPS (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hpos : 0 < S.slimMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val))) :
    3 * S.rho j.1 / 4 ≤ S.rho q.val ∧ S.rho q.val ≤ 5 * S.rho j.1 / 4 := by
  rw [slimMarker_stageProj_BAUGD S 2 j, (S.slimBlock_boundaryOriginalMap_BAUGP2 j q.val).2] at hpos
  have hrj := S.rho_pos j.1
  have hc : 0 < S.slimCutoffW_BAUGP2 j q.val := pos_of_mul_pos_right hpos hrj.le
  obtain ⟨h1, h2, -⟩ := S.slim_scale_comparable_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb j q.val hc
  constructor <;> linarith

/-- The slim markers are `1`-Lipschitz on `H^∂`. -/
theorem lipschitzWith_slimMarker_BPS (j : S.SlimIdx_BAUGD) :
    LipschitzWith 1 (S.slimMarker_BAUGD j) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (by
    rw [NNReal.coe_one]
    exact norm_blockMarkerCLM_le _)

/-- **CFS07's (MC) on the enlarged slim cloud for ANY preimages** (closed twin: the fourth clause of
`fc27_slim_cloud_scale`): if `f(p), f(q) ∈ S̃₂` and `|f(q) − f(p)| ≤ L'·max(σρ(q), σρ(p))` with
`L'σ ≤ 1/5`, then `3/5 ≤ ρ(q)/ρ(p) ≤ 5/3`. -/
theorem slim_scale_ratio_BPS (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {σ L' : ℝ} (hσ : 0 ≤ σ) (hL' : 0 ≤ L')
    (hLσ : L' * σ ≤ 1 / 5) {p q : W.pieceInterior ⊤}
    (hp : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2)
    (hq : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 2)
    (hd : dist ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val))
        ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val)) ≤
      L' * max (σ * S.rho q.val) (σ * S.rho p.val)) :
    3 / 5 * S.rho p.val ≤ S.rho q.val ∧ S.rho q.val ≤ 5 / 3 * S.rho p.val := by
  obtain ⟨i, hi⟩ := S.slim_full_marker_BPS hp
  obtain ⟨j, hj⟩ := S.slim_full_marker_BPS hq
  exact scale_ratio_of_any_preimages_KA3
    (fun p : W.pieceInterior ⊤ =>
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
    (fun p : W.pieceInterior ⊤ => S.rho p.val) (fun j : S.SlimIdx_BAUGD => S.slimMarker_BAUGD j)
    (fun j : S.SlimIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos j.1)
    (fun j => S.lipschitzWith_slimMarker_BPS j)
    (fun j q h => S.slim_marker_scale_BPS hΛ hΔ1 hΛΔ hV hβ1 hb j q h) hσ hL' hLσ hi hj hd

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
