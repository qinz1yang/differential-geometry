import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstCloudCoverage
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEScaleB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersion

/-!
# Pointwise clauses of the circle stage table on a boundary supply (lane O-PORT-A)

The stage-`0` layer of `port_circle_interior_table_BAUGP` (PortTargets v3.1) on the ACTUAL slot
`actualSlotsV2_BAUGD S` (`f(q) = π₀F_∂(q) = F_∂(q)`, `q ∈ W°`, distances `d_ĝ`; `S₀ = f(A₀)`,
`S̃₀ = f(Ã₀)`, `A₀`, `Ã₀` the threshold-`7` / `8` cores `B(j, 200ρ_j) ∩ {‖η_j‖ ≤ θ}` of the circle
charts of the stored family). Closed twins: `tcp06_full_marker_KA8` (PRE), `tcp06_localization_KA8`
(LOC), `circle_coord_cover_KA8` (COV), all in `Fibration/ActualFirstCloudCoverage.lean`, applied
through their boundary ports (`BoundaryPortFirstCloudCoverage`) to the stored family on `W°`; the
reference domain `D_a = B(a, 10ρ(a))` (`stageDomain_BIF Δ 0`) contains every threshold-`8` core
point (TCP01's circle enclosure `circle_dist_lt_ten_BAUGD`).

* `stageDomain_zero_BPC`, `stageCentres_zero_BPC`, `stageTagsV2_zero_BPC`,
  `blockRestrict_stageTagsV2_zero_BPC` (`π_{Q₁} = id` on the interior tags);
* `augIntProj_stageZero_BPC` (`pr_int ∘ π₀ ∘ F_∂ = F_int` on `W°`),
  `interiorMapOn_eq_of_stageProj_zero_BPC`, `augIntProj_sub_stageZero_BPC`;
* `exists_core_of_mem_stageCloud_zero_BPC`, `exists_core_of_mem_stageCloudEnlarged_zero_BPC`,
  `stageProj_mem_stageCloud_zero_BPC`, `stageProj_mem_stageCloudEnlarged_zero_BPC`;
* `circle_dist_lt_ten_BPC` (a threshold-`8` core point lies in `D_j`);
* `circle_preimage_core_BPC` (PRE), `circle_localization_BPC` (LOC), `circle_coverage_BPC` (COV).
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

/-- The circle reference domain constant: `C_0 = 10`. -/
theorem stageDomain_zero_BPC (Δ : ℝ) : stageDomain_BIF Δ 0 = 10 :=
  rfl

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- The circle centres are the stage-`0` centres. -/
theorem stageCentres_zero_BPC :
    S.stageCentres_BIF 0 = (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.circle.centres) :=
  rfl

/-- The stage-`0` tags are all interior tags (`Q₁^∂ ∩ H_int = H_int`). -/
theorem stageTagsV2_zero_BPC : S.stageTagsV2_BAUGD 0 = Finset.univ :=
  rfl

open Classical in
/-- `π_{Q₁} = id` on the interior block space. -/
theorem blockRestrict_stageTagsV2_zero_BPC (z : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) :
    blockRestrict (S.stageTagsV2_BAUGD 0) z = z := by
  rw [S.stageTagsV2_zero_BPC, blockRestrict_univ]
  rfl

/-- **`pr_int ∘ π₀ ∘ F_∂ = F_int` on `W°`.** -/
theorem augIntProj_stageZero_BPC (x : W.pieceInterior ⊤) :
    augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap x.val)) =
      S.interiorMapOn_BAUGA x := by
  rw [stageProj_zero_V2_BAUGD S]
  refine PiLp.ext fun t => ?_
  rw [augIntProjCLM_apply_BAUGC]
  exact S.boundaryOriginalMap_inl_BPS x t

/-- Two interior points with the same image in `H^∂` have the same interior image. -/
theorem interiorMapOn_eq_of_stageProj_zero_BPC {p q : W.pieceInterior ⊤}
    (h : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) =
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val)) :
    S.interiorMapOn_BAUGA q = S.interiorMapOn_BAUGA p := by
  rw [← S.augIntProj_stageZero_BPC q, h, S.augIntProj_stageZero_BPC p]

/-- The interior part of a difference of images is the difference of the interior images. -/
theorem augIntProj_sub_stageZero_BPC (p q : W.pieceInterior ⊤) :
    augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) -
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val)) =
      S.interiorMapOn_BAUGA q - S.interiorMapOn_BAUGA p := by
  rw [map_sub, S.augIntProj_stageZero_BPC q, S.augIntProj_stageZero_BPC p]

/-- A point of the core cloud `S₀` has a threshold-`7` core preimage of a circle chart. -/
theorem exists_core_of_mem_stageCloud_zero_BPC {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0) :
    ∃ (j : S.CircleIdx_BAUGD) (p : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1) ∧
      ‖S.circleEta_BIF j.1 p‖ ≤ 7 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [actualSlotsV2_stageCore_BAUGD, mem_iUnion₂] at hp
  obtain ⟨m, hm, hpm⟩ := hp
  rcases m with j | j | j
  · exact ⟨j, p, hpm.1, hpm.2, rfl⟩
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])

/-- A point of the enlarged cloud `S̃₀` has a threshold-`8` core preimage of a circle chart. -/
theorem exists_core_of_mem_stageCloudEnlarged_zero_BPC {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0) :
    ∃ (j : S.CircleIdx_BAUGD) (p : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1) ∧
      ‖S.circleEta_BIF j.1 p‖ ≤ 8 ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [actualSlotsV2_stageEnlargement_BAUGD, mem_iUnion₂] at hp
  obtain ⟨m, hm, hpm⟩ := hp
  rcases m with j | j | j
  · exact ⟨j, p, hpm.1, hpm.2, rfl⟩
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])

/-- A threshold-`7` core point of a circle chart maps into `S₀`. -/
theorem stageProj_mem_stageCloud_zero_BPC (j : S.CircleIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 p‖ ≤ 7) :
    (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 0 :=
  ⟨p, mem_iUnion₂.mpr ⟨.inl j, rfl, hd, hη⟩, rfl⟩

/-- A threshold-`8` core point of a circle chart maps into `S̃₀`. -/
theorem stageProj_mem_stageCloudEnlarged_zero_BPC (j : S.CircleIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 p‖ ≤ 8) :
    (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 :=
  ⟨p, mem_iUnion₂.mpr ⟨.inl j, rfl, hd, hη⟩, rfl⟩

/-- **A threshold-`8` core point lies in `D_j = B(j, 10ρ_j)`** (TCP01's circle enclosure). -/
theorem circle_dist_lt_ten_BPC (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ ≤ 8) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 < stageDomain_BIF Δ 0 * S.rho j.1 := by
  rw [stageDomain_zero_BPC]
  rw [S.circleEta_eq_circleCoordW_BAUGD j q] at hη
  exact S.circle_dist_lt_ten_BAUGD j q hd hη

/-- **(PRE) at one core witness** (closed `tcp06_full_marker_KA8`): a preimage `q` of `f(p)`, `p` in
the threshold-`8` core of the circle chart `j`, has the same coordinate `η_j(q) = η_j(p)`, lies in
the threshold-`8` core and in `D_j`. -/
theorem circle_preimage_core_BPC (j : S.CircleIdx_BAUGD) {p q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 p‖ ≤ 8)
    (hpq : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) =
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val)) :
    letI := inducedMetricSpace S.completion.metric
    (dist q j.1 < 200 * S.rho j.1 ∧ ‖S.circleEta_BIF j.1 q‖ ≤ 8) ∧
      dist q j.1 < stageDomain_BIF Δ 0 * S.rho j.1 ∧
      S.circleEta_BIF j.1 q = S.circleEta_BIF j.1 p := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hF := S.interiorMapOn_eq_of_stageProj_zero_BPC hpq
  rw [S.interiorMapOn_eq_cgpGlobalMap_BAUGP] at hF
  have hc := S.circleEta_eq_cgpCircleCoord_BBP j
  have hη' : ‖cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB j.1 hj p‖ ≤ 8 := by
    rw [← hc]
    exact hη
  obtain ⟨hqd, hqη⟩ := tcp06_full_marker_KA8_BAUGP S.family.toLocalPacketsOnB hj j rfl hd hη' hF
  have hqe : S.circleEta_BIF j.1 q = S.circleEta_BIF j.1 p := by
    rw [hc]
    exact hqη
  have hq8 : ‖S.circleEta_BIF j.1 q‖ ≤ 8 := by
    rw [hqe]
    exact hη
  exact ⟨⟨hqd, hq8⟩, S.circle_dist_lt_ten_BPC j hqd hq8, hqe⟩

/-- **(LOC) at one core witness** (closed `tcp06_localization_KA8`): if `p` is in the threshold-`7`
core of the circle chart `j` and `‖pr_int(f(q) − f(p))‖ ≤ Rρ_j` with `R < 1/100`, then `q` is in
the threshold-`8` core of `j` and in `D_j`. -/
theorem circle_localization_BPC (j : S.CircleIdx_BAUGD) {p q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 p‖ ≤ 7) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 100)
    (hpq : ‖augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) -
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))‖ ≤ R * S.rho j.1) :
    letI := inducedMetricSpace S.completion.metric
    (dist q j.1 < 200 * S.rho j.1 ∧ ‖S.circleEta_BIF j.1 q‖ ≤ 8) ∧
      dist q j.1 < stageDomain_BIF Δ 0 * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.augIntProj_sub_stageZero_BPC, S.interiorMapOn_eq_cgpGlobalMap_BAUGP, ← dist_eq_norm] at hpq
  have hc := S.circleEta_eq_cgpCircleCoord_BBP j
  have hη' : ‖cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB j.1 hj p‖ ≤ 7 := by
    rw [← hc]
    exact hη
  obtain ⟨hqd, -, -, hqη⟩ :=
    tcp06_localization_KA8_BAUGP S.family.toLocalPacketsOnB hj j rfl hd hη' hR0 hR hpq
  have hq8 : ‖S.circleEta_BIF j.1 q‖ ≤ 8 := by
    rw [hc]
    exact hqη.le
  exact ⟨⟨hqd, hq8⟩, S.circle_dist_lt_ten_BPC j hqd hq8⟩

/-- **(COV) at one core witness** (closed `circle_coord_cover_KA8`): for `p` in the threshold-`7`
core of the circle chart `j` and `‖u − η_j(p)‖ ≤ 1` there is `q` in the threshold-`8` core of `j`
and in `D_j` with `η_j(q) = u` and `f(q) ∈ S̃₀`. -/
theorem circle_coverage_BPC (j : S.CircleIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hη : ‖S.circleEta_BIF j.1 p‖ ≤ 7) {u : ℝ²} (hu : ‖u - S.circleEta_BIF j.1 p‖ ≤ 1) :
    letI := inducedMetricSpace S.completion.metric
    ∃ q : W.pieceInterior ⊤, (dist q j.1 < 200 * S.rho j.1 ∧ ‖S.circleEta_BIF j.1 q‖ ≤ 8) ∧
      dist q j.1 < stageDomain_BIF Δ 0 * S.rho j.1 ∧ S.circleEta_BIF j.1 q = u ∧
      (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hu8 : ‖u‖ ≤ 8 := by
    have := norm_le_norm_add_norm_sub' u (S.circleEta_BIF j.1 p)
    linarith
  obtain ⟨q, hqd, hqu⟩ :=
    circle_coord_cover_KA8_BAUGP S.family.toLocalPacketsOnB hj (lt_of_le_of_lt hu8 (by norm_num))
  have hc := S.circleEta_eq_cgpCircleCoord_BBP j
  have hqe : S.circleEta_BIF j.1 q = u := by
    rw [hc]
    exact hqu
  have hq8 : ‖S.circleEta_BIF j.1 q‖ ≤ 8 := by
    rw [hqe]
    exact hu8
  exact ⟨q, ⟨hqd, hq8⟩, S.circle_dist_lt_ten_BPC j hqd hq8, hqe,
    S.stageProj_mem_stageCloudEnlarged_zero_BPC j hqd hq8⟩

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
