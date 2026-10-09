import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffOne
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloud

/-!
# The `edgeB` markers of the actual stage-`1` clouds of a boundary supply (lane B-PORT-EDGEb)

The marker layer of `port_edge_interior_table_BAUGP` on the ACTUAL slot `actualSlotsV2_BAUGD S`
(`f(q) = π₁ F_∂(q)` for `q ∈ W°`; `S₁ = f(A₁)`, `S̃₁ = f(Ã₁)`, `A₁`, `Ã₁` the threshold-`7` / `8`
cores `B(j, 100Δρ_j) ∩ {|η_j| ≤ θΔ} ∩ {t ≤ θΔ}` of the `edgeB`
charts of the stored family, `t` the ONE
global height `edgeB.smoothing/ρ`). Pointwise twins of EGP07's marker lemmas
(`Fibration/ActualEdgeCloud.lean`: `EdgeFamily.le_of_cutoff_eq_one_KC5`, `egp07_full_marker`,
`egp07_exact_coordinate`) and of `fc27_edge_cloud_scale` / `fc27_edge_cloud_mcb`
(`projected_cloud_scale_KA3`); the boundary differences are only that the preimages lie in `W°`
(distances `d_ĝ`) and that the `edgeB` blocks of `F_∂` are read through BAUG-PSI's
`edgeBlock_boundaryOriginalMap_BAUGP2`.

* `EdgeFamilyOn.le_of_cutoff_eq_one_BPE` (generic regional edge family);
* `augIntProj_stageOne_BPE` (`pr_int ∘ π₁ ∘ F_∂ = π_{Q₂} ∘ F_int` on `W°`),
  `edgeMarker_stageProj_one_BPE`, `edgeVector_stageProj_one_BPE`;
* `edgeMarker_stageOne_BPE`, `edgeVector_stageOne_BPE`, `edgeBlock_stageOne_BPE` (the `edgeB` block
  `j` of `f(q)` is `(ρ_jζ_j(q) η_j(q), ρ_jζ_j(q))`);
* `edge_cutoff_eq_one_BPE` (plateau on the threshold-`8` core), `edge_core_of_cutoff_eq_one_BPE`
  (a full cutoff puts the point in the threshold-`8` core), `edge_dist_le_of_cutoff_ne_zero_BPE`
  (support `⊆ B̄(j, 14Δρ_j)`), `edge_dist_lt_of_cutoff_ne_zero_BPE` (chart ball);
* `exists_core_of_mem_stageCloud_one_BPE`, `exists_core_of_mem_stageCloudEnlarged_one_BPE`,
  `stageProj_mem_stageCloud_one_BPE`, `stageProj_mem_stageCloudEnlarged_one_BPE`;
* `edge_full_marker_BPE` (full marker at points of `S̃₁`), `edge_marker_scale_BPE` ((AS)),
  `lipschitzWith_edgeMarker_BPE`, **`edge_scale_ratio_BPE`** (CFS07's (MC) for ANY preimages of
  points of `S̃₁`, `3/5 … 5/3`).
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

section EdgeOn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ} {U₁ U₂ : Set X}

/-- Where a regional edge cutoff equals one, `x ∈ B(j, 100Δρ(j))`, `|η_j(x)| ≤ 8Δ` and
`F(x)/ρ(x) ≤ 8Δ` (both factors of `f(η_j/Δ)g(F/(ρΔ))` equal one; closed twin
`EdgeFamily.le_of_cutoff_eq_one_KC5`). -/
theorem EdgeFamilyOn.le_of_cutoff_eq_one_BPE
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hΔ : 0 < Δ) {j x : X}
    (h : F.cutoff_BAUGA j x = 1) :
    j ∈ F.centres ∧ x ∈ ball j (100 * Δ * ρ j) ∧ |F.coord_BAUGA j x| ≤ 8 * Δ ∧
      F.smoothing x / ρ x ≤ 8 * Δ := by
  obtain ⟨hj, hball, -, -⟩ := F.mem_of_cutoff_ne_zero_BAUGA hΔ (by rw [h]; exact one_ne_zero)
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
    rw [mem_ball]
    linarith
  rw [F.cutoff_eq_formula_BAUGA hj hx] at h
  have h1 := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9 (F.coord_BAUGA j x / Δ)
  have h2 := descendingIntervalProfile_mem_Icc 8 9 (F.smoothing x / ρ x / Δ)
  obtain ⟨hf, hg⟩ := eq_one_of_mul_eq_one_KC5 h1 h2 h
  have hη := abs_le_of_edgeCoordinateProfile_eq_one_KC5 hf
  have ht := le_of_descendingIntervalProfile_eq_one_KC5 (by norm_num) hg
  refine ⟨hj, hx, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ] at hη
    linarith
  · rw [div_le_iff₀ hΔ] at ht
    linarith

end EdgeOn

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- The `edgeB` tags are tags of stage `1`. -/
theorem edgeTag_mem_stageTagsV2_one_BPE (j : S.EdgeIdx_BAUGD) :
    (.inr (.inr (.inl j)) : S.IntTag_BAUGA) ∈ S.stageTagsV2_BAUGD 1 :=
  BoundarySupplyCore.mem_stageTagsV2_one_BAUGD.mpr rfl

/-- **`pr_int ∘ π₁ ∘ F_∂ = π_{Q₂} ∘ F_int` on `W°`.** -/
theorem augIntProj_stageOne_BPE (x : W.pieceInterior ⊤) :
    augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap x.val)) =
      blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) := by
  refine PiLp.ext fun t => ?_
  rw [augIntProjCLM_apply_BAUGC]
  simp only [BoundaryInteriorSlots_BIF.stageProj, BoundaryInteriorSlots_BIF.stageTagsAug,
    blockRestrict_apply, Finset.inl_mem_disjSum, actualSlotsV2_stageTags_BAUGD]
  split_ifs
  · exact S.boundaryOriginalMap_inl_BPS x t
  · rfl

/-- A kept `edgeB` block: the edge marker of `π₁ y` is that of `y`. -/
theorem edgeMarker_stageProj_one_BPE (j : S.EdgeIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 y) = S.edgeMarker_BAUGD j y := by
  have hmem : (Sum.inl (.inr (.inr (.inl j))) : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug 1 :=
    Finset.inl_mem_disjSum.mpr (S.edgeTag_mem_stageTagsV2_one_BPE j)
  exact blockMarkerCLM_blockRestrict_BAUGC _ hmem y

/-- A kept `edgeB` block: the edge vector of `π₁ y` is that of `y`. -/
theorem edgeVector_stageProj_one_BPE (j : S.EdgeIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeVector_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 y) = S.edgeVector_BAUGD j y := by
  have hmem : (Sum.inl (.inr (.inr (.inl j))) : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug 1 :=
    Finset.inl_mem_disjSum.mpr (S.edgeTag_mem_stageTagsV2_one_BPE j)
  simp only [BoundarySupplyCore.edgeVector_BAUGD, blockVectorCLM_apply,
    BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hmem, ite_true]

/-- The edge marker `j` of `f(q) = π₁F_∂(q)` is `ρ_j ζ_j(q)`. -/
theorem edgeMarker_stageOne_BPE (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)) =
      S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        S.family.edgeB.cutoff_BAUGA j.1 q) := by
  rw [S.edgeMarker_stageProj_one_BPE j, (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).2,
    S.edgeCutoffW_val_BAUGP2]

/-- The edge vector `j` of `f(q) = π₁F_∂(q)` is `ρ_j ζ_j(q) η_j(q)`. -/
theorem edgeVector_stageOne_BPE (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeVector_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)) =
      (S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        S.family.edgeB.cutoff_BAUGA j.1 q)) • planeAxis (S.edgeEta_BIF j.1 q) := by
  rw [S.edgeVector_stageProj_one_BPE j, (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).1,
    S.edgeCutoffW_val_BAUGP2, S.edgeCoordW_val_BAUGP2, S.edgeEta_eq_coord_BAUGP2]

/-- The whole `edgeB` block `j` of `f(q) = π₁F_∂(q)`: `(ρ_jζ_j(q) η_j(q), ρ_jζ_j(q))`. -/
theorem edgeBlock_stageOne_BPE (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)
        (Sum.inl (.inr (.inr (.inl j)))) =
      WithLp.toLp 2 ((S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.edgeB.cutoff_BAUGA j.1 q)) • planeAxis (S.edgeEta_BIF j.1 q),
        S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.edgeB.cutoff_BAUGA j.1 q)) := by
  rw [← S.edgeVector_stageOne_BPE j q, ← S.edgeMarker_stageOne_BPE j q]
  rfl

/-- **The edge plateau**: `ζ_j(q) = 1` on the threshold-`8` core of `j`. -/
theorem edge_cutoff_eq_one_BPE (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 8 * Δ) (ht : S.edgeHeightRaw q ≤ 8 * Δ) :
    (letI := inducedMetricSpace S.completion.metric
     letI := S.completion.complete
     S.family.edgeB.cutoff_BAUGA j.1 q) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.edgeEta_eq_coord_BAUGP2] at hη
  exact S.family.edgeB.cutoff_eq_one_of_le_BCF2K hΔ hj (mem_ball.mpr hd) hη ht

/-- **A full edge cutoff puts the point in the threshold-`8` core** (closed
`EdgeFamily.le_of_cutoff_eq_one_KC5`). -/
theorem edge_core_of_cutoff_eq_one_BPE (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.cutoff_BAUGA j.1 q) = 1) :
    (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1) ∧
      |S.edgeEta_BIF j.1 q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨-, hx, hη, ht⟩ := S.family.edgeB.le_of_cutoff_eq_one_BPE hΔ hq
  refine ⟨mem_ball.mp hx, ?_, ht⟩
  rw [S.edgeEta_eq_coord_BAUGP2]
  exact hη

/-- **The edge support**: `ζ_j(q) ≠ 0 ⟹ d(q, j) ≤ 14Δρ_j` (FC18 (ii) on the boundary family). -/
theorem edge_dist_le_of_cutoff_ne_zero_BPE (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.cutoff_BAUGA j.1 q) ≠ 0) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 ≤ 14 * Δ * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have h := (LocalPacketsOnB.tsupport_edgeB_cutoff_subset_BAUGA
    S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB hΛ hΔ hμ hτ hΔΛ hj).1
    (subset_tsupport _ hq)
  exact mem_closedBall.mp h

/-- The edge support lies in the chart ball: `ζ_j(q) ≠ 0 ⟹ d(q, j) < 100Δρ_j`. -/
theorem edge_dist_lt_of_cutoff_ne_zero_BPE (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.cutoff_BAUGA j.1 q) ≠ 0) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 < 100 * Δ * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨-, hball, -, -⟩ := S.family.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hq
  have hh := (inv_mul_lt_iff₀ (S.rho_pos j.1)).mp hball
  linarith

/-- A point of the core cloud `S₁` has a threshold-`7` core preimage of an `edgeB` chart. -/
theorem exists_core_of_mem_stageCloud_one_BPE {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1) :
    ∃ (j : S.EdgeIdx_BAUGD) (p : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist p j.1 < 100 * Δ * S.rho j.1) ∧
      |S.edgeEta_BIF j.1 p| ≤ 7 * Δ ∧ S.edgeHeightRaw p ≤ 7 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [actualSlotsV2_stageCore_BAUGD, mem_iUnion₂] at hp
  obtain ⟨m, hm, hpm⟩ := hp
  rcases m with j | j | j
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact ⟨j, p, hpm.1, hpm.2.1, hpm.2.2, rfl⟩

/-- A point of the enlarged cloud `S̃₁` has a threshold-`8` core preimage of an `edgeB` chart. -/
theorem exists_core_of_mem_stageCloudEnlarged_one_BPE {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1) :
    ∃ (j : S.EdgeIdx_BAUGD) (p : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist p j.1 < 100 * Δ * S.rho j.1) ∧
      |S.edgeEta_BIF j.1 p| ≤ 8 * Δ ∧ S.edgeHeightRaw p ≤ 8 * Δ ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [actualSlotsV2_stageEnlargement_BAUGD, mem_iUnion₂] at hp
  obtain ⟨m, hm, hpm⟩ := hp
  rcases m with j | j | j
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact absurd hm (by simp [BoundarySupplyCore.markerStage_BAUGC])
  · exact ⟨j, p, hpm.1, hpm.2.1, hpm.2.2, rfl⟩

/-- A threshold-`8` core point of an `edgeB` chart maps into `S̃₁`. -/
theorem stageProj_mem_stageCloudEnlarged_one_BPE (j : S.EdgeIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 p| ≤ 8 * Δ) (ht : S.edgeHeightRaw p ≤ 8 * Δ) :
    (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 :=
  ⟨p, mem_iUnion₂.mpr ⟨.inr (.inr j), rfl, hd, hη, ht⟩, rfl⟩

/-- A threshold-`7` core point of an `edgeB` chart maps into `S₁`. -/
theorem stageProj_mem_stageCloud_one_BPE (j : S.EdgeIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 p| ≤ 7 * Δ) (ht : S.edgeHeightRaw p ≤ 7 * Δ) :
    (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud 1 :=
  ⟨p, mem_iUnion₂.mpr ⟨.inr (.inr j), rfl, hd, hη, ht⟩, rfl⟩

/-- **Full markers on `S̃₁`**: at a point of the enlarged cloud some edge marker is `ρ_j`. -/
theorem edge_full_marker_BPE (hΔ : 0 < Δ)
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1) :
    ∃ j : S.EdgeIdx_BAUGD, S.edgeMarker_BAUGD j x = S.rho j.1 := by
  obtain ⟨j, p, hd, hη, ht, rfl⟩ := S.exists_core_of_mem_stageCloudEnlarged_one_BPE hx
  refine ⟨j, ?_⟩
  rw [S.edgeMarker_stageOne_BPE j p, S.edge_cutoff_eq_one_BPE hΔ j hd hη ht, mul_one]

/-- **(AS)**: a positive edge marker `j` at `f(q)` gives `3ρ_j/4 ≤ ρ(q) ≤ 5ρ_j/4`. -/
theorem edge_marker_scale_BPE (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hpos : 0 < S.edgeMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))) :
    3 * S.rho j.1 / 4 ≤ S.rho q.val ∧ S.rho q.val ≤ 5 * S.rho j.1 / 4 := by
  rw [S.edgeMarker_stageProj_one_BPE j, (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).2] at hpos
  have hrj := S.rho_pos j.1
  have hc : 0 < S.edgeCutoffW_BAUGP2 j q.val := pos_of_mul_pos_right hpos hrj.le
  obtain ⟨h1, h2, -⟩ := S.edge_scale_comparable_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb j q.val hc
  constructor <;> linarith

/-- The edge markers are `1`-Lipschitz on `H^∂`. -/
theorem lipschitzWith_edgeMarker_BPE (j : S.EdgeIdx_BAUGD) :
    LipschitzWith 1 (S.edgeMarker_BAUGD j) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (by
    rw [NNReal.coe_one]
    exact norm_blockMarkerCLM_le _)

/-- **CFS07's (MC) on the enlarged edge cloud for ANY preimages** (closed twin: the fourth clause of
`fc27_edge_cloud_scale`): if `f(p), f(q) ∈ S̃₁` and `|f(q) − f(p)| ≤ L'·max(σρ(q), σρ(p))` with
`L'σ ≤ 1/5`, then `3/5 ≤ ρ(q)/ρ(p) ≤ 5/3`. -/
theorem edge_scale_ratio_BPE (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {σ L' : ℝ} (hσ : 0 ≤ σ) (hL' : 0 ≤ L')
    (hLσ : L' * σ ≤ 1 / 5) {p q : W.pieceInterior ⊤}
    (hp : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1)
    (hq : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged 1)
    (hd : dist ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))
        ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val)) ≤
      L' * max (σ * S.rho q.val) (σ * S.rho p.val)) :
    3 / 5 * S.rho p.val ≤ S.rho q.val ∧ S.rho q.val ≤ 5 / 3 * S.rho p.val := by
  have hΔ : 0 < Δ := by linarith
  obtain ⟨i, hi⟩ := S.edge_full_marker_BPE hΔ hp
  obtain ⟨j, hj⟩ := S.edge_full_marker_BPE hΔ hq
  exact scale_ratio_of_any_preimages_KA3
    (fun p : W.pieceInterior ⊤ =>
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
    (fun p : W.pieceInterior ⊤ => S.rho p.val) (fun j : S.EdgeIdx_BAUGD => S.edgeMarker_BAUGD j)
    (fun j : S.EdgeIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos j.1)
    (fun j => S.lipschitzWith_edgeMarker_BPE j)
    (fun j q h => S.edge_marker_scale_BPE hΛ hΔ1 hΛΔ hV hβ1 hb j q h) hσ hL' hLσ hi hj hd

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
