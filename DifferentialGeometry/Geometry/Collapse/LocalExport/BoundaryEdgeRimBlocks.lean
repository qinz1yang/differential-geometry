import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffOne
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferNormal

/-!
# The `E'` and `edgeB` blocks of `F_∂` on the edge plateau (S-BAUG-D, G16 part b)

Closed twins: `edge_cutoff_eq_one_EDPE`, `edgeMarker_eq_one_EDPE`, `globalMap_heightAxis_EDPE`,
`globalMap_edgeAxis_EDPE` (`Fibration/ActualStageChainEdpBlocks.lean`). For the boundary supply
`S` (at an interior point `q` of the chart ball of an `edgeB` centre `j`):

* `edgeCutoff_eq_one_BAUGD`: `ζ_j(q) = 1` where `|η_j| < 8Δ`, `t ≤ 8Δ`;
* `edgeBMarker_eq_one_BAUGD`: `z_{E'}(q) = 1` where moreover `.3Δ ≤ t`;
* `heightCoord_boundaryOriginalMap_BAUGD`: `u_{E'}(F_∂ q) = z_{E'}(q) · F(q)` (`F` the smoothing);
* `edgeProj_boundaryOriginalMap_BAUGD`: `pr₀ u_j(F_∂ q) = ρ_j ζ_j(q) η_j(q)`;
* the open plateau region `edgeRegion_BAUGD` and the germ identities
  `heightCoord_boundaryOriginalMap_eq_BAUGD`, `edgeRatio_boundaryOriginalMap_eq_BAUGD`.
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

/-- The first coordinate of the plane axis vector. -/
theorem planeAxis_zero_BAUGD (t : ℝ) : (planeAxis t : ℝ²) 0 = t := by
  rw [planeAxis_apply]
  simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]

/-- A block coordinate read on the axis is bounded by the norm of the block space. -/
theorem abs_proj_blockVector_le_BAUGD {κ : Type*} [Fintype κ] (t : κ)
    (y : BlockSpace (fun _ : κ => ℝ²)) :
    |EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ : κ => ℝ²) t y)| ≤ ‖y‖ := by
  have h1 : ‖EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ : κ => ℝ²) t y)‖ ≤
      ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ := by
    have hn : ‖(EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      simpa using PiLp.norm_apply_le v (0 : Fin 2)
    calc _ ≤ ‖(EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)‖ *
          ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := one_mul _
  have h2 : ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ ≤ ‖y‖ := by
    have h3 := norm_blockVectorCLM_le (V := fun _ : κ => ℝ²) t
    calc _ ≤ ‖(blockVectorCLM (V := fun _ : κ => ℝ²) t : BlockSpace (fun _ : κ => ℝ²) →L[ℝ] ℝ²)‖
          * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = _ := one_mul _
  rw [← Real.norm_eq_abs]
  exact h1.trans h2

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- On the plateau `|η_j| < 8Δ`, `t ≤ 8Δ` of the chart ball the `edgeB` cutoff is one. -/
theorem edgeCutoff_eq_one_BAUGD (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 8 * Δ) (ht : S.edgeHeightRaw q ≤ 8 * Δ) :
    S.edgeCutoffW_BAUGP2 j q.val = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hmem : q.val ∈ S.edgeDomW_BAUGP2 j := ⟨q, mem_ball.mpr hd, rfl⟩
  have hη' : ‖S.edgeCoordW_BAUGP2 j q.val‖ < 8 * Δ := by
    rw [S.norm_edgeCoordW_val_BAUGP2]
    exact hη
  rw [S.edgeCutoffW_identity_BAUGP2 hΔ j q.val hmem hη', S.edgeHeightW_val_BAUGP2]
  have h0 : cfsRamp lc87EdgeTransition 8 9 (S.edgeHeightRaw q / Δ) = 0 := by
    refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
    rw [div_le_iff₀ hΔ]
    exact ht
  rw [h0, sub_zero]

/-- On the band `.3Δ ≤ t ≤ 8Δ` of the plateau the `E'` marker is one. -/
theorem edgeBMarker_eq_one_BAUGD (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤)
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 8 * Δ) (ht3 : 3 / 10 * Δ ≤ S.edgeHeightRaw q)
    (ht : S.edgeHeightRaw q ≤ 8 * Δ) :
    (letI := inducedMetricSpace S.completion.metric
     letI := S.completion.complete
     S.family.edgeBMarker_BAUGA q) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hζ := S.edgeCutoff_eq_one_BAUGD hΔ j q hd hη ht
  rw [S.edgeCutoffW_val_BAUGP2] at hζ
  have hsum : 1 ≤ S.family.edgeBSum_BAUGA q := by
    unfold LocalPacketsOnB.edgeBSum_BAUGA
    have h := Finset.single_le_sum
      (f := fun i : S.family.edgeB.finite_centres.toFinset => S.family.edgeB.cutoff_BAUGA i.1 q)
      (fun i _ => (S.family.edgeB.cutoff_mem_Icc_BAUGA hΔ i.1 q).1) (Finset.mem_univ j)
    rw [hζ] at h
    exact h
  have h3 : 3 / 10 ≤ S.family.edgeBHeight_BAUGA q / Δ := by
    rw [le_div_iff₀ hΔ]
    exact ht3
  have hH : cgpEdgeH (S.family.edgeBHeight_BAUGA q / Δ) = 1 := by
    rw [cgpEdgeH_eq_of_le h3]
    have h0 : cfsRamp lc87EdgeTransition 8 9 (S.family.edgeBHeight_BAUGA q / Δ) = 0 := by
      refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
      rw [div_le_iff₀ hΔ]
      exact ht
    rw [h0, sub_zero]
  unfold LocalPacketsOnB.edgeBMarker_BAUGA
  rw [hH, one_mul]
  exact cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hsum

/-- The `E'` height coordinate of `F_∂` at an interior point: `u_{E'}(F_∂ q) = z_{E'}(q) · F(q)`
(`F` the `edgeB` smoothing; BAUG-A's (WB)). -/
theorem heightCoord_boundaryOriginalMap_BAUGD (q : W.pieceInterior ⊤) :
    S.heightCoord_BIF (S.boundaryOriginalMap q.val) =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.edgeBMarker_BAUGA q * S.family.edgeB.smoothing q) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hE := S.boundaryOriginalMap_edgePrime_formula q
  have hrq := S.rho_pos q.val
  unfold heightCoord_BIF
  simp only [blockVectorCLM_apply, hE]
  change ((S.rho q.val * S.family.edgeBMarker_BAUGA q) • planeAxis (S.family.edgeBHeight_BAUGA q))
    0 = _
  rw [planeAxis_apply]
  unfold LocalPacketsOnB.edgeBHeight_BAUGA
  simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  field_simp

/-- The normalized `edgeB` coordinate functional `λ_j = ρ_j⁻¹ pr₀ ∘ u_j` of `H^∂` (so that
`λ_j(F_∂ q) = ζ_j(q) η_j(q)`). -/
def edgeRatio_BAUGD (j : S.EdgeIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  (S.rho j.1)⁻¹ • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).comp (S.edgeVector_BAUGD j)

/-- `|pr₀ u_j(z)| ≤ ‖z‖`. -/
theorem abs_proj_edgeVector_le_BAUGD (j : S.EdgeIdx_BAUGD)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    |EuclideanSpace.proj (0 : Fin 2) (S.edgeVector_BAUGD j z)| ≤ ‖z‖ := by
  have h := abs_proj_blockVector_le_BAUGD
    (κ := S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) (Sum.inl (.inr (.inr (.inl j)))) z
  unfold edgeVector_BAUGD
  exact h

/-- `|λ_j z| ≤ ‖z‖/ρ_j`. -/
theorem abs_edgeRatio_le_BAUGD (j : S.EdgeIdx_BAUGD)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    |S.edgeRatio_BAUGD j z| ≤ ‖z‖ / S.rho j.1 := by
  have hr := S.rho_pos j.1
  unfold edgeRatio_BAUGD
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul, div_le_div_iff_of_pos_right hr]
  exact S.abs_proj_edgeVector_le_BAUGD j z

/-- **The `edgeB` block of `F_∂`** at an interior point: `λ_j(F_∂ q) = ζ_j(q) η_j(q)`. -/
theorem edgeRatio_boundaryOriginalMap_BAUGD (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeRatio_BAUGD j (S.boundaryOriginalMap q.val) =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.edgeCutoffW_BAUGP2 j q.val * S.family.edgeB.coord_BAUGA j.1 q) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hr := S.rho_pos j.1
  have h := (S.edgeBlock_boundaryOriginalMap_BAUGP2 j q.val).1
  rw [S.edgeCoordW_val_BAUGP2] at h
  unfold edgeRatio_BAUGD
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change (S.rho j.1)⁻¹ * (S.edgeVector_BAUGD j (S.boundaryOriginalMap q.val)) 0 = _
  rw [h]
  simp only [PiLp.smul_apply, planeAxis_zero_BAUGD, smul_eq_mul]
  field_simp

/-- The `edgeB` smoothing `F` on `W°` (the stored one, never re-chosen). -/
def edgeSmoothing_BAUGD : W.pieceInterior ⊤ → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  S.family.edgeB.smoothing

theorem edgeHeightRaw_eq_BAUGD (z : W.pieceInterior ⊤) :
    S.edgeHeightRaw z = S.edgeSmoothing_BAUGD z / S.rho z.val :=
  rfl

/-- `u_{E'}(F_∂ q) ≤ F(q)` (the marker is at most one). -/
theorem heightCoord_boundaryOriginalMap_le_BAUGD (q : W.pieceInterior ⊤) :
    S.heightCoord_BIF (S.boundaryOriginalMap q.val) ≤ S.edgeSmoothing_BAUGD q := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  rw [S.heightCoord_boundaryOriginalMap_BAUGD]
  have h1 := (S.family.edgeBMarker_mem_Icc_BAUGA q).2
  have h2 := S.family.edgeB.smoothing_nonneg q
  exact mul_le_of_le_one_left h2 h1

/-- The open plateau region of the chart of the edge centre `j`: the chart ball with
`|η_j| < 8Δ` and `.3Δ < t < 8Δ`. -/
def edgeRegion_BAUGD (j : S.EdgeIdx_BAUGD) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  {z | z ∈ ball j.1 (100 * Δ * S.rho j.1) ∧ |S.edgeEta_BIF j.1 z| < 8 * Δ ∧
    3 / 10 * Δ < S.edgeHeightRaw z ∧ S.edgeHeightRaw z < 8 * Δ}

theorem isOpen_edgeRegion_BAUGD (j : S.EdgeIdx_BAUGD) : IsOpen (S.edgeRegion_BAUGD j) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hη : IsOpen (ball j.1 (100 * Δ * S.rho j.1) ∩
      S.family.edgeB.coord_BAUGA j.1 ⁻¹' Ioo (-(8 * Δ)) (8 * Δ)) :=
    (S.family.edgeB.contMDiffOn_coord_BAUGA hj).continuousOn.isOpen_inter_preimage isOpen_ball
      isOpen_Ioo
  have ht : IsOpen (S.edgeHeightRaw ⁻¹' Ioo (3 / 10 * Δ) (8 * Δ)) :=
    isOpen_Ioo.preimage S.family.continuous_edgeBHeight_BAUGA
  convert hη.inter ht using 1
  ext z
  simp only [edgeRegion_BAUGD, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt,
    S.edgeEta_eq_coord_BAUGP2 j z]
  tauto

/-- On the plateau region the `E'` coordinate of `F_∂` is the smoothing `F`. -/
theorem heightCoord_boundaryOriginalMap_eq_BAUGD (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD)
    {z : W.pieceInterior ⊤} (hz : z ∈ S.edgeRegion_BAUGD j) :
    S.heightCoord_BIF (S.boundaryOriginalMap z.val) = S.edgeSmoothing_BAUGD z := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨hd, hη, h3, h8⟩ := hz
  have hm := S.edgeBMarker_eq_one_BAUGD hΔ j z (mem_ball.mp hd) hη h3.le h8.le
  rw [S.heightCoord_boundaryOriginalMap_BAUGD, hm, one_mul]
  rfl

/-- On the plateau region the normalized `edgeB` coordinate of `F_∂` is `η_j`. -/
theorem edgeRatio_boundaryOriginalMap_eq_BAUGD (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD)
    {z : W.pieceInterior ⊤} (hz : z ∈ S.edgeRegion_BAUGD j) :
    S.edgeRatio_BAUGD j (S.boundaryOriginalMap z.val) = S.edgeEta_BIF j.1 z := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨hd, hη, h3, h8⟩ := hz
  have hζ := S.edgeCutoff_eq_one_BAUGD hΔ j z (mem_ball.mp hd) hη h8.le
  rw [S.edgeRatio_boundaryOriginalMap_BAUGD, hζ, one_mul, S.edgeEta_eq_coord_BAUGP2 j z]

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
