import DifferentialGeometry.Geometry.Fibration.ActualStageChainWitness
import DifferentialGeometry.Geometry.Fibration.GenericLaterTransport

/-!
# GAF02 BASES: the marked patches of the chain, (MW) on them, threshold-5 membership

Blueprint `master207B.tex`, CGP05 (B:4084), CGP07 (B:4176), CGP08 (B:4259: "For `p ∈ U_j` … the
cumulative error puts `f_j(p)` inside `V_i⁰` with strict slack"), FC33 (B:2873: `U_j` = the
original thresholds `5`, `5Δ` (with `η_{E'} = t < 5Δ`), `5·10⁵Δ`); external draft 59 §4, second and
seventh steps (D59-5); review 66 §5.4 (D66-7).

Indexed by ONE chain `C`. The marked patches live on the slot's native zero set
`(C.slot st).zeroSet` (empty for an inactive slot), with the marker condition `v_i > .9R_i` ONLY
(no exact GAF05 marker) and the retained coordinate of the actual block: the vector `u_i ∈ ℝ²` on
circles, the ONE-dimensional axis coordinate `axisCoordCLM_BAS ∘ u_i` on edges and slims.

* `Gaf02Chain.circlePatch_BAS j`, `Gaf02Chain.edgePatch_BAS j`, `Gaf02Chain.slimPatch_BAS j`
  (`V_j⁰`, thresholds `5.5`, `5.5Δ`, `5.5·10⁵Δ`).
* `gafStageDomain5_BAS st`: FC33's EXACT original threshold-5 domains `U_st`
  (`gafStageDomain5_subset_plateau_BAS`: `U_st ⊆ B⁶_st`).
* (MW) on the patches of the chain (inactive slot: vacuous): `Gaf02Chain.circlePatch_witness_BAS`,
  `Gaf02Chain.edgePatch_witness_BAS`, `Gaf02Chain.slimPatch_witness_BAS`.
* Threshold-5 membership with strict slack (consumer of PLAT, CORE's strict errors and the original
  full markers): `Gaf02Chain.circle_mem_patch_of_domain5_BAS`, `edge_mem_patch_of_domain5_BAS`,
  `slim_mem_patch_of_domain5_BAS`: for `p ∈ U_st` in chart `j`, `f_st(p) ∈ V_j⁰`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- FC33's EXACT original threshold-5 domains `U_st` (circle `‖η_j‖ < 5`; edge `|η_j| < 5Δ` and
`t < 5Δ`; slim `|η_j| < 5·10⁵Δ`, each on the chart's smooth domain). -/
def gafStageDomain5_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) (st : Fin 3) : Set X :=
  ![{p | ∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
        p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5},
    {p | ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 5 * Δ ∧ cgpHeight P.toLocalChartFamily p < 5 * Δ},
    {p | ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 5 * (10 ^ 5 * Δ)}]
    st

/-- `U_st ⊆ B⁶_st` (for `Δ ≥ 0`). -/
theorem gafStageDomain5_subset_plateau_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ
    b s b' s' ε γc βc Lmax τ γ δ εr e T V) (hΔ : 0 ≤ Δ) (st : Fin 3) :
    gafStageDomain5_BAS P st ⊆ gafStagePlateau_BAS P st := by
  intro p hp
  fin_cases st
  · obtain ⟨j, hj, hη⟩ := hp
    exact ⟨j, hj, by linarith⟩
  · obtain ⟨j, hj, hη, ht⟩ := hp
    exact ⟨j, hj, by linarith, by linarith⟩
  · obtain ⟨j, hj, hη⟩ := hp
    exact ⟨j, hj, by linarith⟩

/-- `π_{Q₁} = id` (`Q₁ = H`). -/
theorem gafStageQ_zero_starProjection_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b
    s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y := by
  classical
  rw [gafStageQ_starProjection]
  refine PiLp.ext fun t => ?_
  have ht : t ∈ gafStageTags P.toLocalChartFamily P.zero 0 := Finset.mem_univ t
  simp only [blockRestrict_apply, ht, ↓reduceIte]

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The circle marked patch `V_j⁰ = {w ∈ Z₁ | v_j(w) > .9R_j, ‖u_j(w)‖ < 5.5R_j}` of the chain. -/
def circlePatch_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  markedPatch_BPRE (C.slot 0).zeroSet (gafCircleVector P j) (gafCircleMarker P j) (ρ j.1) 1

/-- The edge marked patch `V_j⁰ = {w ∈ Z₂ | v_j(w) > .9R_j, |u_j(w)| < 5.5ΔR_j}` (axis coordinate). -/
def edgePatch_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (j : P.edge.finite_centres.toFinset) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  markedPatch_BPRE (C.slot 1).zeroSet (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily
    P.zero j)) (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ

/-- The slim marked patch `V_j⁰ = {w ∈ Z₃ | v_j(w) > .9R_j, |u_j(w)| < 5.5·10⁵ΔR_j}` (axis
coordinate). -/
def slimPatch_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (j : P.slim.finite_centres.toFinset) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  markedPatch_BPRE (C.slot 2).zeroSet (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily
    P.zero j)) (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ)

/-- **(MW) on the circle patches of the chain** (CGP05 with full marker; vacuous for an inactive
slot). -/
theorem circlePatch_witness_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∀ w ∈ C.circlePatch_BAS j, ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 0,
      q ∈ ball j.1 (200 * ρ j.1) ∧ P.circle.cutoff j.1 q = 1 ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) q‖ < 31 / 5 ∧
      3 / 4 * ρ j.1 ≤ ρ q ∧ ρ q ≤ 5 / 4 * ρ j.1 ∧
      gafCircleVector P j (cgpGlobalMap P.toLocalChartFamily P.zero q) =
        ρ j.1 • cgpCoord P.toLocalChartFamily P.zero (.inl j) q ∧
      gafCircleMarker P j (cgpGlobalMap P.toLocalChartFamily P.zero q) = ρ j.1 ∧
      ‖w - cgpGlobalMap P.toLocalChartFamily P.zero q‖ < 25 / 12 * Ξ 0 * S 0 * ρ j.1 := by
  intro w hw
  unfold circlePatch_BAS at hw
  cases hO : C.slot 0 with
  | active O =>
    rw [hO, Gaf02StageSlot.zeroSet_active] at hw
    exact C.cgp05_circle_full_BAS O j w hw
  | inactive h =>
    rw [hO] at hw
    exact absurd hw.1 (Set.notMem_empty w)

/-- **(MW) on the edge patches of the chain** (CGP05 with full marker and enlarged carrier
`t(q) ≤ 8Δ`; vacuous for an inactive slot). -/
theorem edgePatch_witness_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) :
    ∀ w ∈ C.edgePatch_BAS j, ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 1,
      q ∈ ball j.1 (100 * Δ * ρ j.1) ∧ cgpHeight P.toLocalChartFamily q ≤ 8 * Δ ∧
      P.edge.cutoff j.1 q = 1 ∧ |P.edge.coord j.1 q| < 31 / 5 * Δ ∧
      3 / 4 * ρ j.1 ≤ ρ q ∧ ρ q ≤ 5 / 4 * ρ j.1 ∧
      axisCoordCLM_BAS (gafEdgeVector P.toLocalChartFamily P.zero j
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q))) = ρ j.1 * P.edge.coord j.1 q ∧
      gafEdgeMarker P.toLocalChartFamily P.zero j
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)) = ρ j.1 ∧
      ‖w - (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ < 25 / 12 * Ξ 1 * S 1 * ρ j.1 := by
  intro w hw
  unfold edgePatch_BAS at hw
  cases hO : C.slot 1 with
  | active O =>
    rw [hO, Gaf02StageSlot.zeroSet_active] at hw
    exact C.cgp05_edge_full_BAS O j w hw
  | inactive h =>
    rw [hO] at hw
    exact absurd hw.1 (Set.notMem_empty w)

/-- **(MW) on the slim patches of the chain** (CGP05 with full marker; vacuous for an inactive
slot). -/
theorem slimPatch_witness_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) :
    ∀ w ∈ C.slimPatch_BAS j, ∃ q ∈ gafStageEnlargement P.toLocalChartFamily P.zero 2,
      q ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧ P.slim.cutoff j.1 q = 1 ∧
      |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q| < 31 / 5 * (10 ^ 5 * Δ) ∧
      3 / 4 * ρ j.1 ≤ ρ q ∧ ρ q ≤ 5 / 4 * ρ j.1 ∧
      axisCoordCLM_BAS (gafSlimVector P.toLocalChartFamily P.zero j
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q))) =
        ρ j.1 * (P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q ∧
      gafSlimMarker P.toLocalChartFamily P.zero j
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)) = ρ j.1 ∧
      ‖w - (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q)‖ < 25 / 12 * Ξ 2 * S 2 * ρ j.1 := by
  intro w hw
  unfold slimPatch_BAS at hw
  cases hO : C.slot 2 with
  | active O =>
    rw [hO, Gaf02StageSlot.zeroSet_active] at hw
    exact C.cgp05_slim_full_BAS O j w hw
  | inactive h =>
    rw [hO] at hw
    exact absurd hw.1 (Set.notMem_empty w)

/-- The stage error through `π_st`: `‖f_st(p) − π_st𝓔⁰(p)‖ < c_st ρ(p)`. -/
theorem stageMap_error_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) (p : X) :
    ‖C.stageMap_BAS st p - (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ < c st * ρ p := by
  have herr : ‖C.stageOut_BAS st p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c st * ρ p := by
    have h := C.stage_error_lt
    fin_cases st
    · exact h.1 p
    · exact h.2.1 p
    · exact h.2.2 p
  rw [stageMap_BAS, ← map_sub]
  exact (Submodule.norm_starProjection_apply_le _ _).trans_lt herr

/-- `c_st ≤ 1/512` at every stage (CHOICE). -/
theorem c_le_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) : c st ≤ 1 / 512 := by
  obtain ⟨-, -, h0, -, -, -, -, h1, -, -, -, -, h2, -⟩ := C.numbers
  fin_cases st
  · exact h0
  · exact h1
  · exact h2

/-- `0 < c_st` (from `(5/3)Ξ₁Σ₁ < c₁` and the increasing budgets). -/
theorem c_pos_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) : 0 < c st := by
  obtain ⟨hnum, hv₁, -, -, -, -, hv₂, -, -, -, -, hv₃, -, -⟩ := C.numbers
  have hp : ∀ j, 0 < 5 / 3 * Ξ j * S j := fun j => by
    have := (hnum j).1
    have := (hnum j).2.1
    positivity
  have hc0 : 0 < c 0 := (hp 0).trans hv₁
  have hΞ1 := (hnum 1).1
  have hc1 : 0 < c 1 := by nlinarith [hp 1]
  have hΞ2 := (hnum 2).1
  have h1 : 0 < (1 + Ξ 2) * c 1 := mul_pos (by linarith) hc1
  have hc2 : 0 < c 2 := by linarith [hp 2]
  fin_cases st
  · exact hc0
  · exact hc1
  · exact hc2

/-- **Threshold-5 membership, circle stage**: a point `p` of FC33's `U₁` in chart `j`
(`p ∈ B(c_j, 200ρ_j)`, `‖η_j(p)‖ < 5`) has `f₁(p) ∈ V_j⁰` (PLAT, the full original marker, CORE's
strict error `c₁ ≤ 1/512`). -/
theorem circle_mem_patch_of_domain5_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5) :
    C.stageMap_BAS 0 p ∈ C.circlePatch_BAS j := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hj : j.1 ∈ P.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hd : (ρ j.1)⁻¹ * dist p j.1 < 200 := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j.1) hp
  have hcut : P.circle.cutoff j.1 p = 1 :=
    P.circle.cutoff_eq_one j.1 hj p hd (hη.le.trans (by norm_num))
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inl j) p = 1 := hcut
  have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS (.inl j) p
    (by rw [hcut']; exact one_ne_zero)
  have hs2 : ρ p ≤ 5 * ρ j.1 / 4 := hs.2
  have hb := cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero (.inl j) p
  rw [hcut', mul_one] at hb
  have hZ := C.plat_mem_zeroSet_BAS (st := 0) (p := p) ⟨j, hp, by linarith⟩
  have herr := C.stageMap_error_BAS 0 p
  rw [gafStageQ_zero_starProjection_BAS] at herr
  have hc := C.c_le_BAS 0
  have hc0 := C.c_pos_BAS 0
  exact mem_markedPatch_of_full_marker_BPRE _ (gafCircleVector P j)
    (norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _)
    (gafCircleMarker P j) (norm_blockMarkerCLM_le (V := fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²) _)
    (C.stageMap_BAS 0) (cgpGlobalMap P.toLocalChartFamily P.zero)
    (cgpCoord P.toLocalChartFamily P.zero (.inl j)) ρ (hρ j.1) hc0.le hZ hb.1 hb.2
    (by linarith) herr.le (by linarith) (by linarith) (by linarith)

/-- **Threshold-5 membership, edge stage**: a point `p` of FC33's `U₂` in chart `j`
(`p ∈ B(c_j, 100Δρ_j)`, `|η_j(p)| < 5Δ`, `t(p) < 5Δ`) has `f₂(p) ∈ V_j⁰`. -/
theorem edge_mem_patch_of_domain5_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) {p : X} (hp : p ∈ ball j.1 (100 * Δ * ρ j.1))
    (hη : |P.edge.coord j.1 p| < 5 * Δ) (ht : cgpHeight P.toLocalChartFamily p < 5 * Δ) :
    C.stageMap_BAS 1 p ∈ C.edgePatch_BAS j := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hcut : P.edge.cutoff j.1 p = 1 :=
    P.edge.cutoff_eq_one_of_le hΔ0 hj hp (by linarith) (by
      have : cgpHeight P.toLocalChartFamily p = P.edge.smoothing p / ρ p := rfl
      linarith)
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inr j)) p = 1 := hcut
  have htag : cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈
      gafStageTags P.toLocalChartFamily P.zero 1 := by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j)) ∈ cgpQ2Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS (.inr (.inr j)) p
    (by rw [hcut']; exact one_ne_zero)
  have hs2 : ρ p ≤ 5 * ρ j.1 / 4 := hs.2
  have hb := markerBlock_projMap_BAS P.toLocalChartFamily P.zero htag axisCoordCLM_BAS p
  rw [hcut', mul_one] at hb
  have hZ := C.plat_mem_zeroSet_BAS (st := 1) (p := p) ⟨j, hp, by linarith, by linarith⟩
  have herr := C.stageMap_error_BAS 1 p
  have hc := C.c_le_BAS 1
  have hc0 := C.c_pos_BAS 1
  have hb1 : (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p)) = ρ j.1 • P.edge.coord j.1 p := by
    calc _ = ρ j.1 • axisCoordCLM_BAS (cgpCoord P.toLocalChartFamily P.zero
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr j))) p) := hb.1
      _ = _ := by
        change ρ j.1 • axisCoordCLM_BAS (planeAxis (P.edge.coord j.1 p)) = _
        rw [axisCoordCLM_planeAxis_BAS]
  have hu : ‖axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)‖ ≤ 1 := by
    have h1 := norm_axisCoordCLM_le_BAS
    have h2 := norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero)
    have h3 := norm_nonneg (gafEdgeVector P.toLocalChartFamily P.zero j)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      change ‖axisCoordCLM_BAS‖ * ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero)‖ ≤ 1
      nlinarith [norm_nonneg axisCoordCLM_BAS])
  exact mem_markedPatch_of_full_marker_BPRE _ _ hu (gafEdgeMarker P.toLocalChartFamily P.zero j)
    (norm_blockMarkerCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _)
    (C.stageMap_BAS 1) (fun q => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q))
    (fun q => P.edge.coord j.1 q) ρ (hρ j.1) hc0.le hZ hb1 hb.2
    (by rw [Real.norm_eq_abs]; exact hη) herr.le (by linarith) (by linarith) (by linarith)

/-- **Threshold-5 membership, slim stage**: a point `p` of FC33's `U₃` in chart `j`
(`p ∈ B(c_j, 10⁶Δρ_j)`, `|η_j(p)| < 5·10⁵Δ`) has `f₃(p) ∈ V_j⁰`. -/
theorem slim_mem_patch_of_domain5_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) {p : X} (hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 5 * (10 ^ 5 * Δ)) :
    C.stageMap_BAS 2 p ∈ C.slimPatch_BAS j := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hj : j.1 ∈ P.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hp' : p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) := by
    norm_num
    exact hp
  have hcut : P.slim.cutoff j.1 p = 1 := by
    unfold SlimFamily.cutoff
    rw [dite_eq_left hj]
    exact (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le hp' (by linarith)
  have hcut' : cgpMarkerCutoff P.toLocalChartFamily (.inr (.inl j)) p = 1 := hcut
  have htag : cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈
      gafStageTags P.toLocalChartFamily P.zero 2 := by
    change cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j)) ∈ cgpQ3Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hs := cgpMarkerCutoff_scale_lip_GAF4 P.toLocalChartFamily hΔ hΛ C.small_BAS (.inr (.inl j)) p
    (by rw [hcut']; exact one_ne_zero)
  have hs2 : ρ p ≤ 5 * ρ j.1 / 4 := hs.2
  have hb := markerBlock_projMap_BAS P.toLocalChartFamily P.zero htag axisCoordCLM_BAS p
  rw [hcut', mul_one] at hb
  have hZ := C.plat_mem_zeroSet_BAS (st := 2) (p := p) ⟨j, hp, by linarith⟩
  have herr := C.stageMap_error_BAS 2 p
  have hc := C.c_le_BAS 2
  have hc0 := C.c_pos_BAS 2
  have hb1 : (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p)) =
        ρ j.1 • (P.slim.centre j.1 hj).coord p := by
    calc _ = ρ j.1 • axisCoordCLM_BAS (cgpCoord P.toLocalChartFamily P.zero
          (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl j))) p) := hb.1
      _ = _ := by
        change ρ j.1 • axisCoordCLM_BAS (planeAxis ((P.slim.centre j.1 hj).coord p)) = _
        rw [axisCoordCLM_planeAxis_BAS]
  have hu : ‖axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)‖ ≤ 1 := by
    have h1 := norm_axisCoordCLM_le_BAS
    have h2 := norm_blockVectorCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      change ‖axisCoordCLM_BAS‖ * ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²) (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero)‖ ≤ 1
      nlinarith [norm_nonneg axisCoordCLM_BAS, norm_nonneg (blockVectorCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero))])
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by linarith
  exact mem_markedPatch_of_full_marker_BPRE _ _ hu (gafSlimMarker P.toLocalChartFamily P.zero j)
    (norm_blockMarkerCLM_le (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _)
    (C.stageMap_BAS 2) (fun q => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero q))
    (fun q => (P.slim.centre j.1 hj).coord q) ρ (hρ j.1) hc0.le hZ hb1 hb.2
    (by rw [Real.norm_eq_abs]; exact hη) herr.le (by linarith) (by linarith) (by linarith)

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
