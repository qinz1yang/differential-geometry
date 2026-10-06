import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimModelFacts
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneFullMarker

/-!
# Pointwise clauses of the slim stage table on a boundary supply (lane B-PORT-SLIMb)

The clauses (PRE), (LOC), (COV) of `port_slim_interior_table_BAUGP` at ONE core witness, on the
actual slot `actualSlotsV2_BAUGD S` (`f(q) = π₂F_∂(q)`, `q ∈ W°`, distances `d_ĝ`). Closed twins:
`sgp05_full_marker` (PRE), `sgp06_localization` (LOC), `sgp06_coordinate_coverage` (COV), all in
`Fibration/ActualSlimRankTiers.lean`; the reference domain `D_a = B(a, 950000Δρ(a))` comes from the
slim support `≤ .91·10⁶Δρ` (`tsupport_cutoff_subset_BCNT`) and LFR20.2
(`SlimCentreOn.dist_lt_of_abs_coord_le_ZERO_BAUGP`).

* `SlimCentreOn.Icc_subset_image_coord_BPS` (twin `SlimCentre.Icc_subset_image_coord`);
* `slimBlock_stageTwo_BPS`, `stageDomain_two_BPS`;
* `slim_preimage_core_BPS` (PRE), `slim_localization_BPS` (LOC), `slim_coverage_BPS` (COV).
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

section SlimOn

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- FC27 (slim coverage) on a regional slim centre: `[-905·10³Δ, 905·10³Δ] ⊆ η_j(B(j, 10⁶Δρ(j)))`. -/
theorem SlimCentreOn.Icc_subset_image_coord_BPS {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) :
    Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) ⊆ c.coord_BCG2 '' ball j (10 ^ 6 * Δ * ρ j) := by
  have hball : ∀ x, (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ → x ∈ ball j (10 ^ 6 * Δ * ρ j) := by
    intro x hx
    rw [inv_mul_lt_iff₀ (hρ j)] at hx
    rw [mem_ball]
    linarith
  intro t ht
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  obtain ⟨x, hx, hxt⟩ := P.surjective ht
  exact ⟨x, hball x hx, hxt⟩

end SlimOn

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The slim reference domain constant: `C_2 = 950000Δ`. -/
theorem stageDomain_two_BPS (Δ : ℝ) : stageDomain_BIF Δ 2 = 950000 * Δ :=
  rfl

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- The whole slim block `j` of `f(q) = π₂F_∂(q)`: `(ρ_jζ_j(q) η_j(q), ρ_jζ_j(q))`. -/
theorem slimBlock_stageTwo_BPS (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤) :
    (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) (Sum.inl (.inr (.inl j))) =
      WithLp.toLp 2 ((S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.slim.cutoff_BCNT j.1 q)) • planeAxis (S.slimEta_BIF j.1 q),
        S.rho j.1 * (letI := inducedMetricSpace S.completion.metric
          letI := S.completion.complete
          S.family.slim.cutoff_BCNT j.1 q)) := by
  rw [← S.slimVector_stageTwo_BPS j q, ← S.slimMarker_stageTwo_BPS j q]
  rfl

/-- The slim reference coordinate of a centre is its chart coordinate (`j` given as an index). -/
theorem slimEta_abs_le_ZERO_BPS (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| ≤ 905 * 10 ^ 3 * Δ) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 < 910000 * Δ * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.slimEta_eq_coord_BAUGP2] at hη
  have hd' : q ∈ ball j.1 (10 ^ 6 * Δ * S.rho j.1) := by
    rw [mem_ball]
    have h : (10 : ℝ) ^ 6 * Δ * S.rho j.1 = 1000000 * Δ * S.rho j.1 := by norm_num
    rw [h]
    exact hd
  have h := SlimCentreOn.dist_lt_of_abs_coord_le_ZERO_BAUGP (S.family.slim.centre j.1 hj) hd' hη
  have he : 91 / 100 * (10 ^ 6 * Δ) * S.rho j.1 = 910000 * Δ * S.rho j.1 := by ring
  rw [he] at h
  exact h

/-- **(PRE) at one core witness** (closed `sgp05_full_marker`): a preimage `q` of `f(p)`, `p` in the
threshold-`8` core of the slim chart `j`, has full marker `ζ_j(q) = 1`, the same coordinate
`η_j(q) = η_j(p)`, lies in `B(j, .91·10⁶Δρ_j)`, hence in the threshold-`8` core and in `D_j`. -/
theorem slim_preimage_core_BPS (hΔ : 0 < Δ) (j : S.SlimIdx_BAUGD) {p q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 p| ≤ 8 * (100000 * Δ))
    (hpq : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) =
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val)) :
    letI := inducedMetricSpace S.completion.metric
    ((dist q j.1 < 1000000 * Δ * S.rho j.1 ∧ |S.slimEta_BIF j.1 q| ≤ 8 * (100000 * Δ)) ∧
      dist q j.1 < stageDomain_BIF Δ 2 * S.rho j.1 ∧ S.slimEta_BIF j.1 q = S.slimEta_BIF j.1 p) ∧
      (letI := S.completion.complete; S.family.slim.cutoff_BCNT j.1 q) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hrj := S.rho_pos j.1
  have hcp := S.slim_cutoff_eq_one_BPS j hd hη
  have hm := congrArg (S.slimMarker_BAUGD j) hpq
  rw [S.slimMarker_stageTwo_BPS j q, S.slimMarker_stageTwo_BPS j p, hcp, mul_one] at hm
  have hcq : S.family.slim.cutoff_BCNT j.1 q = 1 := by
    have h := mul_left_cancel₀ hrj.ne' (hm.trans (mul_one _).symm)
    exact h
  have hv := congrArg (S.slimVector_BAUGD j) hpq
  rw [S.slimVector_stageTwo_BPS j q, S.slimVector_stageTwo_BPS j p, hcp, hcq, mul_one] at hv
  have hηq : S.slimEta_BIF j.1 q = S.slimEta_BIF j.1 p :=
    planeAxis_injective_SGP3 (smul_right_injective _ hrj.ne' hv)
  have hdq := S.slim_dist_le_of_cutoff_ne_zero_BPS j (q := q) (by rw [hcq]; exact one_ne_zero)
  have h1 : 910000 * Δ * S.rho j.1 < 950000 * Δ * S.rho j.1 := by
    have := mul_pos hΔ hrj
    nlinarith
  have h2 : 950000 * Δ * S.rho j.1 < 1000000 * Δ * S.rho j.1 := by
    have := mul_pos hΔ hrj
    nlinarith
  refine ⟨⟨⟨by linarith, by rw [hηq]; exact hη⟩, ?_, hηq⟩, hcq⟩
  rw [stageDomain_two_BPS]
  linarith

/-- **(LOC) at one core witness** (closed `sgp06_localization`): if `p` is in the threshold-`7` core of
the slim chart `j` and `‖pr_int(f(q) − f(p))‖ ≤ Rρ_j` with `0 ≤ R < 1/100`, then `q` is in the
threshold-`8` core of `j` and in `D_j`. -/
theorem slim_localization_BPS (hΔ1 : 1 ≤ Δ) (j : S.SlimIdx_BAUGD) {p q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 p| ≤ 7 * (100000 * Δ)) {R : ℝ} (hR : R < 1 / 100)
    (hpq : ‖augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) -
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))‖ ≤ R * S.rho j.1) :
    letI := inducedMetricSpace S.completion.metric
    (dist q j.1 < 1000000 * Δ * S.rho j.1 ∧ |S.slimEta_BIF j.1 q| ≤ 8 * (100000 * Δ)) ∧
      dist q j.1 < stageDomain_BIF Δ 2 * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have hrj := S.rho_pos j.1
  have hcp := S.slim_cutoff_eq_one_BPS j hd (by linarith)
  have hblk := norm_inl_sub_le_augIntProj_BPS
    ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val))
    ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val)) (.inr (.inl j))
  rw [S.slimBlock_stageTwo_BPS j q, S.slimBlock_stageTwo_BPS j p, hcp, ← dist_eq_norm,
    dist_block_scale_GAF hrj, one_smul] at hblk
  have hd1 : dist (WithLp.toLp 2 (S.family.slim.cutoff_BCNT j.1 q • planeAxis (S.slimEta_BIF j.1 q),
      S.family.slim.cutoff_BCNT j.1 q)) (WithLp.toLp 2 (planeAxis (S.slimEta_BIF j.1 p), (1 : ℝ))) <
        1 / 100 := by
    have h := hblk.trans hpq
    have h' : S.rho j.1 * dist (WithLp.toLp 2 (S.family.slim.cutoff_BCNT j.1 q •
        planeAxis (S.slimEta_BIF j.1 q), S.family.slim.cutoff_BCNT j.1 q))
        (WithLp.toLp 2 (planeAxis (S.slimEta_BIF j.1 p), (1 : ℝ))) < S.rho j.1 * (1 / 100) := by
      nlinarith
    exact lt_of_mul_lt_mul_left h' hrj.le
  have hA : ‖planeAxis (S.slimEta_BIF j.1 p)‖ ≤ 7 * (100000 * Δ) := by
    rw [norm_planeAxis]; exact hη
  obtain ⟨hζ, hv⟩ := norm_coordinate_sub_lt_of_block_dist (by norm_num) (by norm_num) hA hd1
  rw [← map_sub, norm_planeAxis] at hv
  have hcq : S.family.slim.cutoff_BCNT j.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdq := S.slim_dist_le_of_cutoff_ne_zero_BPS j hcq
  have hηq : |S.slimEta_BIF j.1 q| ≤ 8 * (100000 * Δ) := by
    have h1 := abs_sub_abs_le_abs_sub (S.slimEta_BIF j.1 q) (S.slimEta_BIF j.1 p)
    have h2 : (1 + 7 * (100000 * Δ)) * (1 / 100) / (1 - 1 / 100) ≤ 100000 * Δ := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  have h1 : 910000 * Δ * S.rho j.1 < 950000 * Δ * S.rho j.1 := by
    have := mul_pos hΔ hrj
    nlinarith
  have h2 : 950000 * Δ * S.rho j.1 < 1000000 * Δ * S.rho j.1 := by
    have := mul_pos hΔ hrj
    nlinarith
  refine ⟨⟨by linarith, hηq⟩, ?_⟩
  rw [stageDomain_two_BPS]
  linarith

/-- **(COV) at one core witness** (closed `sgp06_coordinate_coverage`): for `p` in the threshold-`7`
core of the slim chart `j` and `|u − η_j(p)| ≤ 1/100` there is `q` in the threshold-`8` core of `j`
and in `D_j` with `η_j(q) = u` and `f(q) ∈ S̃₂`. -/
theorem slim_coverage_BPS (hΔ1 : 1 ≤ Δ) (j : S.SlimIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hη : |S.slimEta_BIF j.1 p| ≤ 7 * (100000 * Δ)) {u : ℝ}
    (hu : |u - S.slimEta_BIF j.1 p| ≤ 1 / 100) :
    letI := inducedMetricSpace S.completion.metric
    ∃ q : W.pieceInterior ⊤,
      (dist q j.1 < 1000000 * Δ * S.rho j.1 ∧ |S.slimEta_BIF j.1 q| ≤ 8 * (100000 * Δ)) ∧
      dist q j.1 < stageDomain_BIF Δ 2 * S.rho j.1 ∧ S.slimEta_BIF j.1 q = u ∧
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have hrj := S.rho_pos j.1
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hu8 : |u| ≤ 8 * (100000 * Δ) := by
    have := abs_sub_abs_le_abs_sub u (S.slimEta_BIF j.1 p)
    nlinarith
  have hmem : u ∈ Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) := by
    rw [abs_le] at hu8
    constructor <;> nlinarith
  obtain ⟨q, hq, hqu⟩ := (S.family.slim.centre j.1 hj).Icc_subset_image_coord_BPS hmem
  have hqη : S.slimEta_BIF j.1 q = u := by rw [S.slimEta_eq_coord_BAUGP2]; exact hqu
  have hqd : dist q j.1 < 1000000 * Δ * S.rho j.1 := by
    rw [mem_ball] at hq
    have h : (10 : ℝ) ^ 6 * Δ * S.rho j.1 = 1000000 * Δ * S.rho j.1 := by norm_num
    rw [h] at hq
    exact hq
  have hq91 := S.slimEta_abs_le_ZERO_BPS j hqd (by rw [hqη]; linarith)
  have hηq : |S.slimEta_BIF j.1 q| ≤ 8 * (100000 * Δ) := by rw [hqη]; exact hu8
  have h1 : 910000 * Δ * S.rho j.1 < 950000 * Δ * S.rho j.1 := by
    have := mul_pos hΔ hrj
    nlinarith
  refine ⟨q, ⟨hqd, hηq⟩, ?_, hqη, S.stageProj_mem_stageCloudEnlarged_two_BPS j hqd hηq⟩
  rw [stageDomain_two_BPS]
  linarith

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
