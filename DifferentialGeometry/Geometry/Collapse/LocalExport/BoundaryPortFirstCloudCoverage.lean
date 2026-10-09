import DifferentialGeometry.Geometry.Fibration.ActualFirstCloudCoverage
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleGram
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPacketsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPlaneCoherence
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTags
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTagsScalar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFullMarkerContributors
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeetingTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualFirstCloudCoverage (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstCloudCoverage.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA8C_BAUGP : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Generic

end Generic

section Chart

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **LFR07's coverage in physical units**: every `‖u‖ < 9` is `η_i(q)` for a point `q` of the chart
domain `B(i, 200ρ(i))` (the trivial circle bundle of the chart over `B(0, 9)`). -/
theorem circle_coord_cover_KA8_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) {i : X}
    (hi : i ∈ L.circle.centres) {u : ℝ²} (hu : ‖u‖ < 9) :
    ∃ q ∈ ball i (200 * ρ i), cgpCircleCoord_BAUGP L i hi q = u := by
  have hri := hρ i
  have hcen := L.circle.chart_center i hi
  let c := L.circle.chart i hi
  let mR : MetricSpace X := mX.rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
  have hc : c.center = i := hcen
  obtain ⟨sec, -, hs⟩ := c.exists_section_KC (R := 9) (by norm_num) (by norm_num)
  obtain ⟨hco, hb⟩ := hs ⟨u, mem_ball_zero_iff.mpr hu⟩
  rw [hc] at hb
  have hd : (ρ i)⁻¹ * @dist X mX.toDist (sec ⟨u, mem_ball_zero_iff.mpr hu⟩) i < 200 := hb
  rw [inv_mul_lt_iff₀ hri] at hd
  refine ⟨sec ⟨u, mem_ball_zero_iff.mpr hu⟩, ?_, hco⟩
  change @dist X mX.toDist _ i < 200 * ρ i
  linarith

end Chart

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP06_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP06_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP06_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP06, localization (FC03 on `F`).** If `p ∈ B(i, 200ρ(i))` has `‖η_i(p)‖ ≤ 7` and
`|F(q) − F(p)| ≤ Rρ(i)` with `0 ≤ R < 1/100`, then `q ∈ B(i, 200ρ(i))`, the circle cutoff of `i` is
`1` at `q` (full marker), `‖η_i(q) − η_i(p)‖ < 1/10` and `‖η_i(q)‖ < 8`. -/
theorem tcp06_localization_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    {p q : X} (hp : p ∈ ball i (200 * ρ i))
    (hη : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 7) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < 1 / 100)
    (hpq : dist (cgpGlobalMap_BAUGP P P.zero q)
      (cgpGlobalMap_BAUGP P P.zero p) ≤ R * ρ i) :
    q ∈ ball i (200 * ρ i) ∧ P.circle.cutoff i q = 1 ∧
      ‖cgpCircleCoord_BAUGP P i hi q - cgpCircleCoord_BAUGP P i hi p‖ <
        1 / 10 ∧ ‖cgpCircleCoord_BAUGP P i hi q‖ < 8 := by
  obtain ⟨j, hjmem⟩ := j
  change j = i at hji
  subst hji
  have hrj := hρ j
  have hcutp : P.circle.cutoff j p = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF_BAUGP P P.zero
      ⟨j, hjmem⟩ hp (le_trans hη (by norm_num))
  obtain ⟨e', he'def⟩ : ∃ e', e' = (R + 1 / 100) / 2 := ⟨_, rfl⟩
  have he'0 : 0 < e' := by rw [he'def]; linarith
  have he'R : R < e' := by rw [he'def]; linarith
  have he'1 : e' < 1 / 100 := by rw [he'def]; linarith
  have hblk : dist (cgpGlobalMap_BAUGP P P.zero q (.inl ⟨j, hjmem⟩))
      (cgpGlobalMap_BAUGP P P.zero p (.inl ⟨j, hjmem⟩)) ≤ R * ρ j :=
    (PiLp.dist_apply_le _ _ _).trans hpq
  have hblk' : dist (WithLp.toLp 2 ((ρ j * P.circle.cutoff j q) •
      cgpCircleCoord_BAUGP P j hi q, ρ j * P.circle.cutoff j q))
      (WithLp.toLp 2 ((ρ j * 1) • cgpCircleCoord_BAUGP P j hi p, ρ j * 1)) <
        ρ j * e' := by
    rw [← hcutp]
    exact lt_of_le_of_lt hblk ((mul_lt_mul_of_pos_right he'R hrj).trans_eq (mul_comm _ _))
  rw [dist_block_scale_GAF hrj, one_smul] at hblk'
  have hd : dist (WithLp.toLp 2 (P.circle.cutoff j q • cgpCircleCoord_BAUGP P j hi q,
      P.circle.cutoff j q))
      (WithLp.toLp 2 (cgpCircleCoord_BAUGP P j hi p, (1 : ℝ))) < e' :=
    lt_of_mul_lt_mul_left hblk' hrj.le
  obtain ⟨hζ, hv⟩ := norm_coordinate_sub_lt_of_block_dist he'0 (by linarith) hη hd
  have hloc := marker_localization_lt he'0.le he'1 le_rfl (show (7 : ℝ) ≤ 7 * 1 by norm_num)
  have hv' : ‖cgpCircleCoord_BAUGP P j hi q -
      cgpCircleCoord_BAUGP P j hi p‖ < 1 / 10 := hv.trans hloc
  have hcutq_ne : P.circle.cutoff j q ≠ 0 := by
    intro h
    rw [h] at hζ
    linarith
  have hdom : q ∈ ball j (200 * ρ j) := by
    have h1 : (ρ j)⁻¹ * dist q j < 200 := (P.circle.coord_lt_of_cutoff_ne_zero j hi q hcutq_ne).1
    rw [inv_mul_lt_iff₀ hrj] at h1
    rw [mem_ball]
    linarith
  have hqη : ‖cgpCircleCoord_BAUGP P j hi q‖ < 8 := by
    have := norm_sub_norm_le (cgpCircleCoord_BAUGP P j hi q)
      (cgpCircleCoord_BAUGP P j hi p)
    linarith
  refine ⟨hdom, ?_, hv', hqη⟩
  exact circle_cutoff_eq_one_of_coord_le_GAF_BAUGP P P.zero
    ⟨j, hjmem⟩ hdom hqη.le

/-- **TCP06, the exact coordinate at every preimage.** If `p ∈ B(i, 200ρ(i))` has `‖η_i(p)‖ ≤ 8`,
every `q` with `F(q) = F(p)` lies in `B(i, 200ρ(i))` and has `η_i(q) = η_i(p)` (the full marker and
the vector block of the own tag). -/
theorem tcp06_full_marker_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    {p q : X} (hp : p ∈ ball i (200 * ρ i))
    (hη : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 8)
    (hpq : cgpGlobalMap_BAUGP P P.zero q =
      cgpGlobalMap_BAUGP P P.zero p) :
    q ∈ ball i (200 * ρ i) ∧
      cgpCircleCoord_BAUGP P i hi q = cgpCircleCoord_BAUGP P i hi p := by
  obtain ⟨j, hjmem⟩ := j
  change j = i at hji
  subst hji
  have hrj := hρ j
  have hcutp : P.circle.cutoff j p = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF_BAUGP P P.zero
      ⟨j, hjmem⟩ hp hη
  have hblk : WithLp.toLp 2 ((ρ j * P.circle.cutoff j q) •
      cgpCircleCoord_BAUGP P j hi q, ρ j * P.circle.cutoff j q) =
      (WithLp.toLp 2 ((ρ j * P.circle.cutoff j p) • cgpCircleCoord_BAUGP P j hi p,
        ρ j * P.circle.cutoff j p) : WithLp 2 (ℝ² × ℝ)) :=
    congrArg (fun y => y (.inl ⟨j, hjmem⟩)) hpq
  have hsnd : ρ j * P.circle.cutoff j q = ρ j * P.circle.cutoff j p :=
    congrArg (fun y : WithLp 2 (ℝ² × ℝ) => y.snd) hblk
  have hfst : (ρ j * P.circle.cutoff j q) • cgpCircleCoord_BAUGP P j hi q =
      (ρ j * P.circle.cutoff j p) • cgpCircleCoord_BAUGP P j hi p :=
    congrArg (fun y : WithLp 2 (ℝ² × ℝ) => y.fst) hblk
  rw [hcutp, mul_one] at hsnd
  have hcutq : P.circle.cutoff j q = 1 :=
    mul_left_cancel₀ hrj.ne' (hsnd.trans (mul_one _).symm)
  rw [hcutq, hcutp, mul_one] at hfst
  refine ⟨?_, smul_right_injective _ hrj.ne' hfst⟩
  have h1 : (ρ j)⁻¹ * dist q j < 200 :=
    (P.circle.coord_lt_of_cutoff_ne_zero j hi q (by rw [hcutq]; exact one_ne_zero)).1
  rw [inv_mul_lt_iff₀ hrj] at h1
  rw [mem_ball]
  linarith

/-- **TCP06, the own coordinate.** The `1`-Lipschitz linear map `z ↦ (z_j).fst` (the vector part of
the own block of `j`, `j.1 = i`) reads `a` off every block `(a, m)`, and reads `η_i(q)` off
`ρ(i)⁻¹F(q)` on `{‖η_i‖ ≤ 8} ∩ B(i, 200ρ(i))`. -/
theorem tcp06_own_coordinate_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i) :
    ∃ Pc : BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²) →L[ℝ] ℝ²,
      (∀ z, ‖Pc z‖ ≤ ‖z‖) ∧
      (∀ (z : BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²)) (a : ℝ²) (m : ℝ),
        z (.inl j) = WithLp.toLp 2 (a, m) → Pc z = a) ∧
      ∀ q ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8 →
        Pc ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q) =
          cgpCircleCoord_BAUGP P i hi q := by
  let Pc : BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²) →L[ℝ] ℝ² :=
    (WithLp.fstL 2 ℝ ℝ² ℝ).comp
      (PiLp.proj 2 (fun _ : CGPTag_BAUGP P P.zero => WithLp 2 (ℝ² × ℝ)) (.inl j))
  have hPc : ∀ z, Pc z = (z (.inl j)).fst := fun z => rfl
  refine ⟨Pc, fun z => ?_, fun z a m hz => ?_, fun q hq hq8 => ?_⟩
  · rw [hPc]
    exact (WithLp.norm_fst_le _ _).trans (PiLp.norm_apply_le _ _)
  · rw [hPc, hz]
    rfl
  · rw [hPc, PiLp.smul_apply, (tg_own_tag_KA7_BAUGP P hi j hji hq hq8).1]
    rfl

/-- **TCP06, FC25 in `R_i` units** (`hausdorffDist_coordinate_graph_coverage_le` with
`F' = ρ(i)⁻¹F`, `η = η_i`, `D = {B(i, 200ρ(i)), ‖η_i‖ ≤ 8}`, the model `Φ`, the own coordinate,
`X = F'(Ã₁)`, centre `F'(p)`): for a core witness `p` (`‖η_i(p)‖ ≤ 7`) and `0 < R < 1/100`, the
closed-ball Hausdorff distance between `F'(Ã₁)` and the tangent plane `F'(p) + im DΦ(η_i p)` is at
most `3(2e + C_d R²/2)`. -/
theorem tcp06_scaled_coverage_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²))
    (hΦ : ContDiff ℝ 2 Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1)) {Cd eg : ℝ}
    (hCd : 0 ≤ Cd) (heg : 0 ≤ eg) (hD2 : ∀ a, ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ Cd)
    (hTG : ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P i hi x‖ ≤ 8 →
      ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x -
        Φ (cgpCircleCoord_BAUGP P i hi x)‖ < eg)
    {p : X} (hp : p ∈ ball i (200 * ρ i))
    (hη : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 7) {R : ℝ} (hR0 : 0 < R)
    (hR1 : R < 1 / 100) :
    hausdorffDist ((fun q => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q) ''
        fc04Set_BAUGP P P.zero 8 ∩
        closedBall ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero p) R)
      ((fun v => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero p +
          fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p) v) '' (univ : Set ℝ²) ∩
        closedBall ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero p) R) ≤
      3 * (2 * eg + Cd * R ^ 2 / 2) := by
  have hri := hρ i
  obtain ⟨Pc, hP, hread, hPq⟩ := tcp06_own_coordinate_KA8_BAUGP P hi j hji
  have hgraph : ∀ u, Pc (Φ u) = u := fun u => hread _ u 1 (hown u)
  have hp8 : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 8 := le_trans hη (by norm_num)
  have hPx := hPq p hp hp8
  have hpS : p ∈ fc04Set_BAUGP P P.zero 8 := by
    refine ⟨j, ?_, ?_⟩
    · rw [hji]; exact hp
    · obtain ⟨j', hj'⟩ := j
      change j' = i at hji
      subst hji
      exact hp8
  have hlocal : ∀ y ∈ (fun q => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q) ''
      fc04Set_BAUGP P P.zero 8 ∩
      closedBall ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero p) R,
      ∃ q ∈ {q | q ∈ ball i (200 * ρ i) ∧ ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8},
        (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q = y ∧
          Pc y = cgpCircleCoord_BAUGP P i hi q := by
    rintro y ⟨⟨q, -, rfl⟩, hy⟩
    have hdist : dist (cgpGlobalMap_BAUGP P P.zero q)
        (cgpGlobalMap_BAUGP P P.zero p) ≤ R * ρ i := by
      rw [mem_closedBall, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hri),
        inv_mul_le_iff₀ hri] at hy
      linarith
    obtain ⟨hqb, -, -, hηq⟩ := tcp06_localization_KA8_BAUGP P hi j hji hp hη hR0.le hR1 hdist
    exact ⟨q, ⟨hqb, hηq.le⟩, rfl, hPq q hqb hηq.le⟩
  have happrox : ∀ q ∈ {q | q ∈ ball i (200 * ρ i) ∧
      ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8},
      dist ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q)
        (Φ (cgpCircleCoord_BAUGP P i hi q)) ≤ eg := by
    intro q hq
    rw [dist_eq_norm]
    exact (hTG q hq.1 hq.2).le
  have hcover : ∀ u ∈ closedBall (Pc ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero p)) R,
      ∃ q ∈ {q | q ∈ ball i (200 * ρ i) ∧ ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8},
        cgpCircleCoord_BAUGP P i hi q = u ∧
          (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q ∈
            (fun q => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q) ''
              fc04Set_BAUGP P P.zero 8 := by
    intro u hu
    rw [hPx, mem_closedBall, dist_eq_norm] at hu
    have hu8 : ‖u‖ ≤ 8 := by
      have := norm_sub_norm_le u (cgpCircleCoord_BAUGP P i hi p)
      linarith
    obtain ⟨q, hqb, hqu⟩ := circle_coord_cover_KA8_BAUGP P hi
      (lt_of_le_of_lt hu8 (by norm_num))
    have hq8 : ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8 := by rw [hqu]; exact hu8
    refine ⟨q, ⟨hqb, hq8⟩, hqu, q, ?_, rfl⟩
    refine ⟨j, ?_, ?_⟩
    · rw [hji]; exact hqb
    · obtain ⟨j', hj'⟩ := j
      change j' = i at hji
      subst hji
      exact hq8
  have hk := hausdorffDist_coordinate_graph_coverage_le
    (fun q => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q)
    (cgpCircleCoord_BAUGP P i hi)
    {q | q ∈ ball i (200 * ρ i) ∧ ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8}
    Φ Pc hP hgraph
    ((fun q => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q) ''
      fc04Set_BAUGP P P.zero 8)
    ((ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero p) ⟨p, hpS, rfl⟩ hR0 hCd heg
    (fun u _ => hΦ.contDiffAt)
    (fun u _ => by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Φ) (x := u) (n := 1)
      rw [norm_iteratedFDeriv_one] at h
      calc ‖iteratedFDeriv ℝ 2 Φ u‖ = ‖iteratedFDeriv ℝ (1 + 1) Φ u‖ := rfl
        _ = ‖fderiv ℝ (fderiv ℝ Φ) u‖ := h.symm
        _ ≤ Cd := hD2 u)
    hlocal happrox hcover
  rw [hPx] at hk
  exact hk

/-- **TCP06, the model reference**: a differentiable model `Φ` with own block `(a, 1)` at `j` has
`|z| ≤ ‖DΦ(a) z‖` (its identity component, through the own coordinate). -/
theorem tcp06_model_reference_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²))
    (hΦ : Differentiable ℝ Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1)) (a z : ℝ²) :
    ‖z‖ ≤ ‖fderiv ℝ Φ a z‖ := by
  obtain ⟨Pc, hP, hread, -⟩ := tcp06_own_coordinate_KA8_BAUGP P hi j hji
  have hgraph : ∀ u, Pc (Φ u) = u := fun u => hread _ u 1 (hown u)
  have h := hP (fderiv ℝ Φ a z)
  rwa [fderiv_left_inverse_KA8 Φ Pc hgraph (hΦ a) z] at h

/-- **TCP06, TCP01's Gram margin in norm form**: at `q ∈ B(i, 200ρ(i))`, with `β₂ ≤ 10⁻⁷`, every
unit `ξ ∈ ℝ²` is within `γ + β₂` of `dη_i(w)` for a unit `w` of `ρ(i)⁻²g`. -/
theorem tcp06_gram_low_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hβ : β 2 ≤ 1 / 10000000) {i : X} (hi : i ∈ P.circle.centres) {q : X}
    (hq : q ∈ ball i (200 * ρ i)) :
    ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) q,
      (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 ∧
        ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) q w - ξ‖ ≤ γ + β 2 := by
  intro ξ hξ
  obtain ⟨w, hw, hlt⟩ := circleAdapted_gram_lower_KA2_BAUGP P hβ hi hq ξ hξ
  exact ⟨w, hw, hlt.le⟩

/-- **TCP06 at one core witness.** For a model `Φ` with own block `(a, 1)` at `j` (`j.1 = i`),
`‖D²Φ‖ ≤ C_d`, (TG)'s value clause with error `e`, a core witness `p` (`‖η_i(p)‖ ≤ 7`) and (TP)
(`0 < Σ < min(Γ/200, Γ³/(100C_d))`, `0 < e < ΓΣ/100`): the plane `im DΦ(η_i p)` has dimension
two, and the open-ball cloud test at `x = F(p)` with FC04's exact radius `r(x) = Σx_ρ = Σρ(p)`
holds: `hausdorffEDist (S̃₁ ∩ B(x, r/Γ)) ((x + im DΦ(η_i p)) ∩ B(x, r/Γ)) ≤ Γr`. -/
theorem tcp06_point_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²))
    (hΦ : ContDiff ℝ 2 Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1)) {Cd Γ sg eg : ℝ}
    (hD2 : ∀ a, ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ Cd) (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hCd : 0 < Cd) (hsgC : sg < Γ ^ 3 / (100 * Cd)) (heg : 0 < eg)
    (hegΓ : eg < Γ * sg / 100)
    (hTG : ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P i hi x‖ ≤ 8 →
      ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero x -
        Φ (cgpCircleCoord_BAUGP P i hi x)‖ < eg)
    {p : X} (hp : p ∈ ball i (200 * ρ i))
    (hη : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 7) :
    Module.finrank ℝ (fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p)).range = 2 ∧
      hausdorffEDist (cgpGlobalMap_BAUGP P P.zero ''
          fc04Set_BAUGP P P.zero 8 ∩
          ball (cgpGlobalMap_BAUGP P P.zero p)
            (scaleRadius (cgpScaleTag_BAUGP P P.zero) sg
              (cgpGlobalMap_BAUGP P P.zero p) / Γ))
        ((AffineSubspace.mk' (cgpGlobalMap_BAUGP P P.zero p)
            (fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p)).range :
            Set (BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²))) ∩
          ball (cgpGlobalMap_BAUGP P P.zero p)
            (scaleRadius (cgpScaleTag_BAUGP P P.zero) sg
              (cgpGlobalMap_BAUGP P P.zero p) / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag_BAUGP P P.zero) sg
          (cgpGlobalMap_BAUGP P P.zero p)) := by
  have hri := hρ i
  have hTlow := tcp06_model_reference_KA8_BAUGP P hi j hji Φ (hΦ.differentiable (by norm_num)) hown
    (cgpCircleCoord_BAUGP P i hi p)
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p) :
        ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²)) := by
      intro z w hzw
      have h := hTlow (z - w)
      have h0 : fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p) (z - w) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hzw
      rw [h0, norm_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have h := LinearMap.finrank_range_of_inj hinj
    rw [finrank_euclideanSpace_fin] at h
    exact h
  · have hrad : scaleRadius (cgpScaleTag_BAUGP P P.zero) sg
        (cgpGlobalMap_BAUGP P P.zero p) = sg * ρ p := by
      rw [scaleRadius, cgpGlobalMap_scale_BAUGP]
    rw [hrad]
    obtain ⟨hs1, hs2⟩ := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ hri (mem_ball.mp hp) hΛ200
    have hrad2 := sgp06_radius_SGP5 hsg.le hri hΓ (by linarith : 3 * ρ i / 4 ≤ ρ p)
      (by linarith : ρ p ≤ 5 * ρ i / 4)
    obtain ⟨hrlo, hrhi, hr, hd⟩ := hrad2
    have hpar := sgp06_parameters_SGP5 hΓ hΓ1 hsg hsgΓ hCd hsgC hegΓ hrlo hrhi
    obtain ⟨hRh0, hRh, ht0, ht1, htR0, htR, hbud, hbudt, hslack⟩ := hpar
    have hcovR := tcp06_scaled_coverage_KA8_BAUGP P hi j hji Φ hΦ hown hCd.le heg.le hD2 hTG hp hη
      hRh0 hRh
    have hcovt := tcp06_scaled_coverage_KA8_BAUGP P hi j hji Φ hΦ hown hCd.le heg.le hD2 hTG hp hη
      htR0 htR
    have hp8 : p ∈ fc04Set_BAUGP P P.zero 8 := by
      refine ⟨j, ?_, ?_⟩
      · rw [hji]; exact hp
      · obtain ⟨j', hj'⟩ := j
        change j' = i at hji
        subst hji
        exact le_trans hη (by norm_num)
    exact hausdorffEDist_ball_le_of_scaled_coverage_SGP5
      (cgpGlobalMap_BAUGP P P.zero '' fc04Set_BAUGP P P.zero 8)
      ((fun q => (ρ i)⁻¹ • cgpGlobalMap_BAUGP P P.zero q) ''
        fc04Set_BAUGP P P.zero 8)
      (cgpGlobalMap_BAUGP P P.zero p) ⟨p, hp8, rfl⟩ hri (Set.image_image _ _ _).symm
      (fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p))
      hRh0 ht0 ht1 (lt_of_le_of_lt hcovR hbud) (lt_of_le_of_lt hcovt hbudt) hslack hr hd

/-- **TCP06, the rank at every preimage.** For a model `Φ` with own block `(a, 1)` at `j`,
`‖DΦ‖ ≤ C` (`C = tcpGraphConst`), (TG)'s derivative clause with error `e < 1/100`, TCP01's Gram
margin `γ + β₂ ≤ 1/10` (`β₂ ≤ 10⁻⁷`), a core witness `p` and ANY `q` with `F(q) = F(p)`: with
`T_x = DΦ(η_i p)` and `P_q` the projection onto `im T_x` of `ρ(i)⁻¹dF_q`, `P_q` is onto, the normal
error is at most `eν`, `‖P_q v‖ ≥ ν(v)/2` on the `g`-orthogonal complement of `ker P_q` and
`‖P_q v‖ ≤ 3Cν(v)` (`ν = √(ρ(i)⁻²g)`). -/
theorem tcp06_rank_point_KA8_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {i : X} (hi : i ∈ P.circle.centres) (j : P.circle.finite_centres.toFinset) (hji : j.1 = i)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P P.zero => ℝ²))
    (hΦ : ContDiff ℝ 2 Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1)) {eg : ℝ}
    (hD1 : ∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst) (heg1 : eg < 1 / 100)
    (hTGd : ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P i hi x‖ ≤ 8 →
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P P.zero) x w -
            fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi x)
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
          eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    {p : X} (hp : p ∈ ball i (200 * ρ i))
    (hη : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 7) {q : X}
    (hq : cgpGlobalMap_BAUGP P P.zero q = cgpGlobalMap_BAUGP P P.zero p) :
    let Pq := (fderiv ℝ Φ
      (cgpCircleCoord_BAUGP P i hi p)).range.orthogonalProjectionOnto.comp
        ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P P.zero) q)
    Function.Surjective Pq ∧
      (∀ v, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v) := by
  have hp8 : ‖cgpCircleCoord_BAUGP P i hi p‖ ≤ 8 := le_trans hη (by norm_num)
  obtain ⟨hqb, hηq⟩ := tcp06_full_marker_KA8_BAUGP P hi j hji hp hp8 hq
  have hq8 : ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8 := by rw [hηq]; exact hp8
  have hTlow := tcp06_model_reference_KA8_BAUGP P hi j hji Φ (hΦ.differentiable (by norm_num)) hown
    (cgpCircleCoord_BAUGP P i hi p)
  have hlow := tcp06_gram_low_KA8_BAUGP P hβ hi hqb
  have hup := norm_mvfderiv_circleCoord_le_KA6_BAUGP P hi hqb
  have hD : ∀ v : TangentSpace 𝓘(ℝ, E3) q,
      ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P P.zero) q v -
        fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p)
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) q v)‖ ≤
        eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v) := by
    intro v
    rw [← hηq]
    exact hTGd q hqb hq8 v
  have hde : γ + β 2 + eg ≤ 1 / 5 := by linarith
  have heC : eg ≤ tcpGraphConst := by linarith [one_le_tcpGraphConst]
  exact tcp06_rank_block_KA8 g q (ρ i)⁻¹ (cgpCircleCoord_BAUGP P i hi)
    (cgpGlobalMap_BAUGP P P.zero)
    (fderiv ℝ Φ (cgpCircleCoord_BAUGP P i hi p)) hTlow (hD1 _) hlow hup hD hde heC

end Packets


end DifferentialGeometry.Geometry.Collapse
