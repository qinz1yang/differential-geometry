import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualFirstComparisonList (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstComparisonList.lean` by
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNT_C14KA2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNT_C14KA2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCT_C14KA2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The first (`ℝ²`) component of the original normalized `(2, β₂)`-splitting of the circle
adapted packet (i) at `j`. -/
def circleSplitFst_KA2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (j : X) (hj : j ∈ P.circle.centres) : X → ℝ² :=
  let A := P.circleAdapted j hj
  let sp := A.split
  letI := A.instY
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  fun x => (sp.toFun x).fst

/-- The circle coordinate of the adapted packet (i): value error `< γ` against the SAME splitting
and the physical Lipschitz bound `(1 + γ)/ρ(j)` on `B(j, 200ρ(j))`. -/
theorem circleAdapted_physical_KA2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hγ : 0 ≤ γ) {j : X} (hj : j ∈ P.circle.centres) :
    (∀ x ∈ ball j (200 * ρ j), ‖cgpCircleCoord_BAUGP P j hj x -
        circleSplitFst_KA2_BAUGP P j hj x‖ < γ) ∧
      ∀ y ∈ ball j (200 * ρ j), ∀ z ∈ ball j (200 * ρ j),
        ‖cgpCircleCoord_BAUGP P j hj y - cgpCircleCoord_BAUGP P j hj z‖ ≤
          (1 + γ) / ρ j * dist y z := by
  have hrj := hρ j
  have hn : ∀ y ∈ ball j (200 * ρ j), (ρ j)⁻¹ * dist y j < 200 := fun y hy =>
    inv_mul_dist_lt_of_mem_ball_LC87 hrj hy
  have he : ∀ y z : X, ((Real.toNNReal (1 + γ) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      (1 + γ) / ρ j * dist y z := fun y z => by
    rw [Real.coe_toNNReal _ (by linarith)]
    field_simp
  let A := P.circleAdapted j hj
  have hadapt := A.adapted
  have hlip := A.lipschitz
  refine ⟨fun x hx => hadapt x (hn x hx), fun y hy z hz => ?_⟩
  have h := @LipschitzOnWith.dist_le_mul X ℝ²
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace _ _ _ _ hlip y (hn y hy) z
    (hn z hz)
  have h' : ‖cgpCircleCoord_BAUGP P j hj y - cgpCircleCoord_BAUGP P j hj z‖
      ≤ ((Real.toNNReal (1 + γ) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) := by
    rw [← dist_eq_norm]
    exact h
  linarith [he y z]

/-- The circle chart's enclosure at physical scale: `|η_j(q)| < 100` on `B(j, 200ρ(j))` puts `q` in
`B(j, 102ρ(j))`. -/
theorem circle_enclosure_physical_KA2_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.circle.centres) {q : X} (hq : q ∈ ball j (200 * ρ j))
    (hη : ‖cgpCircleCoord_BAUGP L j hj q‖ < 100) : q ∈ ball j (102 * ρ j) := by
  have hrj := hρ j
  have hc := L.circle.chart_center j hj
  have hn : (ρ j)⁻¹ * dist q j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hq
  have hgoal : (ρ j)⁻¹ * dist q j < 102 → q ∈ ball j (102 * ρ j) := fun h => by
    rw [mem_ball]
    rw [inv_mul_lt_iff₀ hrj] at h
    linarith
  apply hgoal
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  have hq' : q ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    change (ρ j)⁻¹ * @dist X mX.toDist q c.center < 200
    rw [hc']
    exact hn
  have h := c.enclosure q hq' hη
  change (ρ j)⁻¹ * @dist X mX.toDist q c.center < 102 at h
  rw [hc'] at h
  exact h

/-- **TCP01, bindable part** (`lem:fibration-first-comparison-list`) on `LocalChartPackets`, at a
circle centre `i` (`R_i = ρ(i)`, `D_i = B(i, 10R_i)`): the whole comparison list count, the listed
ratios in `(99/100, 101/100)`, the listed original coordinates smooth on `D_i`, the zero
assertions, the early circle-coordinate quality and the enclosure of `|η_i| ≤ 8` in
`B(i, 102R_i)`. -/
theorem tcp01_row_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hγ : 0 ≤ γ) {i : X}
    (hi : i ∈ P.circle.centres) :
    (({j | j ∈ P.circle.centres ∧
          (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard : ℝ) +
        {j | j ∈ P.slim.centres ∧
          (tsupport (P.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        {j | j ∈ P.edgeB.centres ∧
          (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        (zeroMeetingList_BAUGP P.zero i 10).ncard ≤ fc07ActiveBound) ∧
    (∀ j (hj : j ∈ P.circle.centres), (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCircleCoord_BAUGP P j hj)
          (ball i (10 * ρ i))) ∧
    (∀ j (hj : j ∈ P.slim.centres), (tsupport (P.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.slim.centre j hj).coord_BCG2 (ball i (10 * ρ i))) ∧
    (∀ j ∈ P.edgeB.centres, (tsupport (P.edgeB.cutoff_BAUGA j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.edgeB.coord_BAUGA j) (ball i (10 * ρ i))) ∧
    (∀ k ∈ zeroMeetingList_BAUGP P.zero i 10, ∀ k' ∈ zeroMeetingList_BAUGP P.zero i 10, k = k') ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      (∀ x ∈ ball i (10 * ρ i), 3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (P.zero.zero k hk).radius) ∧
      ∃ O : Set X, IsOpen O ∧ ball i (10 * ρ i) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero k hk).radial O) ∧
    (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P i hi x -
        circleSplitFst_KA2_BAUGP P i hi x‖ < γ) ∧
    (∀ y ∈ ball i (200 * ρ i), ∀ z ∈ ball i (200 * ρ i),
      ‖cgpCircleCoord_BAUGP P i hi y - cgpCircleCoord_BAUGP P i hi z‖ ≤
        (1 + γ) / ρ i * dist y z) ∧
    (∀ q ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P i hi q‖ ≤ 8 →
      q ∈ ball i (102 * ρ i)) := by
  obtain ⟨hcount, hC, hS, hE, hZ1, hZ2⟩ := fc07_input_packet_BAUGP P hΛ hΔ hμ hτ hLΛ hLmax he hT i
  have hri := hρ i
  have hΛ1 : Λ < 1 / 100000000000 := by nlinarith
  have hΔΛ : Δ * Λ < 1 / 100000000000 := by nlinarith
  obtain ⟨hA1, hA2⟩ := circleAdapted_physical_KA2_BAUGP P hγ hi
  refine ⟨hcount, fun j hj hmeet => ?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_, hZ1, hZ2,
    hA1, hA2, fun q hq hη => circle_enclosure_physical_KA2_BAUGP P hi hq
      (by linarith)⟩
  · obtain ⟨-, hd, hsub, hsub', -⟩ := hC j hj hmeet
    refine ⟨ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale hri hd (by nlinarith), ?_⟩
    exact (cgpCircleCoord_contMDiffOn_BAUGP P hj).mono (hsub.trans hsub')
  · obtain ⟨hcm, -, hd, hsub, hsub', -⟩ := hS j hj hmeet
    exact ⟨ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale hri hd (by nlinarith),
      hcm.mono (hsub.trans hsub')⟩
  · obtain ⟨-, hd, hsub, hsub', -⟩ := hE j hj hmeet
    exact ⟨ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale hri hd (by nlinarith),
      (P.edgeB.contMDiffOn_coord_BAUGA hj).mono (hsub.trans hsub')⟩

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_C14KA2_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNR_C14KA2_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_C14KA2_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a


end DifferentialGeometry.Geometry.Collapse
