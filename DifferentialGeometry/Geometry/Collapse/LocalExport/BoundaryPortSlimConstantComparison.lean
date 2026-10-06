import DifferentialGeometry.Geometry.Fibration.ActualSlimConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleGram
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualSlimConstantComparison (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualSlimConstantComparison.lean` by
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
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X]
  {Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

variable {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_TCP03S_KA5_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_TCP03S_KA5_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_TCP03S_KA5_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The original long test of the slim chart `j` (`SlimChart.test`) along a physical direction
`w₀` whose normalized geodesics reach `x'`:
`|ρ(j) dη_j(w₀) − (ρ(j)/d(x, x'))(u_j(x') − u_j(x))| < σ_s`. -/
theorem slim_test_of_scaled_KA5_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.slim.centres) {x x' : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j))
    (hx' : x' ∈ ball j (10 ^ 6 * Δ / σs * ρ j)) (hd : 10 ^ 6 * Δ * ρ j < dist x x')
    (w₀ : TangentSpace 𝓘(ℝ, E3) x) (hw₀ : g.inner x w₀ w₀ = 1)
    (hgeo : ∀ (R : ℝ) (hR : 0 < R),
        let hMc : CompleteSpace X := ‹CompleteSpace X›
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x (R • w₀) (dist x x') = x') :
    |ρ j * mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hj).coord_BCG2 x w₀ -
      ρ j / dist x x' * (slimRaw_KA3_BAUGP L j x' - slimRaw_KA3_BAUGP L j x)| < σs := by
  have hrj := hρ j
  have hgj := hgeo (ρ j) hrj
  have hxR : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hx'R : (ρ j)⁻¹ * dist x' j < 10 ^ 6 * Δ / σs := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx'
  have hdR : 10 ^ 6 * Δ < (ρ j)⁻¹ * dist x x' := by
    rw [lt_inv_mul_iff₀ hrj]
    linarith
  have hunit : (scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hrj) 2) g).inner x (ρ j • w₀)
      (ρ j • w₀) = 1 := by
    rw [scaleMetric_inner, gInner_smul_self, hw₀]
    field_simp
  rw [slimRaw_KA3_eq_BAUGP L hj, slimRaw_KA3_eq_BAUGP L hj]
  have he : ∀ a : ℝ, a / ((ρ j)⁻¹ * dist x x') = ρ j / dist x x' * a := fun a => by
    field_simp
  have hlin : mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hj).coord_BCG2 x (ρ j • w₀) =
      ρ j * mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hj).coord_BCG2 x w₀ := by
    rw [map_smul, smul_eq_mul]
  let S := L.slim.centre j hj
  let _ := S.instZ
  have hT : |mvfderiv 𝓘(ℝ, E3) S.coord_BCG2 x (ρ j • w₀) -
      ((@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ S.split
        x').fst -
        (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ S.split
          x).fst) / ((ρ j)⁻¹ * @dist X mX.toDist x x')| < σs := by
    let P := S.packet
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)
    let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hrj)
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hrj)
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hrj)
    let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hrj)).mpr hMc
    have hxB : x ∈ ball j (10 ^ 6 * Δ) := hxR
    have hx'B : x' ∈ ball j (10 ^ 6 * Δ / σs) := hx'R
    have hdB : 10 ^ 6 * Δ < dist x x' := hdR
    exact P.test x hxB x' hx'B hdB (ρ j • w₀) hunit hgj
  rw [hlin, he] at hT
  exact hT

/-- The slim chart's own raw-axis lift: for `d(x, j) < R_x ρ(j)` and `t ≥ 0` with
`R_x + t + 2β₁ ≤ β₁⁻¹`, some `y` has `|ρ(j)⁻¹ d(x, y) − t| ≤ 3β₁`, `|u_j(y) − u_j(x) − t| < 2β₁`
and `ρ(j)⁻¹ d(y, j) < R_x + t + 4β₁`. -/
theorem slim_lift_KA5_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ L.slim.centres) {x : X} {Rx t : ℝ} (hx : dist x j < Rx * ρ j)
    (ht : 0 ≤ t) (hroom : Rx + t + 2 * β 1 ≤ (β 1)⁻¹) :
    ∃ y, |(ρ j)⁻¹ * dist x y - t| ≤ 3 * β 1 ∧
      |slimRaw_KA3_BAUGP L j y - slimRaw_KA3_BAUGP L j x - t| < 2 * β 1 ∧
        (ρ j)⁻¹ * dist y j < Rx + t + 4 * β 1 := by
  have hrj := hρ j
  let Sj := L.slim.centre j hj
  let _ := Sj.instZ
  obtain ⟨f', hf'⟩ := exists_finOne_split_KA3 Sj.split
  have hxR : @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toDist x j < Rx := by
    rw [MetricSpace.rescale_dist, inv_mul_lt_iff₀ hrj]
    linarith
  have hξ : ‖(EuclideanSpace.single 0 1 : ℝ¹)‖ = 1 := by simp
  obtain ⟨y, -, h1, h2, h3⟩ := @kl_lift_KA4 X Sj.Z (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj))
    Sj.instZ 1 j Sj.z (β 1) f' x Rx t hxR _ hξ ht hroom
  rw [MetricSpace.rescale_dist] at h1 h3
  refine ⟨y, h1, ?_, h3⟩
  have hy : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ Sj.split
      y).fst = slimRaw_KA3_BAUGP L j y := (slimRaw_KA3_eq_BAUGP L hj y).symm
  have hx' : (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ Sj.split
      x).fst = slimRaw_KA3_BAUGP L j x := (slimRaw_KA3_eq_BAUGP L hj x).symm
  rw [hf' y, hf' x, hy, hx'] at h2
  have he : EuclideanSpace.single (0 : Fin 1) (slimRaw_KA3_BAUGP L j y) -
      EuclideanSpace.single 0 (slimRaw_KA3_BAUGP L j x) - t • EuclideanSpace.single 0 (1 : ℝ) =
      EuclideanSpace.single 0 (slimRaw_KA3_BAUGP L j y - slimRaw_KA3_BAUGP L j x - t) := by
    ext k
    fin_cases k
    simp
  rw [he, PiLp.norm_single, Real.norm_eq_abs] at h2
  exact h2

/-- Coarse Lipschitz of the slim raw coordinate (distortion of its splitting):
`|u_j(y) − u_j(z)| ≤ ρ(j)⁻¹ d(y, z) + β₁` on `B(j, β₁⁻¹ρ(j))`. -/
theorem slim_raw_coarse_KA5_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.slim.centres) {y z : X} (hy : (ρ j)⁻¹ * dist y j < (β 1)⁻¹)
    (hz : (ρ j)⁻¹ * dist z j < (β 1)⁻¹) :
    |slimRaw_KA3_BAUGP L j y - slimRaw_KA3_BAUGP L j z| ≤ (ρ j)⁻¹ * dist y z + β 1 := by
  have hrj := hρ j
  let Sj := L.slim.centre j hj
  let _ := Sj.instZ
  have hyB : y ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toPseudoMetricSpace j (β 1)⁻¹ := by
    change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toDist y j < (β 1)⁻¹
    rw [MetricSpace.rescale_dist]; exact hy
  have hzB : z ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toPseudoMetricSpace j (β 1)⁻¹ := by
    change @dist X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)).toDist z j < (β 1)⁻¹
    rw [MetricSpace.rescale_dist]; exact hz
  have hd := @KleinerLottApprox.distortion X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _
    Sj.split y hyB z hzB
  rw [MetricSpace.rescale_dist] at hd
  have hfst := WithLp.dist_fst_le (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹
    (inv_pos.mpr hrj)) _ _ _ _ Sj.split y) (@KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹
    (inv_pos.mpr hrj)) _ _ _ _ Sj.split z)
  rw [Real.dist_eq, ← slimRaw_KA3_eq_BAUGP L hj y, ← slimRaw_KA3_eq_BAUGP L hj z] at hfst
  linarith [(abs_le.mp hd).2]

/-- The slim chart's own side of TCP03's saturation: the long test at `(x, y)` for the raw-axis
lift `y` (`|u_j(y) − u_j(x) − 10L| < 2β₁`, `d(x, y) ∈ [(10L − 3β₁)ρ(j), (10L + 3β₁)ρ(j)]`) gives
`ρ(j) dη_j(w₀) ≥ 1 − (σ_s + β₁)`. -/
theorem slim_own_side_KA5_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.slim.centres) {x y : X} (hxL : x ∈ ball j (10 ^ 6 * Δ * ρ j))
    (hyL : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j)) (hΔ : 1 ≤ Δ) (hbpos : 0 < β 1)
    (hb1 : β 1 ≤ 1 / 1000)
    (hD1 : (10 * (10 ^ 6 * Δ) - 3 * β 1) * ρ j ≤ dist x y)
    (hD2 : dist x y ≤ (10 * (10 ^ 6 * Δ) + 3 * β 1) * ρ j)
    (hlift : |slimRaw_KA3_BAUGP L j y - slimRaw_KA3_BAUGP L j x - 10 * (10 ^ 6 * Δ)| < 2 * β 1)
    (w₀ : TangentSpace 𝓘(ℝ, E3) x) (hw₀ : g.inner x w₀ w₀ = 1)
    (hgy : ∀ (R : ℝ) (hR : 0 < R),
        let hMc : CompleteSpace X := ‹CompleteSpace X›
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x (R • w₀) (dist x y) = y) :
    1 - (σs + β 1) ≤ ρ j * mvfderiv 𝓘(ℝ, E3) (L.slim.centre j hj).coord_BCG2 x w₀ := by
  have hrj := hρ j
  have hDpos : 0 < dist x y := lt_of_lt_of_le (by nlinarith) hD1
  have hT := slim_test_of_scaled_KA5_BAUGP L hj hxL hyL (by nlinarith) w₀ hw₀ hgy
  have hq : 1 / (10 * (10 ^ 6 * Δ) + 3 * β 1) ≤ ρ j / dist x y := by
    rw [div_le_div_iff₀ (by positivity) hDpos]
    linarith
  exact long_test_scalar_KA4 (by nlinarith) hbpos.le hb1 hq
    (by linarith [(abs_lt.mp hlift).1]) hT

/-- The reference side of TCP03's slim saturation: the circle test at `(x, z)` (`d(x, z) = 400ρ(i)`
on the long segment toward the lift `y`), FC22's short gain through the coarse Lipschitz bound of
the slim raw coordinate, and (TR) at `x, z` give `(A(ρ(i) dη_i(w₀)))₀ ≥ 1 − (γ + E₀ + β₁)`. -/
theorem slim_reference_side_KA5_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈ P.slim.centres)
    (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100)) {x y z : X} (hx : x ∈ ball i (10 * ρ i))
    (hxjd : dist x j < (91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) (hΔ : 1 ≤ Δ)
    (hbinv : 100 * (10 ^ 6 * Δ) ≤ (β 1)⁻¹) (hb0 : 0 ≤ β 1) (hb1 : β 1 ≤ 1 / 1000)
    (hdxy : |(ρ j)⁻¹ * dist x y - 10 * (10 ^ 6 * Δ)| ≤ 3 * β 1)
    (hyj : (ρ j)⁻¹ * dist y j < 91 / 100 * (10 ^ 6 * Δ) + 4 * 10 + 10 * (10 ^ 6 * Δ) + 4 * β 1)
    (hlift : |slimRaw_KA3_BAUGP P j y - slimRaw_KA3_BAUGP P j x -
      10 * (10 ^ 6 * Δ)| < 2 * β 1)
    (hxz : dist x z = 400 * ρ i) (hzy : dist z y = dist x y - 400 * ρ i)
    (w₀ : TangentSpace 𝓘(ℝ, E3) x) (hw₀ : g.inner x w₀ w₀ = 1)
    (hgz : ∀ (R : ℝ) (hR : 0 < R),
        let hMc : CompleteSpace X := ‹CompleteSpace X›
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x (R • w₀) (dist x z) = z)
    {E₀ : ℝ} (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P j z) -
        A (circleRaw_KA3_BAUGP P i z) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P j i)‖ < E₀) :
    1 - (γ + E₀ + β 1) ≤
      A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w₀) 0 := by
  have hri := hρ i
  have hrj := hρ j
  obtain ⟨hs1, hs2⟩ := hs
  have hrj2 : 99 / 100 * ρ i < ρ j := by rwa [lt_div_iff₀ hri] at hs1
  have hxi : dist x i < 10 * ρ i := mem_ball.mp hx
  have hxi2 : x ∈ ball i (200 * ρ i) := by rw [mem_ball]; linarith
  have hzi : dist z i < 410 * ρ i := by
    have := dist_triangle z x i
    rw [dist_comm z x] at this
    linarith
  have hzi2 : z ∈ ball i (201 * 10000 * ρ i) := by rw [mem_ball]; linarith
  have hT := circle_test_of_scaled_KA4_BAUGP P hi hxi2 hzi2 (by linarith) w₀ hw₀ hgz
  rw [hxz] at hT
  have hq4 : ρ i / (400 * ρ i) = 1 / 400 := by field_simp
  rw [hq4] at hT
  have hyjb : (ρ j)⁻¹ * dist y j < (β 1)⁻¹ := by linarith
  have hzjb : (ρ j)⁻¹ * dist z j < (β 1)⁻¹ := by
    have h1 := dist_triangle z x j
    rw [dist_comm z x] at h1
    have h2 : dist z j < ρ j * (500 + 91 / 100 * (10 ^ 6 * Δ)) := by nlinarith
    have := (inv_mul_lt_iff₀ hrj).mpr h2
    linarith
  have hco := slim_raw_coarse_KA5_BAUGP P hj hyjb hzjb
  rw [dist_comm y z, hzy] at hco
  have h4 : (ρ j)⁻¹ * (400 * ρ i) = 400 * (ρ i / ρ j) := by field_simp
  have hdd : (ρ j)⁻¹ * (dist x y - 400 * ρ i) ≤
      10 * (10 ^ 6 * Δ) + 3 * β 1 - 400 * (ρ i / ρ j) := by
    rw [mul_sub, h4]
    linarith [(abs_le.mp hdxy).2]
  have hgz' : 400 * (ρ i / ρ j) - 6 * β 1 ≤
      slimRaw_KA3_BAUGP P j z - slimRaw_KA3_BAUGP P j x := by
    linarith [(abs_lt.mp hlift).1, (abs_le.mp hco).2]
  have hs0 : 0 ≤ ρ j / ρ i := (div_pos hrj hri).le
  have h5 : (ρ j / ρ i) * (400 * (ρ i / ρ j)) = 400 := by field_simp
  have hgain : 400 - 6 * (ρ j / ρ i) * β 1 ≤ (ρ j / ρ i) *
      (slimRaw_KA3_BAUGP P j z - slimRaw_KA3_BAUGP P j x) := by
    have := mul_le_mul_of_nonneg_left hgz' hs0
    rw [mul_sub, h5] at this
    linarith
  have hR := rank_one_reference_side_KA4 A hA (hTR z (by linarith)) (hTR x (by linarith)) hgain hT
  have hsb : 6 * (ρ j / ρ i) * β 1 ≤ 400 * β 1 := by
    have : ρ j / ρ i ≤ 101 / 100 := hs2.le
    nlinarith
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have h6 : 1 - β 1 - E₀ ≤ (400 - 6 * (ρ j / ρ i) * β 1 - 2 * E₀) / 400 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  linarith

/-- **TCP03, slim block saturation** (its own raw-axis lift of length `10L`, the point `z` at
reference distance `400` on the long minimizing segment, FC22). At `x ∈ D_i` with
`x ∈ B(j, (.91L + 40)ρ(j))`, for a listed slim chart `j` (ratio in `(.99, 1.01)`, `Δ ≥ 1`,
`0 < σ_s ≤ 1/12`, `β₁ ≤ 1/(100L)`) with (TR) `|s u_j e₀ − A u_i − s u_j(i) e₀| < E₀` on
`B(i, 1000ρ(i))`, some `g`-unit `w₀` has `ρ(j) dη_j(w₀) ≥ 1 − ε` and `(A(ρ(i) dη_i(w₀)))₀ ≥ 1 − ε`,
`ε = γ + σ_s + E₀ + β₁`. -/
theorem slim_component_saturation_KA5_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈ P.slim.centres)
    (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100)) {x : X} (hx : x ∈ ball i (10 * ρ i))
    (hxj : x ∈ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j)) (hΔ : 1 ≤ Δ)
    (hσs : 0 < σs) (hσs12 : σs ≤ 1 / 12) (hb : β 1 ≤ 1 / (100 * (10 ^ 6 * Δ)))
    {E₀ : ℝ} (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P j z) -
        A (circleRaw_KA3_BAUGP P i z) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P j i)‖ < E₀) :
    ∃ w₀ : TangentSpace 𝓘(ℝ, E3) x, g.inner x w₀ w₀ = 1 ∧
      1 - (γ + σs + E₀ + β 1) ≤ ρ j * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x w₀ ∧
      1 - (γ + σs + E₀ + β 1) ≤
        A (ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w₀) 0 := by
  have hri := hρ i
  have hrj := hρ j
  have hrj2 : 99 / 100 * ρ i < ρ j := by have := hs.1; rwa [lt_div_iff₀ hri] at this
  have hγ0 := circle_quality_nonneg_KA4_BAUGP P hi
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hbpos : 0 < β 1 := by
    let Sj := P.slim.centre j hj
    let _ := Sj.instZ
    exact @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ Sj.split
  have hΔ0 : 0 < Δ := by linarith
  set Lr : ℝ := 10 ^ 6 * Δ with hLr
  have hL : 1000000 ≤ Lr := by rw [hLr]; linarith
  have hbinv : 100 * Lr ≤ (β 1)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hbpos]
    rwa [one_div] at hb
  have hb1 : β 1 ≤ 1 / 1000 := hb.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hxjd : dist x j < (91 / 100 * Lr + 4 * 10) * ρ j := mem_ball.mp hxj
  obtain ⟨y, hdxy, hlift, hyj⟩ := slim_lift_KA5_BAUGP P hj (t := 10 * Lr) hxjd
    (by positivity) (by linarith)
  have hD1 : (10 * Lr - 3 * β 1) * ρ j ≤ dist x y := by
    have h' : 10 * Lr - 3 * β 1 ≤ (ρ j)⁻¹ * dist x y := by linarith [(abs_le.mp hdxy).1]
    have := (le_inv_mul_iff₀ hrj).mp h'
    linarith
  have hD2 : dist x y ≤ (10 * Lr + 3 * β 1) * ρ j := by
    have h' : (ρ j)⁻¹ * dist x y ≤ 10 * Lr + 3 * β 1 := by linarith [(abs_le.mp hdxy).2]
    have := (inv_mul_le_iff₀ hrj).mp h'
    linarith
  have hDpos : 0 < dist x y := lt_of_lt_of_le (by nlinarith) hD1
  have hxy : x ≠ y := fun h => by rw [h, dist_self] at hDpos; exact lt_irrefl _ hDpos
  have h400 : 400 * ρ i ≤ dist x y := by nlinarith
  obtain ⟨w₀, hw₀, hseg⟩ := exists_scaled_minimizing_seg_KA4_BAUGP g hmetric hxy
  obtain ⟨z, hxz, hzy, hgz⟩ := hseg (400 * ρ i) (by positivity) h400
  obtain ⟨y', -, hy'y, hgy⟩ := hseg (dist x y) dist_nonneg le_rfl
  have hyy : y' = y := dist_le_zero.mp (by linarith)
  rw [hyy] at hgy
  have hxL : x ∈ ball j (Lr * ρ j) := by rw [mem_ball]; nlinarith
  have hyL : y ∈ ball j (Lr / σs * ρ j) := by
    rw [mem_ball]
    have h12 : 12 * Lr ≤ Lr / σs := by
      rw [le_div_iff₀ hσs]
      nlinarith
    have h' : (ρ j)⁻¹ * dist y j < Lr / σs := by linarith
    have := (inv_mul_lt_iff₀ hrj).mp h'
    linarith
  have hown := slim_own_side_KA5_BAUGP P hj hxL hyL hΔ hbpos hb1 hD1 hD2 hlift w₀
    hw₀ hgy
  have href := slim_reference_side_KA5_BAUGP P hi hj hs hx hxjd hΔ hbinv hbpos.le hb1 hdxy hyj
      hlift hxz
    hzy w₀ hw₀ hgz A hA hTR
  exact ⟨w₀, hw₀, by linarith, by linarith⟩

/-- **TCP03, slim derivative clause** (FC15 with `k = 1` on the normalized tangent space of
`ρ(i)⁻² g`): under the hypotheses of `slim_component_saturation_KA5_BAUGP`, with
`ε = γ + σ_s + E₀ + β₁`, every tangent vector `w` at `x` has
`‖s dη_j(w) e₀ − A dη_i(w)‖ ≤ 2√(4ε + ε²) · √(ρ(i)⁻² g(w, w))`. -/
theorem slim_derivative_comparison_KA5_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈ P.slim.centres)
    (hs : ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100)) {x : X} (hx : x ∈ ball i (10 * ρ i))
    (hxj : x ∈ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j)) (hΔ : 1 ≤ Δ)
    (hσs : 0 < σs) (hσs12 : σs ≤ 1 / 12) (hb : β 1 ≤ 1 / (100 * (10 ^ 6 * Δ)))
    {E₀ : ℝ} (A : ℝ² →L[ℝ] ℝ¹)
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ∀ z, dist z i < 1000 * ρ i →
      ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P j z) -
        A (circleRaw_KA3_BAUGP P i z) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P j i)‖ < E₀)
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    ‖(ρ j / ρ i) • EuclideanSpace.single 0
          (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x w) -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w)‖ ≤
      2 * Real.sqrt (4 * (γ + σs + E₀ + β 1) + (γ + σs + E₀ + β 1) ^ 2) *
        Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hrj := hρ j
  let _ := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr hri)
  have hnorm : ∀ v : TangentSpace 𝓘(ℝ, E3) x, ‖v‖ = Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) :=
    norm_tangent_radialScaled_KA4 g hri x
  have hγ0 := circle_quality_nonneg_KA4_BAUGP P hi
  have hE0 : 0 ≤ E₀ := by
    have := hTR i (by rw [dist_self]; positivity)
    exact (norm_nonneg _).trans this.le
  have hbpos : 0 < β 1 := by
    let Sj := P.slim.centre j hj
    let _ := Sj.instZ
    exact @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hrj)) _ _ _ _ Sj.split
  set ε' := γ + σs + E₀ + β 1 with hε'
  have hε0 : 0 ≤ ε' := by positivity
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; linarith
  have hxL : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by
    rw [mem_ball]; have := mem_ball.mp hxj; nlinarith
  set f : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ¹ := (ρ j / ρ i) •
    (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x).smulRight
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) with hfdef
  set gg : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ² :=
    mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x with hgdef
  have hfv : ∀ v, f v = (ρ j / ρ i) • EuclideanSpace.single 0
      (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x v) := fun v => by
    rw [hfdef, smul_apply, smulRight_single_apply_KA4]
  have hlipd : ∀ v, |mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x v| ≤
      (1 + σs) * (ρ j)⁻¹ * Real.sqrt (g.inner x v v) := fun v =>
    (P.slim.centre j hj).abs_mvfderiv_le_SGP2_BAUGP hσs.le hxL v
  have hrows : ∀ a : Fin 1, ‖(EuclideanSpace.proj a : StrongDual ℝ ℝ¹).comp f‖ ≤ 1 + ε' := by
    intro a
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hfa : ((EuclideanSpace.proj a : StrongDual ℝ ℝ¹).comp f) v =
        (ρ j / ρ i) * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x v := by
      fin_cases a
      change (f v) 0 = _
      rw [hfv]
      simp
    rw [hfa, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hrj hri), hnorm v]
    have hsq : (ρ j / ρ i) * ((1 + σs) * (ρ j)⁻¹ * Real.sqrt (g.inner x v v)) =
        (1 + σs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
      field_simp
    have hv0 := Real.sqrt_nonneg ((ρ i)⁻¹ ^ 2 * g.inner x v v)
    calc ρ j / ρ i * |mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x v|
        ≤ ρ j / ρ i * ((1 + σs) * (ρ j)⁻¹ * Real.sqrt (g.inner x v v)) :=
          mul_le_mul_of_nonneg_left (hlipd v) (div_pos hrj hri).le
      _ = (1 + σs) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := hsq
      _ ≤ (1 + ε') * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
          have : 1 + σs ≤ 1 + ε' := by linarith
          exact mul_le_mul_of_nonneg_right this hv0
  have hgb : ‖gg‖ ≤ 1 + ε' := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have h := circleAdapted_gram_upper_KA2_BAUGP P hγ0 hi hxi v
    rw [hnorm v]
    have hv0 := Real.sqrt_nonneg ((ρ i)⁻¹ ^ 2 * g.inner x v v)
    calc ‖gg v‖ ≤ (1 + γ) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := h
      _ ≤ (1 + ε') * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x v v) := by
          have : 1 + γ ≤ 1 + ε' := by linarith
          exact mul_le_mul_of_nonneg_right this hv0
  have htests : ∀ a : Fin 1, ∃ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖w‖ = 1 ∧ 1 - ε' ≤ f w a ∧ 1 - ε' ≤ A (gg w) a := by
    intro a
    obtain ⟨w₀, hw₀, h1, h2⟩ := slim_component_saturation_KA5_BAUGP P hi hj hs hx hxj hΔ hσs hσs12
        hb
      A hA hTR
    refine ⟨ρ i • w₀, ?_, ?_, ?_⟩
    · rw [hnorm, gInner_smul_self, hw₀]
      have : (ρ i)⁻¹ ^ 2 * (ρ i ^ 2 * 1) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    · fin_cases a
      change 1 - ε' ≤ (f (ρ i • w₀)) 0
      rw [hfv, map_smul, smul_eq_mul]
      have he : ((ρ j / ρ i) • EuclideanSpace.single (0 : Fin 1)
          (ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x w₀) : ℝ¹) 0 =
          ρ j * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x w₀ := by
        simp
        field_simp
      rw [he]
      exact h1
    · fin_cases a
      have hge : gg (ρ i • w₀) =
          ρ i • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w₀ := map_smul _ _ _
      change 1 - ε' ≤ A (gg (ρ i • w₀)) 0
      rw [hge]
      exact h2
  have hR := DifferentialGeometry.Geometry.Fibration.norm_difference_of_common_directions f gg A hA
    hε0 hrows hgb htests
  have hw := (f - A.comp gg).le_opNorm w
  rw [hnorm w] at hw
  have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hcast, one_mul] at hR
  have hfw : (f - A.comp gg) w = (ρ j / ρ i) • EuclideanSpace.single 0
      (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x w) -
        A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P i hi) x w) := by
    rw [sub_apply, hfv]
    rfl
  rw [← hfw]
  exact hw.trans (mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg _))

/-- The slim value error of the value-tolerance family (field `slim_value`): `|η_j − u_j| < v_s`
on `B(j, 10⁶Δρ(j))`. -/
theorem slim_value_KA5_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ P.slim.centres) {x : X} (hx : x ∈ ball j (10 ^ 6 * Δ
            * ρ j)) :
    |(P.slim.centre j hj).coord_BCG2 x - slimRaw_KA3_BAUGP P.toLocalPacketsOnB j x| < vs := by
  rw [slimRaw_KA3_eq_BAUGP P.toLocalPacketsOnB hj]
  exact P.slim_value j hj x hx

/-- **TCP03, slim value clause**: `|s η_j(x) e₀ − A η_i(x) − s u_j(i) e₀| < s v_s + E₀ + γ` from the
slim value tolerance (`slim_value`), the circle adaptation error and (TR) at `x`. -/
theorem slim_value_comparison_KA5_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (hγ : 0 ≤ γ) {i j : X} (hi : i ∈ P.circle.centres) (hj : j ∈
            P.slim.centres) {x : X}
    (hx : x ∈ ball i (10 * ρ i)) (hxL : x ∈ ball j (10 ^ 6 * Δ * ρ j)) {E₀ : ℝ}
    (A : ℝ² →L[ℝ] ℝ¹) (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (hTR : ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j x) -
        A (circleRaw_KA3_BAUGP P.toLocalPacketsOnB i x) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j i)‖ < E₀) :
    ‖(ρ j / ρ i) • EuclideanSpace.single 0 ((P.slim.centre j hj).coord_BCG2 x) -
        A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j i)‖ <
      ρ j / ρ i * vs + E₀ + γ := by
  let P' := P.toLocalPacketsOnB
  have hxi : x ∈ ball i (200 * ρ i) := by
    rw [mem_ball]; have := mem_ball.mp hx; have := hρ i; linarith
  have hvj := slim_value_KA5_BAUGP P hj hxL
  have hvi : ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP P' i x‖ <
      γ := by
    have h := (circleAdapted_physical_KA2_BAUGP P' hγ hi).1 x hxi
    rw [circleRaw_KA3_eq_BAUGP P' hi]
    exact h
  have hs0 : 0 < ρ j / ρ i := div_pos (hρ j) (hρ i)
  have hAn := DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one A hA
  set uj := slimRaw_KA3_BAUGP P.toLocalPacketsOnB j
  set ηj := (P.slim.centre j hj).coord_BCG2
  have hdec : (ρ j / ρ i) • EuclideanSpace.single 0 (ηj x) -
      A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (uj i) =
      (ρ j / ρ i) • EuclideanSpace.single 0 (ηj x - uj x) +
        ((ρ j / ρ i) • EuclideanSpace.single 0 (uj x) - A (circleRaw_KA3_BAUGP P' i x) -
          (ρ j / ρ i) • EuclideanSpace.single 0 (uj i)) -
        A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP P' i x) := by
    have hsub : (EuclideanSpace.single 0 (ηj x - uj x) : ℝ¹) =
        EuclideanSpace.single 0 (ηj x) - EuclideanSpace.single 0 (uj x) :=
      PiLp.single_sub 2 (0 : Fin 1)
    rw [map_sub, hsub, smul_sub]
    abel
  rw [hdec]
  have h3 : ‖A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP P' i x)‖ <
      γ := by
    refine lt_of_le_of_lt ?_ hvi
    have := A.le_opNorm (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP P' i
        x)
    nlinarith [norm_nonneg (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP
        P' i x)]
  have h1 : ‖(ρ j / ρ i) • (EuclideanSpace.single 0 (ηj x - uj x) : ℝ¹)‖ ≤ ρ j / ρ i * vs := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, PiLp.norm_single, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hvj.le hs0.le
  calc _ ≤ ‖(ρ j / ρ i) • (EuclideanSpace.single 0 (ηj x - uj x) : ℝ¹) +
        ((ρ j / ρ i) • EuclideanSpace.single 0 (uj x) - A (circleRaw_KA3_BAUGP P' i x) -
          (ρ j / ρ i) • EuclideanSpace.single 0 (uj i))‖ +
        ‖A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP P' i x)‖ :=
            norm_sub_le _ _
    _ ≤ (‖(ρ j / ρ i) • (EuclideanSpace.single 0 (ηj x - uj x) : ℝ¹)‖ +
        ‖(ρ j / ρ i) • EuclideanSpace.single 0 (uj x) - A (circleRaw_KA3_BAUGP P' i x) -
          (ρ j / ρ i) • EuclideanSpace.single 0 (uj i)‖) +
        ‖A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x - circleRaw_KA3_BAUGP P' i x)‖ := by
        gcongr; exact norm_add_le _ _
    _ < ρ j / ρ i * vs + E₀ + γ := by linarith

/-- **TCP03 (slim blocks)** (`lem:fibration-first-constant-comparison`, B:5370) on the
value-tolerance family `LocalChartPacketsRV … vs`: for an early `0 < θ < 1` (and `ν`,
`3ν ≤ β₃ < 1`) there are an early `σ` and an early circle adaptation bound `γ₀`, and for every
`Δ ≥ 1` a later slim splitting bound `η₁(Δ)`, such that, with FC07's parameter ranges, `3β₂ ≤ σ`,
`γ ≤ γ₀`, `β₁ ≤ η₁`, the later slim quality `0 < σ_s ≤ θ²/1000`, the slim value tolerance
`v_s ≤ θ/100` and `σ⁻¹ ≤ Lmax`: at every circle centre `i`, every listed slim chart `j` (closed
support meeting `D_i`) has ONE coisometry `A_j : ℝ² → ℝ¹` with TCP02's (TR) at accuracy `θ²/2000`
on `B(i, 1000ρ(i))` and (TC) on `D_i` for the SAME smooth coordinates (rank one as `t e₀`):
value `≤ θ/2` and differential `≤ (θ/2)|w|` in the norm of `ρ(i)⁻² g`. -/
theorem tcp03_slim_row_BAUGP {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
          vs ζ Λz U₁ U₂ Ue₁ Ue₂),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → γ ≤ γ₀ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 →
      vs ≤ θ / 100 → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres), ∀ j (hj : j ∈ P.slim.centres),
        (tsupport (P.slim.cutoff_BCNT j) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
          (∀ x, dist x i < 1000 * ρ i →
            ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j x) -
              A (circleRaw_KA3_BAUGP P.toLocalPacketsOnB
                i x) -
              (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j i)‖ <
              θ ^ 2 / 2000) ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖(ρ j / ρ i) • EuclideanSpace.single 0 ((P.slim.centre j hj).coord_BCG2 x) -
                A (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j i)‖ ≤
              θ / 2 ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ j / ρ i) • EuclideanSpace.single 0
                    (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord_BCG2 x w) -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi) x w)‖ ≤
                θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hE₀ : (0 : ℝ) < θ ^ 2 / 2000 := by positivity
  obtain ⟨σ₁, hσ₁, hσ₁1, h1⟩ := tcp02_pair_complete_BCG1 hE₀ hν hν1 (j := 1) le_rfl one_le_two
  refine ⟨σ₁, hσ₁, hσ₁1, θ ^ 2 / 1000, by positivity, fun Δ hΔ => ?_⟩
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨η, hη, hk1⟩ := h1 (10 + 2 * (91 / 100 * (10 ^ 6 * Δ))) (by positivity)
  refine ⟨min η (min (θ ^ 2 / 2000) (1 / (100 * (10 ^ 6 * Δ)))),
    lt_min hη (lt_min hE₀ (by positivity)), ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz U₁
      U₂ Ue₁ Ue₂ P hΛ hμ
    hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hγ hb hσs hσsθ hvs hσL i hi j hj hmeet
  let P' := P.toLocalPacketsOnB
  have hγ0 := circle_quality_nonneg_KA4_BAUGP P' hi
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hbη : β 1 ≤ η := hb.trans (min_le_left _ _)
  have hbθ : β 1 ≤ θ ^ 2 / 2000 := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbΔ : β 1 ≤ 1 / (100 * (10 ^ 6 * Δ)) :=
    hb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hσs12 : σs ≤ 1 / 12 := hσsθ.trans (by nlinarith)
  have hsec₁ := tcp02_sectional_KA3_BAUGP P' hσ₁ (by linarith) hσL i (P'.circle.centres_subset hi).1
  have hno := circle_no_three_KA3_BAUGP P'.circle hi hν3 hβ3
  obtain ⟨-, -, hslim, -, -, -⟩ := fc07_input_packet_BAUGP P' hΛ (by linarith) hμ hτ hLΛ hLmax he
      hT i
  obtain ⟨-, hratio, hdist, hsub1, -, -⟩ := hslim j hj hmeet
  obtain ⟨-, -, hS1, -, -⟩ := tcp01_row_BAUGP P' hΛ (by linarith) hμ hτ hLΛ hLmax he hT hγ0 hi
  obtain ⟨hs, -⟩ := hS1 j hj hmeet
  let Ai := P'.circleAdapted i hi
  let Sj := P'.slim.centre j hj
  let _ := Sj.instZ
  obtain ⟨f, hf⟩ := exists_finOne_split_KA3 Sj.split
  obtain ⟨A, hA, hal⟩ := @hk1 X mX _ _ _ _ g hmetric i j (ρ i) (ρ j) (hρ i) (hρ j) hratio.1
    hratio.2 (by rw [dist_comm]; linarith) hsec₁ hno Sj.Z Ai.Y Sj.instZ Ai.instY Sj.z Ai.a (β 1)
    (β 2) hbη hβ2σ f Ai.split
  have hTR : ∀ x, dist x i < 1000 * ρ i →
      ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j x) -
        A (circleRaw_KA3_BAUGP P' i x) -
        (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3_BAUGP P.toLocalPacketsOnB j i)‖ <
        θ ^ 2 / 2000 := by
    intro x hx
    rw [circleRaw_KA3_eq_BAUGP P' hi, slimRaw_KA3_eq_BAUGP P.toLocalPacketsOnB hj,
      slimRaw_KA3_eq_BAUGP P.toLocalPacketsOnB hj]
    have h := hal x hx
    rw [hf x, hf i] at h
    exact h
  refine ⟨A, hA, hTR, fun x hx => ⟨?_, fun w => ?_⟩⟩
  · have hxj : x ∈ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) := hsub1 hx
    have hxL : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by
      rw [mem_ball]; have := mem_ball.mp hxj; have := hρ j; nlinarith
    have hv := slim_value_comparison_KA5_BAUGP P hγ0 hi hj hx hxL A hA
      (hTR x (by have := mem_ball.mp hx; have := hρ i; linarith))
    have hs2 : ρ j / ρ i < 101 / 100 := hs.2
    have hs0 : 0 ≤ ρ j / ρ i := (div_pos (hρ j) (hρ i)).le
    have hvs0 : 0 ≤ vs := by
      have := slim_value_KA5_BAUGP P hj (mem_ball_self (by have := hρ j; positivity))
      exact (abs_nonneg _).trans this.le
    have : ρ j / ρ i * vs ≤ 101 / 100 * (θ / 100) := by
      nlinarith
    linarith
  · have hxj : x ∈ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * 10) * ρ j) := hsub1 hx
    have hd := slim_derivative_comparison_KA5_BAUGP P' hi hj hs hx hxj hΔ hσs hσs12 hbΔ A hA hTR w
    set ε' := γ + σs + θ ^ 2 / 2000 + β 1 with hε'
    have hbpos : 0 < β 1 :=
      @KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _ Sj.split
    have hε0 : 0 ≤ ε' := by positivity
    have hbud := riesz_budget_KA4 hθ hθ1 (ε := ε') hε0 (by linarith)
    have hmono : 2 * Real.sqrt (4 * ε' + ε' ^ 2) ≤ 2 * Real.sqrt (2 * (4 * ε' + ε' ^ 2)) := by
      have : 4 * ε' + ε' ^ 2 ≤ 2 * (4 * ε' + ε' ^ 2) := by nlinarith
      have := Real.sqrt_le_sqrt this
      linarith
    exact hd.trans (mul_le_mul_of_nonneg_right (hmono.trans hbud) (Real.sqrt_nonneg _))


end DifferentialGeometry.Geometry.Collapse
