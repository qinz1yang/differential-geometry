import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ims05EigenIM6
import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenfunctionComplex_EG

/-!
# c3 再收缩：S-W-EIG 的正第一特征函数接入，IMS05′ 只剩共形稳定性（O-W-IMS06 G6，后缀 `_IM6`）

G5 的 `hU`（`u`、`qq`、`μ` 的存在 + B̄ 上 `qq ≥ σ/2` + 特征方程）由下面三件给出：
* (3) `u`：S-W-EIG `exists_positive_first_eigenfunction_complex_EG`，`Ω = ball 0 ρ′`（`ρ′ < 1`，
  `B̄ ⊆ Ω`，`closure Ω ⊆ ball 0 1`），权 `ρ = lam`、势 `W = lam · VJ`；
* (2) `qq := K − VJ`（`K = −Δ log lam / (2 lam)`，平面共形曲率公式）；`VJ ≤ K − R/2`（S-W-STAB G3 的
  `VJ ≤ S_{gN}/2 − R/2` 在共形坐标下）+ B̄ 上 `R ≥ σ` ⇒ `qq ≥ R/2 ≥ σ/2`；
* 特征方程 `−Δu + lam VJ u = μ lam u` ⇔ `Δu = lam (K − qq − μ) u`（代数）。
剩下的显式前提只有共形坐标下的稳定性 `hstab`（EIG 的 `hstab` 形，对 `ball` 内任意开 `Ω`）、`VJ` 光滑与
`hVJle`——即 S-W-STAB-2 G1–G3（`IsMorreyDisk.planar_stability_WS2`，`_HC2` 实例在其 G3）的输出形状；
`‖fderiv φ‖² = (∂₁φ)² + (∂_Iφ)²` 与 `S_{gN}/2 = K` 的换写在收缩时补。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 平面共形曲率 `K = −Δ log lam / (2 lam)` 在开盘上连续（`lam` 光滑且正）。 -/
theorem continuousOn_conformalCurvature_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q)
    (himm : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)) :
    ContinuousOn (fun z => -Laplacian.laplacian
        (fun p => Real.log (diskConformalFactor_IM6 g q p)) z /
      (2 * diskConformalFactor_IM6 g q z)) (Metric.ball (0 : ℂ) 1) := by
  have hlam := contDiffOn_diskConformalFactor_IM6 g hq
  intro z hz
  have hpos := diskConformalFactor_pos_IM6 g (himm z hz)
  have hlog : ContDiffAt ℝ 2 (fun p => Real.log (diskConformalFactor_IM6 g q p)) z :=
    ((hlam.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).log hpos.ne').of_le (by simp)
  have hden : ContinuousAt (fun z => 2 * diskConformalFactor_IM6 g q z) z :=
    continuousAt_const.mul (hlam.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz))
  exact (hlog.continuousAt_laplacian.neg.div hden (by positivity)).continuousWithinAt

/-- **c3（再收缩版）**：开盘内光滑、共形、浸入的盘 + 共形坐标下的稳定性（`VJ` 光滑、
`VJ ≤ K − R/2`、`hstab`：EIG 形）⇒ S-W-NECK G4 的 `hIMS05`（`σ` 版）。 -/
theorem ims05_radius_bound_of_planarStability_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    (himm : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {σ : ℝ} (hσ : 0 < σ) (VJ : ℂ → ℝ)
    (hVJ : ContDiffOn ℝ (⊤ : ℕ∞) VJ (Metric.ball (0 : ℂ) 1))
    (hVJle : ∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤
      -Laplacian.laplacian (fun p => Real.log (diskConformalFactor_IM6 g q p)) z /
        (2 * diskConformalFactor_IM6 g q z) - metricScalarAt g (diskExtension q z) / 2)
    (hstab : ∀ Ω : Set ℂ, IsOpen Ω → Ω ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        0 ≤ (∫ z in Ω, ((fderiv ℝ φ z 1) ^ 2 + (fderiv ℝ φ z Complex.I) ^ 2)) +
          ∫ z in Ω, diskConformalFactor_IM6 g q z * VJ z * φ z ^ 2) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  refine ims05_radius_bound_of_eigen_IM6 g hq hconf himm hσ fun z₀ r h₀ hr hK hR => ?_
  set lam := diskConformalFactor_IM6 g q with hlamdef
  set Bb := {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r}
    with hBb
  have hz₀B : z₀ ∈ Bb := ⟨h₀, by rw [diskEDist_self_NK g q h₀]; exact zero_le⟩
  obtain ⟨z₁, hz₁, hmax⟩ := hK.exists_isMaxOn ⟨z₀, hz₀B⟩ continuous_norm.continuousOn
  have hz₁1 : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁.1
  set ρ' : ℝ := (‖z₁‖ + 1) / 2 with hρ'
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith [norm_nonneg z₁]
  have hBΩ : Bb ⊆ Metric.ball (0 : ℂ) ρ' := fun z hz =>
    mem_ball_zero_iff.mpr ((hmax hz).trans_lt (by rw [hρ']; linarith))
  have hΩb : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball hρ'1.le
  have hcl : closure (Metric.ball (0 : ℂ) ρ') ⊆ Metric.ball (0 : ℂ) 1 := by
    rw [closure_ball _ hρ'0.ne']
    exact Metric.closedBall_subset_ball hρ'1
  have hlam : ContDiffOn ℝ (⊤ : ℕ∞) lam (Metric.ball (0 : ℂ) 1) :=
    contDiffOn_diskConformalFactor_IM6 g hq
  obtain ⟨u, μ, hu, hu0, hμ, -, hpde, -⟩ := exists_positive_first_eigenfunction_complex_EG
    Metric.isOpen_ball Metric.isBounded_ball (convex_ball _ _).isPreconnected
    ⟨z₀, hBΩ hz₀B⟩ Metric.isOpen_ball hcl hlam (hlam.mul hVJ)
    (fun z hz => diskConformalFactor_pos_IM6 g (himm z (hcl hz)))
    (hstab _ Metric.isOpen_ball hΩb)
  have hKc := continuousOn_conformalCurvature_IM6 g hq himm
  refine ⟨Metric.ball (0 : ℂ) ρ', u, fun z => -Laplacian.laplacian
      (fun p => Real.log (lam p)) z / (2 * lam z) - VJ z, μ, Metric.isOpen_ball, hΩb, hBΩ, hu,
    hu0, (hKc.mono hΩb).sub (hVJ.continuousOn.mono hΩb), hμ, ?_, ?_⟩
  · intro z hz hd
    have hzb := hΩb hz
    have hdE : diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r :=
      (ENNReal.le_ofReal_iff_toReal_le (diskEDist_ne_top_IM6 g hq h₀ hzb) hr.le).mpr hd
    have hRz : σ ≤ metricScalarAt g (diskExtension q z) := (hR z hzb hdE).self_of_nhds
    have hle := hVJle z hzb
    simp only
    linarith
  · intro z hz _
    have h := hpde z hz
    simp only at h ⊢
    rw [show lam z * (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) -
        (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) - VJ z) - μ) * u z =
        lam z * VJ z * u z - μ * lam z * u z by ring]
    linarith

end GC.LongTime
