import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StageBallVolumeRatio
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

/-!
# S-CH11-SMALLVOL G2：Bishop–Gromov 适配合同（后缀 `_C11V`）

外审 R-C11-2 Q3.1 / D-R-C11-2-10 的"可独立证明的 BG 适配合同"：非 round 的
`SpatialCanonicalWitness`（尺度 `Q = R(x)`）+ 新增前提 `Ric ≥ −2KQ g` 于
`B(x, 2C₁Q^{-1/2})` ⇒ `Vol B(x, ϱ) ≥ c(K, C₁, C₂) ϱ³`（`0 < ϱ ≤ Q^{-1/2}`）。

* 树内有完整 BG（`riemannianBallOf_volume_ratio_ge_of_ricci_lower`，
  `Comparison/Volume/Bishop/LocalBallRatio.lean:57`），所以 **不需要** 显式前提 `hBG`；
  `OrientedThreeStage` 紧致，`RiemannianMetricComplete.of_compact` 给完备性。
* 体积来源是 witness 的 `volume` 字段（只在 `alternative.requiresVolume` 时有；round 分支
  `requiresVolume = False`，见 `not_requiresVolume_of_round_C11V`）+ `inside_ball` + `radius_upper`。
* `rm_bound` 只在 `domain` 上，所以 `Ric ≥ −2KQ g` 于较大的比较球 `B(x, 2C₁Q^{-1/2})` 是**新增前提**
  `hRic`（审稿原话）；本文件不从 `rm_bound` 推它。
* 常数：`c(K, C₁, C₂) = exp(−4 C₁ √K) / (64 C₁³ C₂)`，与 `Q` 无关。
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- **BG 适配合同（宽形）**：非 round witness（`requiresVolume`）+ `Ric ≥ −2KQ g` 于
`B(x, 2C₁/√Q)` ⇒ 所有 `0 < ϱ ≤ 2C₁/√Q` 有 `c ϱ³ ≤ Vol B(x, ϱ)`，`c = e^{-4C₁√K}/(64 C₁³ C₂)`。 -/
theorem vol_ball_ge_of_nonround_witness_wide_C11V {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps C1 C2 K : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hnr : W.alternative.requiresVolume) (hK : 0 ≤ K)
    (hRic : ∀ y ∈ riemannianBallOf g x (2 * C1 / Real.sqrt (metricScalarAt g x)),
      ∀ v : TangentSpace ThreeModel y,
        -(2 * K * metricScalarAt g x) * g.inner y v v ≤ ricciTensor (I := ThreeModel) g y v v)
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ 2 * C1 / Real.sqrt (metricScalarAt g x)) :
    ENNReal.ofReal (Real.exp (-(4 * C1 * Real.sqrt K)) / (64 * C1 ^ 3 * C2) * ρ ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := by
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := W.Q_pos
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hC1 : 1 ≤ C1 := by
    have h := W.radius_lower.trans W.radius_upper
    rw [← one_div, div_le_div_iff_of_pos_right hsQ] at h
    exact h
  have hC1pos : 0 < C1 := zero_lt_one.trans_le hC1
  set R : ℝ := 2 * C1 / Real.sqrt Q with hR
  have hRpos : 0 < R := by positivity
  have hdomain : W.domain.carrier ⊆ riemannianBallOf g x R := by
    refine W.inside_ball.trans (riemannianBallOf_mono g x ?_)
    have h := W.radius_upper
    rw [hR, mul_div_assoc]
    linarith
  have hvolR : ENNReal.ofReal (C2⁻¹ / (Q * Real.sqrt Q)) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x R) :=
    (W.volume hnr).trans (measure_mono hdomain)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hq : 0 ≤ Real.sqrt K * Real.sqrt Q := by positivity
  have hcoef : ((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * (Real.sqrt K * Real.sqrt Q) ^ 2 =
      2 * K * Q := by
    rw [hdim, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hQ.le]
    norm_num
    ring
  have hRic' : ∀ y ∈ riemannianBallOf g x R, ∀ v : TangentSpace ThreeModel y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * (Real.sqrt K * Real.sqrt Q) ^ 2) *
          g.inner y v v ≤ ricciTensor (I := ThreeModel) g y v v := by
    intro y hy v
    rw [hcoef]
    exact hRic y hy v
  have hmain :=
    Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower g
      (RiemannianMetricComplete.of_compact g) x hq hρ hρR hRic'
  rw [hdim] at hmain
  have h31 : ((3 - 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h31] at hmain
  have hexp : Real.sqrt K * Real.sqrt Q * 2 * R = 4 * C1 * Real.sqrt K := by
    rw [hR]
    field_simp
    ring
  have hQs : Q * Real.sqrt Q = Real.sqrt Q ^ 3 :=
    calc Q * Real.sqrt Q = Real.sqrt Q ^ 2 * Real.sqrt Q := by rw [hsq]
      _ = Real.sqrt Q ^ 3 := by ring
  have hid : Real.exp (-(Real.sqrt K * Real.sqrt Q * 2 * R)) * (ρ / (2 * R)) ^ 3 *
      (C2⁻¹ / (Q * Real.sqrt Q)) =
        Real.exp (-(4 * C1 * Real.sqrt K)) / (64 * C1 ^ 3 * C2) * ρ ^ 3 := by
    rw [hexp, hQs, hR]
    field_simp
    ring
  have hA : 0 ≤ Real.exp (-(Real.sqrt K * Real.sqrt Q * 2 * R)) * (ρ / (2 * R)) ^ 3 := by
    positivity
  calc ENNReal.ofReal (Real.exp (-(4 * C1 * Real.sqrt K)) / (64 * C1 ^ 3 * C2) * ρ ^ 3)
      = ENNReal.ofReal (Real.exp (-(Real.sqrt K * Real.sqrt Q * 2 * R)) * (ρ / (2 * R)) ^ 3) *
          ENNReal.ofReal (C2⁻¹ / (Q * Real.sqrt Q)) := by
        rw [← ENNReal.ofReal_mul hA, hid]
    _ ≤ ENNReal.ofReal (Real.exp (-(Real.sqrt K * Real.sqrt Q * 2 * R)) * (ρ / (2 * R)) ^ 3) *
          riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x R) :=
        mul_le_mul' le_rfl hvolR
    _ ≤ riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := hmain

/-- **BG 适配合同（审稿原形）**：`0 < ϱ ≤ Q^{-1/2}`。 -/
theorem vol_ball_ge_of_nonround_witness_C11V {P : OrientedThreeStage.{u}} {g : P.Metric}
    {x : P.Carrier} {eps C1 C2 K : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hnr : W.alternative.requiresVolume) (hK : 0 ≤ K)
    (hRic : ∀ y ∈ riemannianBallOf g x (2 * C1 / Real.sqrt (metricScalarAt g x)),
      ∀ v : TangentSpace ThreeModel y,
        -(2 * K * metricScalarAt g x) * g.inner y v v ≤ ricciTensor (I := ThreeModel) g y v v)
    {ρ : ℝ} (hρ : 0 < ρ) (hρQ : ρ ≤ (Real.sqrt (metricScalarAt g x))⁻¹) :
    ENNReal.ofReal (Real.exp (-(4 * C1 * Real.sqrt K)) / (64 * C1 ^ 3 * C2) * ρ ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := by
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
  have hC1 : 1 ≤ C1 := by
    have h := W.radius_lower.trans W.radius_upper
    rw [← one_div, div_le_div_iff_of_pos_right hsQ] at h
    exact h
  refine vol_ball_ge_of_nonround_witness_wide_C11V W hnr hK hRic hρ (hρQ.trans ?_)
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by linarith) hsQ.le

/-- **round 分支的前提不满足**：`.round` 的 `requiresVolume` 是 `False`，所以
`vol_ball_ge_of_nonround_witness_C11V` 的 `hnr` 不能被 round witness 提供（这不是对 round 分支的体积
下界的证伪——圆 lens space 反例见 R-C11-2 Q3.1——只是此适配合同不覆盖它）。 -/
theorem not_requiresVolume_of_round_C11V {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {g : SmoothRiemannianMetric ThreeModel M} {eps C : ℝ} {x : M} {U : Set M}
    (whole : U = connectedComponent x) (data : SpatialRoundComponent g eps x U) :
    ¬ (SpatialCanonicalAlternative.round (C := C) whole data).requiresVolume :=
  id

/-- consumer（round 不能喂入）：round witness 不满足 `hnr`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier} {eps C1 C2 : ℝ}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (whole : W.domain.carrier = connectedComponent x)
    (data : SpatialRoundComponent g eps x W.domain.carrier)
    (h : W.alternative = SpatialCanonicalAlternative.round whole data) :
    ¬ W.alternative.requiresVolume := by
  rw [h]
  exact id

/-- consumer（κ 形，P6B `ballVolume` 形）：非 round witness + `hRic` ⇒ 存在 `κ > 0` 使
`0 < ϱ ≤ Q^{-1/2}` 上 `κ ϱ³ ≤ ballVolume g x ϱ`。这是 P6B window 里小尺度 `hsmall` 的 witness 端
供给形（G3 adapter 的体积来源之一）。 -/
theorem exists_kappa_ballVolume_of_nonround_witness_C11V {P : OrientedThreeStage.{u}}
    {g : P.Metric} {x : P.Carrier} {eps C1 C2 K : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hnr : W.alternative.requiresVolume) (hK : 0 ≤ K)
    (hRic : ∀ y ∈ riemannianBallOf g x (2 * C1 / Real.sqrt (metricScalarAt g x)),
      ∀ v : TangentSpace ThreeModel y,
        -(2 * K * metricScalarAt g x) * g.inner y v v ≤ ricciTensor (I := ThreeModel) g y v v) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ (Real.sqrt (metricScalarAt g x))⁻¹ →
      ENNReal.ofReal (κ * ρ ^ 3) ≤ Geometry.Collapse.ballVolume g x ρ := by
  have hC1 : 1 ≤ C1 := by
    have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
    have h := W.radius_lower.trans W.radius_upper
    rw [← one_div, div_le_div_iff_of_pos_right hsQ] at h
    exact h
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  refine ⟨Real.exp (-(4 * C1 * Real.sqrt K)) / (64 * C1 ^ 3 * C2), by positivity, ?_⟩
  intro ρ hρ hρQ
  exact vol_ball_ge_of_nonround_witness_C11V W hnr hK hRic hρ hρQ

end GC.LongTime.Ch11
