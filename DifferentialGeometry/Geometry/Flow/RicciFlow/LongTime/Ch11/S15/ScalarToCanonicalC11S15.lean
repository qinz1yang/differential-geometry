import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A

set_option autoImplicit false

/-!
# S-CH11-S15 G1：S8（larger-ball scalar control）+ canonical supply ⇒ P6 (b) late 形（`_C11S15`）

`LargerBallScalarLargeSupply_C11S`（S8）是 KL 84.1 **(c)**：`B(p, A r)` 上 `R ≤ K r⁻²`（"Large"
指 `A > 1`，不是 "scalar large"）。(b) 要的是反方向：`R ≥ K₁ r⁻²` 的点有带 neck chart 的
canonical witness。所以 S8 对 (b) 的作用是**空真**，canonical supply
（`HistoryCanonicalSupply_C11S F ρ`：`R > ρ(t)⁻²` 的点有 witness）覆盖 `R > ρ(t)⁻²` 的点。

固定 `A > 0`，S8 在 `A` 处给 `r̄, K`（`∃`）。取 `K₁ ≥ K + 1`、`T ≥ A`（`T ≥ A` 时 S7 给出 S8 的
accuracy 前提，`accuracy_on_late_half_P6A`），对晚期 `t ≥ T`、`2r² < t`、小抛物曲率、体积
`≥ A⁻¹ r³`、`y ∈ B(p, A r)`、`R(y) ≥ K₁ r⁻²`，分三种情形：
* `R(y) > ρ(t)⁻²`：canonical supply 直接给 witness（任意 `r`）；
* `R(y) ≤ ρ(t)⁻²` 且 `r ≤ r̄√t`：S8 给 `R(y) ≤ K r⁻² < K₁ r⁻²`，矛盾（空真）；
* `R(y) ≤ ρ(t)⁻²` 且 `r̄√t < r`：**缺口形 band**——`K₁ r⁻² ≤ R(y) ≤ ρ(t)⁻²`、`r̄√t < r < √(t/2)`
  的点。这正是 KL 84.1(b) 的实质内容（design-C11-P6 L4 的坏点区间 `Q ≤ ρ(t)⁻²`），树内不可推
  （`R ≥ K₁ r⁻² ≥ 2K₁ / t` 远小于 `ρ(t)⁻²`，canonical supply 不覆盖；S8 要 `r ≤ r̄√t`），
  写成显式前提 `hband`。

**诚实边界**：本文件**不证** (b)；只证 "(b) ⇐ S8 + canonical supply + band"。band 前提只含
`r̄√t < r`（S8 的 `r̄` 由 S8 给出，故结论写成 `∃ rbar, 0 < rbar ∧ (band rbar → (b))`），
所以它严格窄于 "(b) 对全部 `r`"，且不依赖 (c)——但 S8 本身（(c)）的证明在 P6 线里用到 (b)
（`S8WireC11V4` 的 `hspine`），二者不能同时被当作已证的循环输入，这是 P6 线的事。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1**：S8 在 `A` 处（`r̄, K`）+ S7 + canonical supply ⇒ 存在 `r̄ > 0`（S8 给的），使得
band 前提（`r̄√t < r`、`K₁ r⁻² ≤ R(y) ≤ ρ(t)⁻²` 的点有 neck-chart witness）⇒ P6 (b) late 形。
band 之外（`R > ρ⁻²`、`r ≤ r̄√t`）由 canonical supply 与 S8 空真给出。 -/
theorem largerBallCanonicalLate_of_scalarLarge_C11S15 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ ρ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {ε C1 C2 A : ℝ} (hacc : LargerBallAccuracySupply_C11S δ α) (hA : 0 < A)
    (hS8 : LargerBallScalarAt_C11S F δ α A)
    (hcanon : HistoryCanonicalSupply_C11S F ρ ε C1 C2) :
    ∃ rbar : ℝ, 0 < rbar ∧
      ((∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → rbar * Real.sqrt t < r → 2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
            K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
            metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ (ρ t ^ 2)⁻¹ →
            ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
              W.capTubeHasNeckChart ε) →
        LargerBallCanonicalLateAt_P6A F ε C1 C2 A) := by
  obtain ⟨rbar, K, hrbar, hK, hbody⟩ := hS8
  refine ⟨rbar, hrbar, ?_⟩
  rintro ⟨K₁, T, hK₁, hT, hband⟩
  refine ⟨max K₁ (K + 1), max T A, lt_max_of_lt_left hK₁, lt_max_of_lt_left hT, ?_⟩
  intro n H t p r hTt h2 hsmall hvol y hy hKy
  have hr : 0 < r := hsmall.1
  have hinv : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  by_cases hρ : (ρ t ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage t) t) y
  · exact hcanon n t y hρ
  · have hρ' := not_lt.mp hρ
    have hKy' : K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hinv.le).trans hKy
    by_cases hrs : r ≤ rbar * Real.sqrt t
    · exfalso
      have hlate := accuracy_on_late_half_P6A hacc hA ((le_max_right T A).trans hTt)
      have hbd := hbody n t p r h2 hlate hsmall hvol hrs y hy
      have hK1 : (K + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y :=
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hinv.le).trans hKy
      nlinarith
    · exact hband n t p r ((le_max_left T A).trans hTt) (not_le.mp hrs) h2 hsmall hvol y hy
        hKy' hρ'

end GC.LongTime.Ch11
