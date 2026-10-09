import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10ScaleSepCXJ10

/-!
# J10 的 surgery-scale 阈值障碍（CX-J10 G2，后缀 `_CXJ10`）

G1 把 J10 化成 scale separation `Θ_n < R^orig(σ_n, y_n)`。本文件说明 J9 阈值**不能**取 surgery 尺度
`ρ(T′)⁻²`（`ρ = q.neckRadius`，`T′ ≥ Tno`，例如 `T′ = (Ho n).horizon`，即 `TimeDerivativeSupply_C11E`
的阈值在整条 history 上的上确界）：冻结 hgapJ 前提 `R ≤ ((q.rescale_P6N c).neckRadius Tn ^ 2)⁻¹`
（`c·Tn = Tno`）+ `AntitoneOn ρ` ⇒ `¬ c · ρ(T′)⁻² < R`。故 J10 的 `Qs` 必须是严格低于 surgery 尺度的
canonical-neighborhood 阈值（P6WR 取 `qcanSup`），scale separation 是 `qcan` 带与 selected 曲率之间的
真实分离，不能由 ρ 阈值替代。

* `not_hJ10_neckThreshold_CXJ10`：标量形障碍。
* `not_hJ10_horizonNeck_CXJ10`：hOpen 形实例（`Tn := rescaleTime Tno`，`T′ := (Ho n).horizon`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **surgery 尺度阈值障碍**：`R ≤ ((q.rescale c).neckRadius Tn)⁻²`、`c·Tn ≤ T′`、`ρ` antitone ⇒
`¬ c · ρ(T′)⁻² < R`。 -/
theorem not_hJ10_neckThreshold_CXJ10 (q : CutoffParameters) (hρa : AntitoneOn q.neckRadius (Ici 0))
    {c Tn R T' : ℝ} (hc : 0 < c) (hTn : 0 ≤ Tn) (hT' : c * Tn ≤ T')
    (hQρ : R ≤ ((q.rescale_P6N c hc).neckRadius Tn ^ 2)⁻¹) :
    ¬ c * (q.neckRadius T' ^ 2)⁻¹ < R := by
  intro hlt
  have h0 : 0 ≤ c * Tn := mul_nonneg hc.le hTn
  have hρ0 : 0 < q.neckRadius (c * Tn) := q.neckRadius_pos _ h0
  have hρ1 : 0 < q.neckRadius T' := q.neckRadius_pos _ (h0.trans hT')
  have hanti : q.neckRadius T' ≤ q.neckRadius (c * Tn) :=
    hρa (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr (h0.trans hT')) hT'
  change R ≤ ((q.neckRadius (c * Tn) / Real.sqrt c) ^ 2)⁻¹ at hQρ
  rw [div_pow, Real.sq_sqrt hc.le, inv_div] at hQρ
  have hsq : q.neckRadius T' ^ 2 ≤ q.neckRadius (c * Tn) ^ 2 :=
    pow_le_pow_left₀ hρ1.le hanti 2
  have hinv : (q.neckRadius (c * Tn) ^ 2)⁻¹ ≤ (q.neckRadius T' ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hρ1 2) hsq
  have h1 : c / q.neckRadius (c * Tn) ^ 2 ≤ c * (q.neckRadius T' ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hc.le
  linarith

/-- hOpen 形实例：`Tn := rescaleTime Tno`、`T′ := (Ho).horizon`，阈值 `ρ(horizon)⁻²` 不满足 J10。 -/
theorem not_hJ10_horizonNeck_CXJ10 (q : CutoffParameters) (hρa : AntitoneOn q.neckRadius (Ici 0))
    (Ho : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c) (Tno : Icc (0 : ℝ) Ho.toHistory.horizon)
    {R : ℝ} (hQρ : R ≤ ((q.rescale_P6N c hc).neckRadius (Ho.rescaleTime_P6X hc Tno) ^ 2)⁻¹) :
    ¬ c * (q.neckRadius Ho.horizon ^ 2)⁻¹ < R := by
  refine not_hJ10_neckThreshold_CXJ10 q hρa hc (div_nonneg Tno.2.1 hc.le) ?_ hQρ
  rw [mul_div_cancel₀ _ hc.ne']
  exact Tno.2.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
