import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

set_option autoImplicit false

/-!
# born patch 的 no-straddling（O-CH11-NATIVE-BORN G1 = SL2-c-i，后缀 `_C11SP`）

hBorn（`P6NativeNJSlotV2C11SP` 的 binder）的第一个引理。born 点 `x*` 在 birth 时刻 `u = time e.succ`
落在 `(records e).static b` 的内窗 `window z*`，`‖z*‖ ≤ Z`（native 用 `Z = transitionEnd + 10`）。
若 `q` 与 `window z*` 在 birth 度量 `stageMetric (activeStage u) u = initialMetric e.succ` 下距离 `≤ dd`，
且 `neck.scale ≤ 4M`、`2Z + √(8M)·dd < Dcap ≤ modelRadius`，则 `q = window x`，`‖x‖ < Dcap`。
所以整块 patch 在 `u` 时落在 G63 的 window 内（G63 jets 覆盖 `‖x‖ < modelRadius`）。
* `exists_window_point_of_edist_le_C11SP`：`BoundedCurvatureAtDistanceAfterEventCapture:78`
  的 private 引理的公开孪生，`‖xz‖ ≤ transitionEnd` 推广为 `‖xz‖ ≤ Z`（证明逐行，只改 `2Z` 一处）；
  只用 `hasCanonicalWindow` 的 C⁰ 部分（`modelAccuracy ≤ 1/2`），不需要 linked。
* `bornPoint_window_capture_C11SP`：hBorn `Born` 谓词的 `HEq` 形（stage 下标 `e.succ = j`）。
* `smallPatch_radius_fit_C11SP`：小 patch 缩放：`Rwide` 任意时，取
  `ρ0 = min (Rwide − R) ((Dcap − 2Z) / (2·√(8c)·L))`，则 `2Z + √(8cQ)·(L·ρ0/√Q) < Dcap`
  （`L` = `[u*, t]` 距离畸变因子，由 G3 的公共 flow 付）。这正是 hBorn 冻结形 ∀ Rwide 必须先缩小 patch 的原因。
-/

noncomputable section

open Set TopologicalSpace Manifold Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace GC.LongTime.Ch11

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- **G1a（PROVED）**：cap 内窗点附近（birth 度量距离 `≤ dd`）的点仍是 window 点；
`BoundedCurvatureAtDistanceAfterEventCapture` private 引理的公开孪生，内窗界推广为 `Z`。 -/
theorem exists_window_point_of_edist_le_C11SP (H : RetainedCoreHistory.{u})
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2) (j : Fin H.eventCount)
    (b : (H.toHistory.event j).RetainedBoundaryIndex) {M dd Dcap Dstar Z : ℝ}
    (hsM : ((records j).static b).neck.scale ≤ 4 * M)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (xz : standardCapWindow p.modelRadius) (hxzn : ‖xz.val‖ ≤ Z)
    (q : (H.toHistory.stage j.succ).Carrier)
    (hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j).static b).window xz) q ≤ ENNReal.ofReal dd)
    (hdd0 : 0 ≤ dd) (hwin : 2 * Z + Real.sqrt (8 * M) * dd < Dcap) :
    ∃ x : standardCapWindow p.modelRadius,
      ‖x.val‖ < Dcap ∧ ((records j).static b).window x = q := by
  obtain ⟨x₀, δ, kk, d, w, -, hinner, -⟩ := hcan j b
  have hspos : 0 < ((records j).static b).neck.scale := ((records j).static b).neck.scale_pos
  have hlocW : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ((records j).static b).window :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      ((records j).static b).window_smooth.contMDiff
      (fun q => (((records j).static b).window_smooth.isImmersion.isImmersionAt
        q).mfderiv_injective (by simp)) rfl
  have hinjW := ((records j).static b).window_smooth.isEmbedding.injective
  have hsmall := w.properties.window_close
  change Geometry.Metric.metricDerivENormSupOn
    {y : standardCapWindow p.modelRadius |
      (riemannianEDistOf StandardCap.metric 0 y.val).toReal < p.modelRadius} p.modelOrder
    w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius))
      (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius)) <
        ENNReal.ofReal p.modelAccuracy at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  rw [H.toHistory.event_output j] at hinner
  have hTE := StandardCap.transitionEnd_pos
  set sc := ((records j).static b).neck.scale with hsc
  have hL : 0 < Real.sqrt (2 * sc) := Real.sqrt_pos.mpr (by positivity)
  have hU : 0 < Real.sqrt (2 / sc) := Real.sqrt_pos.mpr (by positivity)
  have hLU : Real.sqrt (2 * sc) * Real.sqrt (2 / sc) = 2 := by
    rw [← Real.sqrt_mul (by positivity), show 2 * sc * (2 / sc) = 2 * 2 by field_simp,
      Real.sqrt_mul_self (by norm_num)]
  have hL8 : Real.sqrt (2 * sc) ≤ Real.sqrt (8 * M) := Real.sqrt_le_sqrt (by linarith)
  have hsqrt8 : 0 ≤ Real.sqrt (8 * M) := Real.sqrt_nonneg _
  have hkey : Real.sqrt (2 * sc) * (Real.sqrt (2 / sc) * ‖xz.val‖ + dd) < Dcap := by
    have h1 : Real.sqrt (2 * sc) * dd ≤ Real.sqrt (8 * M) * dd :=
      mul_le_mul_of_nonneg_right hL8 hdd0
    have h2 : Real.sqrt (2 * sc) * (Real.sqrt (2 / sc) * ‖xz.val‖) ≤
        2 * Z := by
      rw [← mul_assoc, hLU]
      linarith
    nlinarith
  have hxzD : ‖xz.val‖ < Dcap := by
    have h0 : 0 ≤ Real.sqrt (8 * M) * dd := mul_nonneg (Real.sqrt_nonneg _) hdd0
    have h1 : 0 ≤ ‖xz.val‖ := norm_nonneg _
    linarith
  have hgap : Real.sqrt (2 / sc) * ‖xz.val‖ + dd < Dcap / Real.sqrt (2 * sc) := by
    rw [lt_div_iff₀ hL]
    linarith
  set r' := (Dcap / Real.sqrt (2 * sc) - (Real.sqrt (2 / sc) * ‖xz.val‖ + dd)) / 2 with hr'
  have hmargin : Real.sqrt (2 / sc) * ‖xz.val‖ + dd + r' < Dcap / Real.sqrt (2 * sc) := by
    rw [hr']
    linarith
  have hr'pos : 0 < r' := by
    rw [hr']
    linarith
  have hbd : ∀ x : standardCapWindow p.modelRadius, ‖x.val‖ < p.modelRadius →
      ∀ v : TangentSpace ThreeModel x,
        (1 - p.modelAccuracy) * StandardCap.metric.inner x.val v v ≤
            w.windowMetric.inner x v v ∧
          w.windowMetric.inner x v v ≤
            (1 + p.modelAccuracy) * StandardCap.metric.inner x.val v v := by
    intro x hx v
    have hn := Geometry.Metric.metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hsmall (Nat.zero_le _)
      (x := x) hx
    simpa only [SmoothRiemannianMetric.restrictOpen_inner] using
      Geometry.Metric.inner_bounds_of_metricDerivNorm_le
        (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius)) w.windowMetric x
        hn.le v
  have hacc0 := p.modelAccuracy_pos
  have hball := StandardCap.window_ball_subset_image_ball_of_metric_bounds
    (H.toHistory.initialMetric j.succ) (D := p.modelRadius) (R := Dcap) (r := r')
    (by linarith) hL hU hdd0 ((records j).static b).window hlocW hinjW
    (fun x hx v => by
      obtain ⟨hlo, -⟩ := hbd x (hx.trans_le (hDstar.trans hDmodel)) v
      have hi := hinner x v v
      have hn := metric_inner_self_nonneg StandardCap.metric x.val v
      rw [Real.sq_sqrt (by positivity)]
      nlinarith)
    (fun x hx v => by
      obtain ⟨-, hup⟩ := hbd x (hx.trans_le (hDstar.trans hDmodel)) v
      have hi := hinner x v v
      have hn := metric_inner_self_nonneg StandardCap.metric x.val v
      rw [Real.sq_sqrt (by positivity), div_mul_eq_mul_div, le_div_iff₀ hspos]
      nlinarith)
    xz hxzD (q) hnear hmargin
  have hcenter : q ∈
      riemannianBallOf (H.toHistory.initialMetric j.succ)
        (q) r' := by
    change riemannianEDistOf _ _ _ < ENNReal.ofReal r'
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr'pos
  obtain ⟨x, hxn, hxeq⟩ := hball hcenter
  exact ⟨x, hxn, hxeq⟩

/-- **G1（PROVED）**：hBorn `Born` 谓词形的 no-straddling。born 点 `P`（`HEq (window z) P`，
`‖z‖ ≤ Z`）在 birth 时刻 stage `j = e.succ` 上；与 `P` 的 `stageMetric j (time j)` 距离 `≤ dd` 的点
`q` 都是同一 cap 的 window 点，`‖x‖ < Dcap`。 -/
theorem bornPoint_window_capture_C11SP (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2) (e : Fin H.eventCount)
    (j : Fin (H.toHistory.eventCount + 1)) (hj : e.succ = j)
    (b : (H.toHistory.event e).RetainedBoundaryIndex) {M dd Dcap Z : ℝ}
    (hsM : ((records e).static b).neck.scale ≤ 4 * M)
    (hDmodel : Dcap ≤ p.modelRadius)
    (z : standardCapWindow p.modelRadius) (hz : ‖z.val‖ ≤ Z)
    (P q : (H.toHistory.stage j).Carrier)
    (hP : HEq (((records e).static b).window z) P)
    (hnear : riemannianEDistOf (H.toHistory.stageMetric j (H.toHistory.time j)) P q ≤
      ENNReal.ofReal dd)
    (hdd : 0 ≤ dd) (hwin : 2 * Z + Real.sqrt (8 * M) * dd < Dcap) :
    ∃ x : standardCapWindow p.modelRadius,
      ‖x.val‖ < Dcap ∧ HEq (((records e).static b).window x) q := by
  subst hj
  have hP' : ((records e).static b).window z = P := eq_of_heq hP
  rw [H.toHistory.stageMetric_initial, ← hP'] at hnear
  obtain ⟨x, hx, hxq⟩ := exists_window_point_of_edist_le_C11SP H records hcan hacc e b hsM le_rfl
    hDmodel z hz q hnear hdd hwin
  exact ⟨x, hx, heq_of_eq hxq⟩

/-- **G1c（PROVED）**：小 patch 缩放。任给 `R < Rwide`、畸变因子 `L ≥ 1`、`c > 0`、
`2Z < Dcap`，存在 `ρ0 ∈ (0, Rwide − R]`，使对一切 `Q > 0`：
`2Z + √(8·(c·Q/4))·(L·(2ρ0/√Q)) < Dcap`（`M = cQ/4` 使 `neck.scale ≤ cQ = 4M`）。 -/
theorem smallPatch_radius_fit_C11SP {R Rwide L c Z Dcap : ℝ} (hRR : R < Rwide) (hL : 1 ≤ L)
    (hc : 0 < c) (hZ : 2 * Z < Dcap) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ρ0 ≤ Rwide - R ∧ ∀ Q : ℝ, 0 < Q →
      2 * Z + Real.sqrt (8 * (c * Q / 4)) * (L * (2 * ρ0 / Real.sqrt Q)) < Dcap := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by positivity)
  let ρ0 : ℝ := min (Rwide - R) ((Dcap - 2 * Z) / (4 * Real.sqrt (2 * c) * L))
  have hgap : 0 < Dcap - 2 * Z := by linarith
  have hρ0 : 0 < ρ0 := lt_min (by linarith) (by positivity)
  refine ⟨ρ0, hρ0, min_le_left _ _, ?_⟩
  intro Q hQ
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsplit : Real.sqrt (8 * (c * Q / 4)) = Real.sqrt (2 * c) * Real.sqrt Q := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hcancel : Real.sqrt (8 * (c * Q / 4)) * (L * (2 * ρ0 / Real.sqrt Q)) =
      2 * Real.sqrt (2 * c) * L * ρ0 := by
    rw [hsplit]
    field_simp
  rw [hcancel]
  have hle : ρ0 ≤ (Dcap - 2 * Z) / (4 * Real.sqrt (2 * c) * L) := min_le_right _ _
  have hden : 0 < 4 * Real.sqrt (2 * c) * L := by positivity
  have h2 : 2 * Real.sqrt (2 * c) * L * ρ0 ≤ (Dcap - 2 * Z) / 2 := by
    have h3 := mul_le_mul_of_nonneg_left hle hden.le
    rw [mul_div_cancel₀ _ hden.ne'] at h3
    nlinarith
  linarith

end GC.LongTime.Ch11
