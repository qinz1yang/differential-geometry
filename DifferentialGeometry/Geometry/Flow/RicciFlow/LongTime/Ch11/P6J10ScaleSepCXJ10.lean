import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaRescaleP6CK

/-!
# J10 `c n · Q_{s,n} < R n` 的 scale-separation 归约（CX-J10 G1，后缀 `_CXJ10`）

D-8：jointD（`canonicalLateCore_of_jointD_P6CK`）的 `Qs` 在 selection 之后 ∃，同一 `Qs` 同时进 J9
`EventSlabsDerivative Ctime₀ (Qs n) (Fin.last _)`（整条 history `Ho n` 的阈值）与 J10 `c n * Qs n < R n`；
P6WR 的 `hOpen` 冻结形取 `Qs n := qcanSup S (Ho n).horizon`（依赖 `ind`/horizon）。

**路线选择 = (ii) near-selection scale separation**，理由（树内核查）：
* (i) 前置 envelope 不可行：J10 等价于 `Θ_n < R n / c n`（`Θ_n` = J9 阈值），`R n / c n` 是原尺度
  selected 曲率；selection 前唯一的 envelope 是 `Qt`（`Qt k < R k`，**重标度**单位），要用它须
  `c n · Θ_n ≤ Qt n`，而 `c n = r n ^ 2` 由 selection 给出、`Θ_n = qcanSup S (ind n)` 依赖 `ind`——
  树内无 selection 前的 `r n` 上界，也无与 horizon 无关的一致 derivative 阈值（`qcan` 随带增长）。
  envelope 形只作为**消费引理** `hJ10_of_envelope_CXJ10` 保留（`c·Θ ≤ max Qt (n+1)` ⇒ J10）。
* (ii)：把 J10 化成 selected 点自身的原尺度不等式 `Θ_n < R^orig(σ_n, y_n)`（`c` 消掉），这是
  selection 的性质，不是 selection 前的统一 `T₀`；并证明它对冻结形 **等价**（`hJ10_iff_…`），故
  这正是精确 repair target。

主结果：
* `scalar_uncastRescale_CXJ10`：`R̃(σ, y) = c · R(cσ, y)`（重标度 → 原尺度）。
* `hJ10_iff_origSep_CXJ10` / **`hJ10_of_scaleSeparation_CXJ10`**：冻结 hOpen 形 J10
  （`Qs := qcanSup S (Ho n).horizon`）⟺ 原尺度 scale separation `qcanSup S (Ho n).horizon < R^orig`。
* `hJ10_of_envelope_CXJ10`、`eventually_hJ10_of_bounded_CXJ10`（`R → ∞` 只给 eventually）。
* `exists_Qs_slab_J10_CXJ10`：jointD 形 `∃ Qs`（J9 ∧ J10 ∧ KNOM Q 档 `Qs ≤ Q` ∧ 两个 scale 合取）。
**未付（BLOCKED）**：scale separation 本身（见 state-CX-J10.md HANDOVER）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `c Q < R ⟺ Q < R / c`（`c > 0`）。 -/
theorem mul_lt_iff_lt_div_CXJ10 {c Q R : ℝ} (hc : 0 < c) : c * Q < R ↔ Q < R / c := by
  rw [lt_div_iff₀ hc, mul_comm]

/-- 同一 history 上时刻相等 + 点 `HEq` ⇒ 标量相等。 -/
theorem scalar_congr_CXJ10 (H : ObservedHistory.{u}) {v w : Icc (0 : ℝ) H.horizon} (h : v = w)
    {z : (H.stageAt v).Carrier} {z' : (H.stageAt w).Carrier} (hz : HEq z z') :
    metricScalarAt (H.stageMetric (H.activeStage v) v) z =
      metricScalarAt (H.stageMetric (H.activeStage w) w) z' := by
  subst h
  rw [eq_of_heq hz]

namespace RetainedCoreHistory

/-- J9 阈值单调：阈值放大，`EventSlabsDerivative` 仍成立（结论只在 `qcan < R` 处要求）。 -/
theorem eventSlabsDerivative_mono_CXJ10 (H : RetainedCoreHistory.{u}) {Ctime : ℝ≥0} {Θ Θ' : ℝ}
    (h : Θ ≤ Θ') {k : Fin (H.eventCount + 1)} (hd : H.EventSlabsDerivative Ctime Θ k) :
    H.EventSlabsDerivative Ctime Θ' k :=
  fun j hj y t ht hR => hd j hj y t ht (h.trans_lt hR)

/-- 标量（反向）：`R̃(v, y) = c · R(c v, uncast y)`。 -/
theorem scalar_uncastRescale_CXJ10 (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)
    (v : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (y : ((K.rescale_P6N c hc).toHistory.stageAt v).Carrier) :
    metricScalarAt ((K.rescale_P6N c hc).toHistory.stageMetric
        ((K.rescale_P6N c hc).toHistory.activeStage v) v) y =
      c * metricScalarAt (K.toHistory.stageMetric
        (K.toHistory.activeStage (K.unscaleTime_P6X hc v)) (K.unscaleTime_P6X hc v))
        (K.uncastRescale_P6CK hc v y) := by
  obtain ⟨w, rfl⟩ : ∃ w, K.rescaleTime_P6X hc w = v := ⟨_, K.rescale_unscaleTime_P6X hc v⟩
  obtain ⟨x, rfl⟩ := K.castRescale_surj_P6CK hc w y
  have h2 := scalar_congr_CXJ10 K.toHistory (K.unscale_rescaleTime_P6X hc w)
    ((K.heq_uncastRescale_P6CK hc _ _).trans (K.heq_castRescale_P6X hc w x))
  rw [h2]
  exact K.scalar_castRescale_P6X hc w x

end RetainedCoreHistory

/-- 原尺度 selected 曲率 `R^orig(cσ, y)`（`R n / c n` 的内蕴形）。 -/
def origScalar_CXJ10 (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)
    (σ : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (y : ((K.rescale_P6N c hc).toHistory.stageAt σ).Carrier) : ℝ :=
  metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage (K.unscaleTime_P6X hc σ))
    (K.unscaleTime_P6X hc σ)) (K.uncastRescale_P6CK hc σ y)

/-- `R n = R̃(σ, y)` ⇒ `R n / c n = R^orig`。 -/
theorem div_eq_origScalar_CXJ10 (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)
    (σ : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (y : ((K.rescale_P6N c hc).toHistory.stageAt σ).Carrier) {R : ℝ}
    (hR : R = metricScalarAt ((K.rescale_P6N c hc).toHistory.stageMetric
      ((K.rescale_P6N c hc).toHistory.activeStage σ) σ) y) :
    R / c = origScalar_CXJ10 K hc σ y := by
  rw [hR, K.scalar_uncastRescale_CXJ10 hc σ y, mul_div_cancel_left₀ _ hc.ne']
  rfl

/-- **J10 ⟺ 原尺度 scale separation**（任意阈值 `Θ`）：`c n Θ n < R n ⟺ Θ n < R^orig(σ n, y n)`。 -/
theorem hJ10_iff_origSep_CXJ10 (Ho : ℕ → RetainedCoreHistory.{u}) {c : ℕ → ℝ}
    (hc : ∀ n, 0 < c n) {Θ : ℕ → ℝ}
    (σ : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (y : ∀ n, (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ)
    (hRdef : ∀ n, R n = metricScalarAt (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
      (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n)) (y n)) :
    (∀ n, c n * Θ n < R n) ↔ ∀ n, Θ n < origScalar_CXJ10 (Ho n) (hc n) (σ n) (y n) := by
  refine forall_congr' fun n => ?_
  rw [mul_lt_iff_lt_div_CXJ10 (hc n), div_eq_origScalar_CXJ10 (Ho n) (hc n) (σ n) (y n) (hRdef n)]

/-- **`hJ10_of_scaleSeparation_CXJ10`**：P6WR `hOpen` 冻结形 J10（`Qs n := qcanSup S (Ho n).horizon`）
⇐ near-selection scale separation：selected 点原尺度曲率 `>` 该 history 的 J9 阈值。 -/
theorem hJ10_of_scaleSeparation_CXJ10 {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (Ho : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (σ : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (y : ∀ n, (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ)
    (hRdef : ∀ n, R n = metricScalarAt (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
      (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n)) (y n))
    (hsep : ∀ n, GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon <
      origScalar_CXJ10 (Ho n) (hc n) (σ n) (y n)) :
    ∀ n, c n * GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon < R n :=
  (hJ10_iff_origSep_CXJ10 Ho hc σ y R hRdef).2 hsep

/-- envelope 消费形：`c n Θ n ≤ max (Qt n) (n+1)` + 冻结前提 `Qt k < R k`、`k + 1 < R k` ⇒ J10。 -/
theorem hJ10_of_envelope_CXJ10 {c Θ R Qt : ℕ → ℝ} (hQt : ∀ n, Qt n < R n)
    (hR1 : ∀ n : ℕ, (n : ℝ) + 1 < R n) (henv : ∀ n, c n * Θ n ≤ max (Qt n) ((n : ℝ) + 1)) :
    ∀ n, c n * Θ n < R n :=
  fun n => (henv n).trans_lt (max_lt (hQt n) (hR1 n))

/-- `R n → ∞` 只给 eventually 形：重标度阈值 `c n Θ n` 有界 ⇒ eventually J10。 -/
theorem eventually_hJ10_of_bounded_CXJ10 {c Θ R : ℕ → ℝ} (hR : Tendsto R atTop atTop) {B : ℝ}
    (hB : ∀ᶠ n in atTop, c n * Θ n ≤ B) : ∀ᶠ n in atTop, c n * Θ n < R n :=
  (hB.and (hR.eventually_gt_atTop B)).mono fun _ h => h.1.trans_lt h.2

/-- **jointD 形 `∃ Qs` 打包**：J9 阈值 `Θ` + scale separation + KNOM Q 档 `Θ ≤ Q`（及 Q 档的两个
scale 合取）⇒ `∃ Qs`：`Qs ≤ Q` ∧ J9 ∧ J10 ∧ `(n+1)·max((n+1)/c)(Qs) ≤ scale` ∧ `max Qs 1 ≤ Cb·scale`。
`scale n` 为任意族（实例 = `recordsK` 的 neck scale）。 -/
theorem exists_Qs_slab_J10_CXJ10 (Ho : ℕ → RetainedCoreHistory.{u}) (Ctime₀ : ℝ≥0)
    (c Θ R Q Cb : ℕ → ℝ) {ι : ℕ → Type*} (scale : ∀ n, ι n → ℝ)
    (hslab : ∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Θ n) (Fin.last (Ho n).eventCount))
    (hJ : ∀ n, c n * Θ n < R n) (hΘQ : ∀ n, Θ n ≤ Q n)
    (hQa : ∀ (n : ℕ) b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤ scale n b)
    (hQb : ∀ n b, max (Q n) 1 ≤ Cb n * scale n b) :
    ∃ Qs : ℕ → ℝ, (∀ n, Qs n ≤ Q n) ∧
      (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
      (∀ n, c n * Qs n < R n) ∧
      (∀ (n : ℕ) b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤ scale n b) ∧
      (∀ n b, max (Qs n) 1 ≤ Cb n * scale n b) := by
  refine ⟨Θ, hΘQ, hslab, hJ, fun n b => ?_, fun n b => ?_⟩
  · have h0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact (mul_le_mul_of_nonneg_left (max_le_max le_rfl (hΘQ n)) h0).trans (hQa n b)
  · exact (max_le_max (hΘQ n) le_rfl).trans (hQb n b)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
