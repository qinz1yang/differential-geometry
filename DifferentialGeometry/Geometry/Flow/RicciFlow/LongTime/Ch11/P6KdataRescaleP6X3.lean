import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchRescaleP6X2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

/-!
# 原尺度 K 层数据 ⇒ 重标度 K 层（O-CH11-P6SEL3 G1，后缀 `_P6X3`）

D-17 rescale 路线：`hgapN`（`hPN_of_pureClass_lateHI_P6X2`）的 K 层数据写在重标度 history
`K̃ := K.rescale_P6N c` 上。本文件逐项给 transport（输入 = 原 history `K` 的对应数据 + `c > 0`）：
* `recordsKRescale_P6X3`（def）：late records `GeometricCutoffRecord.rescale_P6M`，参数
  `p ↦ p.rescale_P6N c`，late 量词 `T̃₀ := max 1 (T₀/c) ≤ time/c ⇒ T₀ ≤ time`
  （`le_time_of_rescale_P6X3`）；全 records `recordsF` 同（直接 `rescale_P6M`）；
* `hHI_rescale_P6X3`：`ã₀ := a₀/c`（`inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M`，
  `−3/ã₀ = c·(−3/a₀) ≤ c·R = R̃`；不需要 `a₀ > 0`）；
* `hcanK_rescale_P6X3`（`hasCanonicalWindow_rescale_P6M`）；`hδF_rescale_P6X3`
  （`CutoffParameters.rescale_P6N_eval`：`δ̃(t/c) = δ(t)`）；
  `model_rescale_P6X3`（`hacc hrad hord`：`rfl`）；
* `hscaleK_rescale_P6X3`：原尺度前提 `A·max (B/c) Q ≤ scale` ⇒ `A·max B (c·Q) ≤ c·scale = scalẽ`
  （`c` 可 < 1，故原尺度前提必须带 `B/c`）；`hbirthA_rescale_P6X3`：`(a₀/c)(c·scale) = a₀·scale`；
* `derivativeBoundBefore_rescale_P6X3` / `eventSlabsDerivative_rescale_P6X3`：`∂R̃ = c²·∂R(c·)`，
  `Ctime` 不变、阈值 `Q ↦ c·Q`；
* **`KdataRescale_P6X3`**（consumer 打包）：存在**固定** `phi`，使任意原尺度序列数据
  （`0 < a₀ n` + 上面各项原尺度形）⇒ `hgapN` 的 K 层合取（`Q̃ = c·Q`、`T̃₀ = max 1 (T₀/c)`、
  `p̃ = p.rescale_P6N c`、`ã₀ = a₀/c`、`hpinchK0` 由 P6SEL2 `hpinchK0_rescale_P6X2`）。
不能由 rescale 直接推出、留在原尺度前提里的项：`0 < a₀ n`（仅 `hpinchK0` 用）与 `hscaleK` 的 `B/c` 形。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 模型数据（`modelAccuracy` / `modelRadius` / `modelOrder`）在参数重标度下不变（`rfl`）。 -/
theorem CutoffParameters.model_rescale_P6X3 (p : CutoffParameters) {c : ℝ} (hc : 0 < c) :
    (p.rescale_P6N c hc).modelAccuracy = p.modelAccuracy ∧
      (p.rescale_P6N c hc).modelRadius = p.modelRadius ∧
      (p.rescale_P6N c hc).modelOrder = p.modelOrder :=
  ⟨rfl, rfl, rfl⟩

/-- incoming slab 的时间导数界在重标度下：`∂R̃(t) = c²·∂R(c t)`，`Ctime` 不变、阈值 `qcan ↦ c·qcan`。 -/
theorem OrientedThreeStage.IncomingSlab.derivativeBoundBefore_rescale_P6X3
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) {c : ℝ} (hc : 0 < c)
    {Ctime : ℝ≥0} {qcan t₀ : ℝ} (h : G.DerivativeBoundBefore Ctime qcan t₀) :
    (G.rescale c hc).DerivativeBoundBefore Ctime (c * qcan) (t₀ / c) := by
  intro y t ht hq
  have hs : ∀ v, (G.rescale c hc).flow.scalar v y = c * G.flow.scalar (c * v) y :=
    fun v => RetainedCoreHistory.rescale_scalar_P6N G c hc v y
  have hct : c * t ∈ Ioo a t₀ := by
    obtain ⟨h1, h2⟩ := ht
    rw [div_lt_iff₀ hc] at h1
    rw [lt_div_iff₀ hc] at h2
    exact ⟨by linarith, by linarith⟩
  rw [hs] at hq
  have hq' : qcan < G.flow.scalar (c * t) y := (mul_lt_mul_iff_right₀ hc).mp hq
  have hD := h y (c * t) hct hq'
  have hfun : (fun v => (G.rescale c hc).flow.scalar v y) =
      fun v => c • (fun u => G.flow.scalar u y) (c * v) := by
    funext v
    rw [hs, smul_eq_mul]
  rw [hfun, derivWithin_fun_const_smul_field,
    derivWithin_comp_mul_left c (fun u => G.flow.scalar u y),
    LinearOrderedField.smul_Iic hc, hs, smul_eq_mul, smul_eq_mul]
  set D := derivWithin (fun u => G.flow.scalar u y) (Iic (c * t)) (c * t)
  set Rz := G.flow.scalar (c * t) y
  have hc2 : 0 < c ^ 2 := by positivity
  rw [show |c * (c * D)| = c ^ 2 * |D| by
      rw [abs_mul, abs_mul, abs_of_pos hc]; ring,
    show (Ctime : ℝ) * (c * Rz) ^ 2 = c ^ 2 * (Ctime * Rz ^ 2) by ring]
  exact (mul_le_mul_iff_of_pos_left hc2).mpr hD

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

include hc in
/-- 重标度 late 量词的回拉：`max 1 (T₀/c) ≤ t/c ⇒ T₀ ≤ t`。 -/
theorem le_time_of_rescale_P6X3 {T₀ t : ℝ} (h : max 1 (T₀ / c) ≤ t / c) : T₀ ≤ t :=
  (div_le_div_iff_of_pos_right hc).mp ((le_max_right _ _).trans h)

/-- **late records 的重标度**（`GeometricCutoffRecord.rescale_P6M`；`T̃₀ := max 1 (T₀/c)`）。 -/
def recordsKRescale_P6X3 {p : CutoffParameters} {T₀ : ℝ}
    (recordsK : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (i : Fin (K.rescale_P6N c hc).eventCount)
    (hi : max 1 (T₀ / c) ≤ (K.rescale_P6N c hc).time i.succ) :
    GeometricCutoffRecord (K.rescale_P6N c hc).toHistory i (p.rescale_P6N c hc) :=
  (recordsK i (le_time_of_rescale_P6X3 hc (t := K.time i.succ) hi)).rescale_P6M c hc

/-- `hHI`：时刻 0 的 Hamilton–Ivey 区域与标量下界，年龄 `a₀ ↦ a₀/c`。 -/
theorem hHI_rescale_P6X3 {a₀ : ℝ}
    (hHI : ∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) :
    ∀ x, InFixedHamiltonIveyRegion ((K.rescale_P6N c hc).initialMetric 0) (a₀ / c) x ∧
      -3 / (a₀ / c) ≤ metricScalarAt ((K.rescale_P6N c hc).initialMetric 0) x := by
  have key : ∀ x : (K.stage 0).Carrier,
      InFixedHamiltonIveyRegion (scaleMetric c⁻¹ (inv_pos.mpr hc) (K.initialMetric 0))
        (a₀ / c) x ∧
      -3 / (a₀ / c) ≤ metricScalarAt (scaleMetric c⁻¹ (inv_pos.mpr hc) (K.initialMetric 0)) x := by
    intro x
    rw [inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M hc, metricScalarAt_scaleMetric, inv_inv,
      mul_div_cancel₀ a₀ hc.ne']
    refine ⟨(hHI x).1, ?_⟩
    have h := mul_le_mul_of_nonneg_left (hHI x).2 hc.le
    calc -3 / (a₀ / c) = c * (-3 / a₀) := by rw [div_div_eq_mul_div]; ring
      _ ≤ _ := h
  exact key

/-- `hcanK`：重标度 records 的 static cap 仍有 canonical window。 -/
theorem hcanK_rescale_P6X3 {p : CutoffParameters} {T₀ : ℝ}
    (recordsK : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (hcanK : ∀ i hi b, ((recordsK i hi).static b).hasCanonicalWindow) :
    ∀ i hi b, ((K.recordsKRescale_P6X3 hc recordsK i hi).static b).hasCanonicalWindow :=
  fun i _ b => ((recordsK i _).static b).hasCanonicalWindow_rescale_P6M (hcanK i _ b) c hc

/-- `hδF`：`δ̃(t/c) = δ(t)`，late 量词 `T̃₀ = max 1 (T₀/c)`。 -/
theorem hδF_rescale_P6X3 {pF : CutoffParameters} {T₀ δ : ℝ}
    (hδF : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → pF.delta (K.time i.succ) ≤ δ) :
    ∀ i : Fin (K.rescale_P6N c hc).eventCount,
      max 1 (T₀ / c) ≤ (K.rescale_P6N c hc).time i.succ →
      (pF.rescale_P6N c hc).delta ((K.rescale_P6N c hc).time i.succ) ≤ δ :=
  fun i hi => ((pF.rescale_P6N_eval c hc (K.time i.succ)).1).trans_le
    (hδF i (le_time_of_rescale_P6X3 hc (t := K.time i.succ) hi))

/-- `hscaleK`：`scalẽ = c·scale`；原尺度前提写 `A·max (B/c) Q ≤ scale`。 -/
theorem hscaleK_rescale_P6X3 {p : CutoffParameters} {T₀ A B Q : ℝ}
    (recordsK : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (hscaleK : ∀ i hi b, A * max (B / c) Q ≤ ((recordsK i hi).static b).neck.scale) :
    ∀ i hi b, A * max B (c * Q) ≤
      ((K.recordsKRescale_P6X3 hc recordsK i hi).static b).neck.scale := by
  intro i hi b
  have hmax : c * max (B / c) Q = max B (c * Q) := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_div_cancel₀ B hc.ne']
  have h := mul_le_mul_of_nonneg_left (hscaleK i (le_time_of_rescale_P6X3 hc
    (t := K.time i.succ) hi) b) hc.le
  have h' : A * max B (c * Q) ≤ c * ((recordsK i (le_time_of_rescale_P6X3 hc
      (t := K.time i.succ) hi)).static b).neck.scale := by
    calc A * max B (c * Q) = c * (A * max (B / c) Q) := by rw [mul_left_comm, hmax]
      _ ≤ _ := h
  exact h'.trans_eq (((recordsK i _).static b).rescale_P6M_scale c hc).symm

/-- `hbirthA`：`(a₀/c)·(c·scale) = a₀·scale`。 -/
theorem hbirthA_rescale_P6X3 {p : CutoffParameters} {T₀ a₀ : ℝ}
    (recordsK : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (hbirthA : ∀ i hi b, 1 ≤ a₀ * ((recordsK i hi).static b).neck.scale) :
    ∀ i hi b, 1 ≤ a₀ / c * ((K.recordsKRescale_P6X3 hc recordsK i hi).static b).neck.scale := by
  intro i hi b
  have h := hbirthA i (le_time_of_rescale_P6X3 hc (t := K.time i.succ) hi) b
  have he : a₀ / c * (c * ((recordsK i (le_time_of_rescale_P6X3 hc
      (t := K.time i.succ) hi)).static b).neck.scale) =
      a₀ * ((recordsK i (le_time_of_rescale_P6X3 hc
        (t := K.time i.succ) hi)).static b).neck.scale := by
    field_simp
  refine h.trans_eq (he.symm.trans ?_)
  exact congrArg (fun z => a₀ / c * z) (((recordsK i _).static b).rescale_P6M_scale c hc).symm

/-- `hslabK`：event slab 时间导数界（`Ctime` 不变、阈值 `Q ↦ c·Q`）。 -/
theorem eventSlabsDerivative_rescale_P6X3 {Ctime : ℝ≥0} {Q : ℝ} {k : Fin (K.eventCount + 1)}
    (h : K.EventSlabsDerivative Ctime Q k) :
    (K.rescale_P6N c hc).EventSlabsDerivative Ctime (c * Q) k :=
  fun j hj => (K.toHistory.event j).incoming.derivativeBoundBefore_rescale_P6X3 hc (h j hj)

end RetainedCoreHistory

/-- **K 层 transport 打包（`_P6X3`）**：存在固定 `phi`，任意原尺度序列数据 ⇒ `hgapN` 的 K 层合取
（重标度 history `(Ko n).rescale_P6N (c n)`；见文件头）。 -/
theorem KdataRescale_P6X3 :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∀ (Ko : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
      (Ctime₀ : ℝ≥0) (Q T₀ : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        GeometricCutoffRecord (Ko n).toHistory i (p n))
      (a₀ : ℕ → ℝ),
      (∀ n i, GeometricCutoffRecord (Ko n).toHistory i (pF n)) →
      (∀ n, 0 < a₀ n) →
      (∀ n x, InFixedHamiltonIveyRegion ((Ko n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((Ko n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (Ko n).eventCount), T₀ n ≤ (Ko n).time i.succ →
        (pF n).delta ((Ko n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n, (Ko n).EventSlabsDerivative Ctime₀ (Q n) (Fin.last (Ko n).eventCount)) →
      (∀ n x, InFixedHamiltonIveyRegion (((Ko n).rescale_P6N (c n) (hc n)).initialMetric 0)
          (a₀ n / c n) x ∧
        -3 / (a₀ n / c n) ≤
          metricScalarAt (((Ko n).rescale_P6N (c n) (hc n)).initialMetric 0) x) ∧
      (∀ n i hi b,
        (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).hasCanonicalWindow) ∧
      (∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount),
        max 1 (T₀ n / c n) ≤ ((Ko n).rescale_P6N (c n) (hc n)).time i.succ →
        ((pF n).rescale_P6N (c n) (hc n)).delta (((Ko n).rescale_P6N (c n) (hc n)).time i.succ) ≤
          1 / ((n : ℝ) + 1)) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (c n * Q n) ≤
        (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale) ∧
      (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n / c n *
        (((Ko n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale) ∧
      (∀ n (i : Fin ((Ko n).rescale_P6N (c n) (hc n)).eventCount), Perelman.PhiAlmostNonnegative
        (((Ko n).rescale_P6N (c n) (hc n)).toHistory.event i).incoming.flow
        (Ico (((Ko n).rescale_P6N (c n) (hc n)).time i.castSucc)
          (((Ko n).rescale_P6N (c n) (hc n)).time i.succ) ∩ Ici (max 1 (T₀ n / c n))) phi) ∧
      (∀ n, ((Ko n).rescale_P6N (c n) (hc n)).EventSlabsDerivative Ctime₀ (c n * Q n)
        (Fin.last ((Ko n).rescale_P6N (c n) (hc n)).eventCount)) := by
  obtain ⟨Phi, hPhi, hpinch⟩ := hpinchK0_rescale_P6X2.{u}
  refine ⟨Phi, hPhi, ?_⟩
  intro Ko c hc Ctime₀ Q T₀ p pF recordsK a₀ recordsF ha₀ hHI hcanK hδF hscaleK hbirthA hslabK
  refine ⟨fun n => (Ko n).hHI_rescale_P6X3 (hc n) (hHI n),
    fun n => (Ko n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcanK n),
    fun n => (Ko n).hδF_rescale_P6X3 (hc n) (hδF n),
    fun n => (Ko n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hscaleK n),
    hbirthA.mono fun n hn => (Ko n).hbirthA_rescale_P6X3 (hc n) (recordsK n) hn,
    fun n i => hpinch (Ko n) (c n) (hc n) (pF n) (recordsF n) (a₀ n) (ha₀ n) (hHI n) _
      (le_max_left _ _) i,
    fun n => (Ko n).eventSlabsDerivative_rescale_P6X3 (hc n) (hslabK n)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
