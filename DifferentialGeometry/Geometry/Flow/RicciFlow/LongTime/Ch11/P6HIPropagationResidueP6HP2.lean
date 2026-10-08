import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationP6HP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M

/-!
# HIPROP2 G1：HIPROP 的三个残余（O-CH11-HIPROP2，后缀 `_P6HP2`）

HIPROP（root #94，`P6HIPropagationP6HP`）的 φ-pinching producer `hpinch_of_initial_P6HP` 需要两个 binder：
`0 < a₀ n` 与 `A ≤ a₀ n + T₀ n`；HANDOVER 把它们拆成三个残余。本文件逐项付清（全部 PROVED，standard axioms）：
* **(i) `0 < a₀ / c n`**：`rescaledHIParam_pos_P6HP2`（一行 `div_pos`），以及完整的重标度初始输入
  `RetainedCoreHistory.rescale_initialHI_P6HP2`：原尺度 `initialMetric 0` 的 HI(`a₀`) ∧ `R ≥ −3/a₀` ⇒
  `rescale_P6N c` 的 `initialMetric 0` 的 HI(`a₀/c`) ∧ `R ≥ −3/(a₀/c)`
  （`scaleMetric c⁻¹`：`R ↦ c·R`，
  HI 参数 `a ↦ a/c`，树内 `inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M`）。
* **(ii) `A ≤ T₀ n` 的来源**：不再找外部下界——取 `A := T₁`（固定常数 `T₁ > 0`），records 阈值抬到
  `max T₀ T₁`：`records_raise_P6HP2`（records 的限制）、`le_max_threshold_P6HP2`（`T₁ ≤ max T₀ T₁`）、
  `eventually_threshold_le_P6HP2`（`aSeed ≥ 1`、`R k ≥ k + 1` ⇒ `∀ᶠ k`, `max T₀ T₁ ≤ σ k − B/R k`，
  当 `T₁ < 1`
  且 `T₀ ≤ σ k − B/R k`）。抬阈值只缩小 records 的使用范围（late 窗不受影响）。
* **(iii) 重标度后一致下界**：`hpinch_rescaled_late_P6HP2`：∃ 只依赖 `T₁` 的 admissible `Phi`，对一切
  原尺度族 `H n`、一切重标度因子 `c n > 0`（**无上下界**）、全事件 records、逐 `n` 的 `a₀ n > 0` 初始 HI，
  重标度族 `(H n).rescale_P6N (c n)` 的 event slab ∩ `Ici (T₀ n)` 与 final slab ∩ `Ici (T₀ n)` 都
  `PhiAlmostNonnegative Phi`，只要 `T₁ ≤ T₀ n`。理由：重标度 frame 里 HI 参数 = `a₀ n / c n + τ ≥ τ ≥ T₁`。
  `T₀ n ≥ T₁` 必须保留：首 slab τ ≈ 0 处 HI 参数 `a₀/c → 0`，没有一致下界（反例见 state 末尾）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **(i)（`_P6HP2`，PROVED）**：重标度 frame 的 HI 初始参数 `a₀ / c` 为正。 -/
theorem rescaledHIParam_pos_P6HP2 {a₀ c : ℝ} (ha₀ : 0 < a₀) (hc : 0 < c) : 0 < a₀ / c :=
  div_pos ha₀ hc

/-- **(i) 重标度初始输入（`_P6HP2`，PROVED）**：`(H.rescale_P6N c).initialMetric j = c⁻¹·g`；
HI(`a₀`) ⇔ HI(`c·(a₀/c)`)，`R(c⁻¹ g) = c·R(g) ≥ c·(−3/a₀) = −3/(a₀/c)`。 -/
theorem RetainedCoreHistory.rescale_initialHI_P6HP2 (H : RetainedCoreHistory.{u}) {c : ℝ}
    (hc : 0 < c) (j : Fin (H.eventCount + 1)) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric j) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt (H.initialMetric j) x) (x : (H.stage j).Carrier) :
    InFixedHamiltonIveyRegion ((H.rescale_P6N c hc).initialMetric j) (a₀ / c) x ∧
      -3 / (a₀ / c) ≤ metricScalarAt ((H.rescale_P6N c hc).initialMetric j) x := by
  have hca : c * (a₀ / c) = a₀ := mul_div_cancel₀ a₀ hc.ne'
  refine ⟨?_, ?_⟩
  · change InFixedHamiltonIveyRegion (scaleMetric c⁻¹ (inv_pos.mpr hc) (H.initialMetric j))
      (a₀ / c) x
    rw [inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M hc, hca]
    exact (hHI x).1
  · change -3 / (a₀ / c) ≤ metricScalarAt (scaleMetric c⁻¹ (inv_pos.mpr hc) (H.initialMetric j)) x
    rw [metricScalarAt_scaleMetric, inv_inv]
    have h2 := (hHI x).2
    have he : -3 / (a₀ / c) = c * (-3 / a₀) := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left h2 hc.le

/-- **(ii) records 阈值抬升（`_P6HP2`，PROVED）**：阈值 `T₀` 的 records 限制到阈值 `max T₀ T₁`。 -/
def records_raise_P6HP2 {H : ObservedHistory.{u}} {p : CutoffParameters} {T₀ : ℝ} (T₁ : ℝ)
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H i p) :
    ∀ i : Fin H.eventCount, max T₀ T₁ ≤ H.time i.succ → GeometricCutoffRecord H i p :=
  fun i h => records i ((le_max_left T₀ T₁).trans h)

/-- **(ii)（`_P6HP2`，PROVED）**：`A := T₁` 时 `A ≤ max T₀ T₁` 恒成立（取代"records 阈值下界"的外部来源）。 -/
theorem le_max_threshold_P6HP2 (T₀ T₁ : ℝ) : T₁ ≤ max T₀ T₁ := le_max_right T₀ T₁

/-- **(ii) 抬升后阈值仍在 late 窗内（`_P6HP2`，PROVED）**：`T₁ < 1`、`1 ≤ σ k`、`k + 1 ≤ R k`、
原阈值 `T₀ k ≤ σ k − B/R k` ⇒ `∀ᶠ k`，`max (T₀ k) T₁ ≤ σ k − B/R k`。 -/
theorem eventually_threshold_le_P6HP2 {T₁ B : ℝ} (hT₁ : T₁ < 1)
    {σ R T₀ : ℕ → ℝ} (hσ : ∀ k, 1 ≤ σ k) (hR : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k)
    (hT₀ : ∀ k, T₀ k ≤ σ k - B / R k) :
    ∀ᶠ k in atTop, max (T₀ k) T₁ ≤ σ k - B / R k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (B / (1 - T₁))
  refine eventually_atTop.mpr ⟨N, fun k hk => max_le (hT₀ k) ?_⟩
  have h1T : 0 < 1 - T₁ := sub_pos.mpr hT₁
  have hNk : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
  have hRk : (N : ℝ) + 1 ≤ R k := by linarith [hR k]
  have hRpos : 0 < R k := lt_of_lt_of_le (by positivity) hRk
  have hBR : B / R k ≤ 1 - T₁ := by
    rw [div_le_iff₀ hRpos]
    have h := (div_lt_iff₀ h1T).mp hN
    nlinarith
  linarith [hσ k]

/-- **(iii) 重标度后一致下界（`_P6HP2`，PROVED）**：∃ 只依赖 `T₁ > 0` 的 admissible `Phi`，对一切原尺度族、
一切 `c n > 0`、全事件 records、逐 `n` 初始 HI(`a₀ n`)（`a₀ n > 0`），重标度族的 event slab ∩ `Ici (T₀ n)`
与接在 last 上的任意 IncomingSlab ∩ `Ici (T₀ n)` 都 φ-pinched，只要 `T₁ ≤ T₀ n`。
= `hpinch_of_initial_P6HP`（`A := T₁`）喂 `K n := (H n).rescale_P6N (c n)`、records `rescale_P6M`、
初始 `rescale_initialHI_P6HP2`、`a₀ n / c n + T₀ n ≥ T₁`。 -/
theorem hpinch_rescaled_late_P6HP2 {T₁ : ℝ} (hT₁ : 0 < T₁) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
    ∀ (H : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
      (pF : ℕ → CutoffParameters)
      (_recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n)) (a₀ : ℕ → ℝ),
      (∀ n, 0 < a₀ n) →
      (∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((H n).initialMetric 0) x) →
      ∀ T₀ : ℕ → ℝ, (∀ n, T₁ ≤ T₀ n) →
      (∀ n (i : Fin ((H n).rescale_P6N (c n) (hc n)).eventCount), Perelman.PhiAlmostNonnegative
        (((H n).rescale_P6N (c n) (hc n)).toHistory.event i).incoming.flow
        (Ico (((H n).rescale_P6N (c n) (hc n)).time i.castSucc)
          (((H n).rescale_P6N (c n) (hc n)).time i.succ) ∩ Ici (T₀ n)) Phi) ∧
      ∀ (s : ℕ → ℝ) (G : ∀ n, (((H n).rescale_P6N (c n) (hc n)).stage
          (Fin.last ((H n).rescale_P6N (c n) (hc n)).eventCount)).IncomingSlab
          (((H n).rescale_P6N (c n) (hc n)).time
            (Fin.last ((H n).rescale_P6N (c n) (hc n)).eventCount)) (s n)),
        (∀ n, (G n).flow.base.metric (((H n).rescale_P6N (c n) (hc n)).time
            (Fin.last ((H n).rescale_P6N (c n) (hc n)).eventCount)) =
          ((H n).rescale_P6N (c n) (hc n)).initialMetric
            (Fin.last ((H n).rescale_P6N (c n) (hc n)).eventCount)) →
        ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
          (Ico (((H n).rescale_P6N (c n) (hc n)).time
            (Fin.last ((H n).rescale_P6N (c n) (hc n)).eventCount)) (s n) ∩ Ici (T₀ n)) Phi := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} hT₁
  refine ⟨Phi, hPhi, ?_⟩
  intro H c hc pF recordsF a₀ ha₀ hHI T₀ hT
  exact hP (fun n => (H n).rescale_P6N (c n) (hc n))
    (fun n => (pF n).rescale_P6N (c n) (hc n))
    (fun n i => (recordsF n i).rescale_P6M (c n) (hc n))
    (fun n => a₀ n / c n) T₀ (fun n => rescaledHIParam_pos_P6HP2 (ha₀ n) (hc n))
    (fun n => (hT n).trans (le_add_of_nonneg_left (rescaledHIParam_pos_P6HP2 (ha₀ n) (hc n)).le))
    (fun n x => (H n).rescale_initialHI_P6HP2 (hc n) 0 (ha₀ n) (hHI n) x)

/-- **(iii) 常数阈值特例（`_P6HP2`，PROVED）**：`T₀ n := T₁` 时的 event 部分（hpinch 槽 ∩`Ici T₁` 形的核）。 -/
theorem hpinch_rescaled_const_P6HP2 {T₁ : ℝ} (hT₁ : 0 < T₁) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
    ∀ (H : ℕ → RetainedCoreHistory.{u}) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
      (pF : ℕ → CutoffParameters)
      (_recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n)) (a₀ : ℕ → ℝ),
      (∀ n, 0 < a₀ n) →
      (∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((H n).initialMetric 0) x) →
      ∀ n (i : Fin ((H n).rescale_P6N (c n) (hc n)).eventCount), Perelman.PhiAlmostNonnegative
        (((H n).rescale_P6N (c n) (hc n)).toHistory.event i).incoming.flow
        (Ico (((H n).rescale_P6N (c n) (hc n)).time i.castSucc)
          (((H n).rescale_P6N (c n) (hc n)).time i.succ) ∩ Ici T₁) Phi := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_rescaled_late_P6HP2.{u} hT₁
  exact ⟨Phi, hPhi, fun H c hc pF recordsF a₀ ha₀ hHI =>
    (hP H c hc pF recordsF a₀ ha₀ hHI (fun _ => T₁) (fun _ => le_rfl)).1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
