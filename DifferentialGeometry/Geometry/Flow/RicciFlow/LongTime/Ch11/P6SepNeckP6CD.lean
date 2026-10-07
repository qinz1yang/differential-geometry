import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedResidualCondP6CD

/-!
# (SEP) / (SEP′)：neck 识别 + `recent_cutoff_smallness` ⇒ 尺度分离（O-CH11-P6COND G3，后缀 `_P6CD`）

* `static_scale_ge_of_recenter_P6CD`（record 侧，任意参数）：`scale_eq` + `recenter_scale_comparison` +
  `delta_le` ⇒ `Λ·δ(tᵢ) ≤ 1/2` 时 `(2·nominal²)⁻¹ ≤ static.scale`；
* `recenter_delta_tail_of_common_P6CD`：P5L 供给形（`p n` 与 `q` 共用 `δ / Λ`，`q.δ → 0`）⇒ (DLT)；
* `recordsK_smallness_of_native_P6CD`：**neck 识别** `hnomId`（late `recordsK` 与 `d.native.records` 的
  nominal 半径逐 tube 相同）+ native `recent_cutoff_smallness` ⇒ late records 的新近小性；
* `sepWK_of_smallness_P6CD`：⇒ 残余形 (SEP) `hsepWK` 体逐字；`sepK_eventually_of_smallness_P6CD`：⇒
  (SEP′) `hsepK` 体的 eventually 版；
* consumer `hdistC_of_native_P6CD`：条件形 `hdistC` 只剩 native / 识别输入（无 (SEP) binder）。
**缺口（精确）**：`hnomId`（数据层 `nominalRadius` 是 record 字段，同一 event 的两个 record 不必相等）、
④ 里 selector 参数 `q = d.native.params`、`Tn → ∞`、(DLT)。repair target 见 DELIVERIES G3 块。
由 build-logs/scratch/O-CH11-P6COND/mk_g3.py（+ g3_core.lean.txt）生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **record 侧 neck 尺度下界（`_P6CD`，任意参数）**：`scale_eq`（`neck.scale = nominal⁻²`）+
`recenter_scale_comparison`（`|static / neck − 1| ≤ Λ δ_α`）+ `delta_le`（`δ_α ≤ p.δ(tᵢ)`）⇒
`Λ·p.δ(tᵢ) ≤ 1/2` 时 `(2·nominal²)⁻¹ ≤ static.scale`。 -/
theorem static_scale_ge_of_recenter_P6CD {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (Rec : GeometricCutoffRecord H i p)
    (hδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (b : (H.event i).RetainedBoundaryIndex) :
    (2 * Rec.nominalRadius ⟨b.1.1⟩ ^ 2)⁻¹ ≤ (Rec.static b).neck.scale := by
  have hnpos := Rec.nominal_pos ⟨b.1.1⟩
  have hcmp := Rec.recenter_scale_comparison b
  have hsc := Rec.scale_eq b.1.1
  have hdα := Rec.delta_le b.1.1
  have hΛ : (4 : ℝ) ≤ p.recenterConstant := p.recenterConstant_ge_four
  set r := Rec.nominalRadius ⟨b.1.1⟩
  set N := (Rec.neck b.1.1).scale
  set S := (Rec.static b).neck.scale
  have hNpos : 0 < N := by
    rw [hsc]
    exact inv_pos.mpr (pow_pos hnpos 2)
  have hΛδα : p.recenterConstant * Rec.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hdα (by linarith)).trans hδ
  have hhalf : 1 / 2 ≤ S / N := by
    have := (abs_le.mp (hcmp.trans hΛδα)).1
    linarith
  have hS : N / 2 ≤ S := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * r ^ 2)⁻¹ = N / 2 := by
    rw [hsc, mul_inv, div_eq_mul_inv]
    ring
  rw [h2]
  exact hS

/-- **(DLT) ⇐ 共同参数**（`_P6CD`）：late 参数 `p n` 与 `q` 共用 `δ`、`Λ`（P5L 供给形
`hpδ / hprc`）且 `q.δ → 0` ⇒ 存在 `Tδ`，`τ ≥ Tδ` 时 `Λ·δ(τ) ≤ 1/2`（对所有 `n` 一致）。 -/
theorem recenter_delta_tail_of_common_P6CD {p : ℕ → CutoffParameters} {q : CutoffParameters}
    (hpδ : ∀ n, (p n).delta = q.delta) (hprc : ∀ n, (p n).recenterConstant = q.recenterConstant)
    (hδq : Tendsto q.delta atTop (𝓝 0)) :
    ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ → (p n).recenterConstant * (p n).delta τ ≤ 1 / 2 := by
  have hΛ : (4 : ℝ) ≤ q.recenterConstant := q.recenterConstant_ge_four
  have hc : (0 : ℝ) < 1 / (2 * q.recenterConstant) := by positivity
  obtain ⟨Tδ, hT⟩ := Filter.eventually_atTop.1 (hδq.eventually (ge_mem_nhds hc))
  refine ⟨Tδ, fun n τ hτ => ?_⟩
  rw [hpδ n, hprc n]
  have h1 : q.recenterConstant * q.delta τ ≤ q.recenterConstant * (1 / (2 * q.recenterConstant)) :=
    mul_le_mul_of_nonneg_left (hT τ hτ) (by linarith)
  have h2 : q.recenterConstant * (1 / (2 * q.recenterConstant)) = 1 / 2 := by
    field_simp
  linarith

/-- **neck 识别 ⇒ late records 的新近小性（`_P6CD`）**：`hnomId`（late `recordsK` 与 native
`N.records` 的 nominal 半径逐 tube 相同）+ native `recent_cutoff_smallness` ⇒ `recordsK` 的
新近小性（`tᵢ ∈ [τ/2, τ]` ⇒ `nominal ≤ ε ρ(τ)`，`ρ = N.params.neckRadius`）。 -/
theorem recordsK_smallness_of_native_P6CD {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (N : GC.LongTime.Ch11.Pre841NativeData_C11K (fun n => (K n).toHistory))
    (hnomId : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (N.records n i).nominalRadius h) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (τ / 2) τ → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * N.params.neckRadius τ := by
  intro ε hε
  obtain ⟨T, hT, h⟩ := N.recent_cutoff_smallness ε hε
  exact ⟨T, hT, fun τ hτ n i hti hi hh => (hnomId n i hi hh).trans_le (h τ hτ n i hti hh)⟩

/-- **(SEP) ⇐ 新近小性 + selector ④ + (DLT)（`_P6CD`）**：结论 = closed 主形残余形 `hsepWK` 体
（`s` = 选点时刻）。证明：窗口 `s − T/R < tᵢ ≤ t ≤ Tn` + 半深度 + `R r² → ∞` ⇒ `tᵢ ∈ [Tn/2, Tn]`；
小性（`t := Tn`）⇒ `nominal ≤ ε ρ(Tn)`；record 下界 ⇒ `scale ≥ (2 nominal²)⁻¹ ≥ (2ε²)⁻¹ ρ(Tn)⁻² ≥
(2ε²)⁻¹ R`；`3/(r/100)² ≤ R` eventually；取 `ε = 1/(4 max C 1)`。 -/
theorem sepWK_of_smallness_P6CD {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {s t Tn r R : ℕ → ℝ} {ρ : ℝ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htT : ∀ n, t n ≤ Tn n)
    (hhalf : ∀ n, Tn n - r n ^ 2 / 2 ≤ s n) (htime : ∀ n, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ n, 0 < R n) (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hTn : Tendsto Tn atTop atTop) (hsel4 : ∀ n, R n ≤ (ρ (Tn n) ^ 2)⁻¹)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
      (p n).recenterConstant * (p n).delta τ ≤ 1 / 2)
    (hsmallK : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (τ / 2) τ → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρ τ) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
        s n - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale := by
  intro T _ C _
  set M : ℝ := max C 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  set ε : ℝ := 1 / (4 * M) with hεdef
  have hε : 0 < ε := by positivity
  have h4 : 4 * M * ε = 1 := by
    rw [hεdef]
    field_simp
  have hε1 : ε < 1 := by nlinarith
  obtain ⟨Tε, -, hsm⟩ := hsmallK ε hε
  obtain ⟨Tδ, hδ⟩ := hδK
  filter_upwards [hTn.eventually_ge_atTop (max Tε (2 * Tδ)),
    hRr.eventually_ge_atTop (max 30000 (4 * T))] with n hTnn hRrn
  intro i hij hi b hwin
  have hR := hRpos n
  have hx : 30000 ≤ R n * r n ^ 2 := (le_max_left _ _).trans hRrn
  have hx4 : 4 * T ≤ R n * r n ^ 2 := (le_max_right _ _).trans hRrn
  have hr2 : 0 < r n ^ 2 := by
    rcases (sq_nonneg (r n)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hx
      linarith
  have hTR : T / R n ≤ r n ^ 2 / 4 := by
    rw [div_le_iff₀ hR]
    nlinarith
  have hle : i.succ ≤ (j n).castSucc := by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hti_hi : (K n).time i.succ ≤ Tn n :=
    ((K n).time_strictMono.monotone hle).trans ((hjt n).le.trans (htT n))
  have hti_lo : Tn n / 2 ≤ (K n).time i.succ := by
    have h1 := hhalf n
    have h2 := htime n
    have h3 := sq_nonneg (r n)
    linarith
  have hTε : Tε ≤ Tn n := (le_max_left _ _).trans hTnn
  have hTδ : Tδ ≤ (K n).time i.succ := by
    have := (le_max_right _ _).trans hTnn
    linarith
  have hnom := hsm (Tn n) hTε n i ⟨hti_lo, hti_hi⟩ hi ⟨b.1.1⟩
  have hS := static_scale_ge_of_recenter_P6CD (recordsK n i hi) (hδ n _ hTδ) b
  set rn := (recordsK n i hi).nominalRadius ⟨b.1.1⟩
  have hrn : 0 < rn := (recordsK n i hi).nominal_pos _
  set ρn := ρ (Tn n)
  have hερ : 0 < ε * ρn := hrn.trans_le hnom
  have hρ : 0 < ρn := pos_of_mul_pos_right hερ hε.le
  have hRρ : R n * ρn ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hsel4 n) (sq_nonneg ρn)
    rwa [inv_mul_cancel₀ (pow_pos hρ 2).ne'] at h
  have hrn2 : rn ^ 2 ≤ ε ^ 2 * ρn ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hrn.le hnom 2
  have h3 : 3 / (r n / 100) ^ 2 ≤ R n := by
    have hpos : 0 < (r n / 100) ^ 2 := by
      have e : (r n / 100) ^ 2 = r n ^ 2 / 10000 := by ring
      rw [e]
      exact div_pos hr2 (by norm_num)
    rw [div_le_iff₀ hpos]
    have e : R n * (r n / 100) ^ 2 = R n * r n ^ 2 / 10000 := by ring
    rw [e]
    linarith
  have hmax : max (3 / (r n / 100) ^ 2) (C * R n) ≤ M * R n :=
    max_le (h3.trans (le_mul_of_one_le_left hR.le hM1))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le)
  have hkey : 2 * (M * R n) * (2 * rn ^ 2) < 1 := by
    have h4MR : 0 ≤ 4 * M * R n := mul_nonneg (mul_nonneg (by norm_num) hM0.le) hR.le
    calc 2 * (M * R n) * (2 * rn ^ 2) = 4 * M * R n * rn ^ 2 := by ring
      _ ≤ 4 * M * R n * (ε ^ 2 * ρn ^ 2) := mul_le_mul_of_nonneg_left hrn2 h4MR
      _ = (4 * M * ε) * ε * (R n * ρn ^ 2) := by ring
      _ ≤ (4 * M * ε) * ε * 1 :=
        mul_le_mul_of_nonneg_left hRρ (mul_nonneg (by rw [h4]; norm_num) hε.le)
      _ = ε := by rw [h4]; ring
      _ < 1 := hε1
  have hpos2 : 0 < 2 * rn ^ 2 := mul_pos two_pos (pow_pos hrn 2)
  have hlt : 2 * (M * R n) < (2 * rn ^ 2)⁻¹ := by
    rw [← one_div]
    exact (lt_div_iff₀ hpos2).2 hkey
  calc 2 * max (3 / (r n / 100) ^ 2) (C * R n) ≤ 2 * (M * R n) := by linarith
    _ < (2 * rn ^ 2)⁻¹ := hlt
    _ ≤ ((recordsK n i hi).static b).neck.scale := hS

/-- **(SEP′) eventually ⇐ 新近小性 + selector ④ + (DLT)（`_P6CD`）**：结论 = 残余形 `hsepK` 体的
eventually 版（`∀ n` 版经主形对尾子列 `n ↦ n + N` 重新应用）。`t − tᵢ ≤ scale⁻¹ ≤ 1`（`hscaleK`）+
半深度 + `Tn → ∞` ⇒ `tᵢ ∈ [Tn/2, Tn]`；`ε = min 1 (η/4)` ⇒ `R·2 nominal² ≤ 2ε² < η`。 -/
theorem sepK_eventually_of_smallness_P6CD {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {T₀ Q : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {t Tn r R : ℕ → ℝ} {ρ : ℝ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htT : ∀ n, t n ≤ Tn n)
    (hhalf : ∀ n, Tn n - r n ^ 2 / 2 ≤ t n) (htime : ∀ n, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ n, 0 < R n) (hTn : Tendsto Tn atTop atTop) (hsel4 : ∀ n, R n ≤ (ρ (Tn n) ^ 2)⁻¹)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
      (p n).recenterConstant * (p n).delta τ ≤ 1 / 2)
    (hsmallK : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (τ / 2) τ → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρ τ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
      R n < η * ((recordsK n i hi).static b).neck.scale := by
  set ε : ℝ := min 1 (η / 4) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε ≤ η / 4 := min_le_right _ _
  obtain ⟨Tε, -, hsm⟩ := hsmallK ε hε
  obtain ⟨Tδ, hδ⟩ := hδK
  filter_upwards [hTn.eventually_ge_atTop (max (max Tε (2 * Tδ)) 4)] with n hTnn
  intro i hi b hle hwin
  have hR := hRpos n
  set S := ((recordsK n i hi).static b).neck.scale with hSdef
  have hS1 : 1 ≤ S := by
    have h := hscaleK n i hi b
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hm : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    nlinarith
  have hSinv : S⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1
  have hT4 : 4 ≤ Tn n := (le_max_right _ _).trans hTnn
  have hti_hi : (K n).time i.succ ≤ Tn n :=
    ((K n).time_strictMono.monotone hle).trans ((hjt n).le.trans (htT n))
  have hti_lo : Tn n / 2 ≤ (K n).time i.succ := by
    have h1 := hhalf n
    have h2 := htime n
    have h3 := sq_nonneg (r n)
    linarith
  have hTε : Tε ≤ Tn n := ((le_max_left _ _).trans (le_max_left _ _)).trans hTnn
  have hTδ : Tδ ≤ (K n).time i.succ := by
    have := ((le_max_right _ _).trans (le_max_left _ _)).trans hTnn
    linarith
  have hnom := hsm (Tn n) hTε n i ⟨hti_lo, hti_hi⟩ hi ⟨b.1.1⟩
  have hSlow := static_scale_ge_of_recenter_P6CD (recordsK n i hi) (hδ n _ hTδ) b
  set rn := (recordsK n i hi).nominalRadius ⟨b.1.1⟩
  have hrn : 0 < rn := (recordsK n i hi).nominal_pos _
  set ρn := ρ (Tn n)
  have hερ : 0 < ε * ρn := hrn.trans_le hnom
  have hρ : 0 < ρn := pos_of_mul_pos_right hερ hε.le
  have hRρ : R n * ρn ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hsel4 n) (sq_nonneg ρn)
    rwa [inv_mul_cancel₀ (pow_pos hρ 2).ne'] at h
  have hrn2 : rn ^ 2 ≤ ε ^ 2 * ρn ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hrn.le hnom 2
  have hε2 : 2 * ε ^ 2 ≤ η / 2 := by nlinarith
  have hkey : R n * (2 * rn ^ 2) < η := by
    calc R n * (2 * rn ^ 2) ≤ R n * (2 * (ε ^ 2 * ρn ^ 2)) := by
          have := mul_le_mul_of_nonneg_left hrn2 (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_left this hR.le
      _ = (2 * ε ^ 2) * (R n * ρn ^ 2) := by ring
      _ ≤ (2 * ε ^ 2) * 1 := mul_le_mul_of_nonneg_left hRρ (by positivity)
      _ < η := by linarith
  have hpos2 : 0 < 2 * rn ^ 2 := mul_pos two_pos (pow_pos hrn 2)
  have hlt : R n < η * (2 * rn ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (lt_div_iff₀ hpos2).2 hkey
  exact hlt.trans_le (mul_le_mul_of_nonneg_left hSlow hη.le)

/-- **consumer：条件形 `hdistC` ⇐ native 数据 + neck 识别（`_P6CD`）**：`hdistC_of_sep_P6CD` 的 (SEP)
`hsepWK` 换成其来源——`hnomId`（neck / nominal 识别）、selector ④ `hsel4`（`ρ = d.native.params`）、
(DLT) `hδK`、`Tn → ∞`；`d.native.recent_cutoff_smallness` 在证明里取 `t := Tn`。 -/
theorem hdistC_of_native_P6CD {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
        n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => (K n).toHistory) σ y R
      hRpos)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (hTn : Tendsto (fun n => (Tn n : ℝ)) atTop atTop)
    (hsel4 : ∀ n, R n ≤ (d.native.params.neckRadius (Tn n) ^ 2)⁻¹)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
      (p n).recenterConstant * (p n).delta τ ≤ 1 / 2)
    (hnomId : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (d.native.records n i).nominalRadius h) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
          n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
                hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                  n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have htT : ∀ n, t n ≤ (Tn n : ℝ) := fun n => by
    rw [← hσ n]
    exact hsT n
  exact hdistC_of_sep_P6CD hjt htj rfl σ y R hσ hRpos d Tn aSeed haT hsT has pT seedTrace r L hL
    hroom htime hsmall hclock hRr recordsK hcanK hacc hrad hord hT₀
    (sepWK_of_smallness_P6CD recordsK (s := fun n => (σ n : ℝ)) hjt htT hhalf htime hRpos hRr hTn
      hsel4 hδK (recordsK_smallness_of_native_P6CD recordsK d.native hnomId))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
