import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTnP6SN

/-!
# (SEP′) 常数核对：SLICE-BCBD `hsepT / hsep4` ↔ SEPTN `hsep`（η 形）（O-CH11-SLICE-BCBD2 G4，后缀 `_P6SB2`）

三处名为 "(SEP′)" 的陈述**不是同一个**：
* SLICE-BCBD G6/G7/G8 `hsepT`：年轻窗口 `t − tᵢ ≤ θ₀/s` ⇒ `θ₀·R ≤ c⋆/Qb′·s`；常数
  `c⋆ = 1/(2·max(Ctime′,1))`、`Qb′ = max(max 1 Cg) 1`、`θ₀ > 0`。
* SLICE-BCBD G7/G8 `hsep4`：同一窗口 ⇒ `4·Qb′·R < s`。
* SEPTN `hnotK_of_diagonal_cws_P6SN` 的 `hsep` 与 `sepK_eventually_of_smallAtTn_P6SN`：
  窗口 `t − tᵢ ≤ 1/s` ⇒ `R < η·s`；前者 `η` = 标准解常数 `c`（存在量词给出，不可调），后者对每个 `η > 0` eventually 成立。
* NATIVE-SEP `sep_of_records_C11SP`（SEP′）：cap window ∌ 后继 regular crossing 点；常数 `Csep`、
  `δ₁ = 1/(8√(5Csep)(D+1) + 40000 + 2Rc)`、`16Bθ ≤ 1`——不同对象，与上三者无常数关系。
结论：SB 两条与 SN 的 η 形只差常数与窗口（`θ₀ ≤ 1` 时 SB 年轻窗口 ⊆ SN 窗口）：
* `sepSB_of_sepSN_real_P6SB2`（PROVED，纯实数）：`θ₀ ∈ (0, 1]`、`4·Qb′·η ≤ 1`、`θ₀·η ≤ c⋆/Qb′` ⇒ 单个 cap 的
  SN 结论推出 SB 两条；
* `sepSB_ev_of_sepSN_P6SB2`（PROVED）：SN 的 ∀η eventually 形 ⇒ SB `hsepT ∧ hsep4` 的 eventually 形
  （`η := min (1/(4Qb′)) (c⋆/(Qb′θ₀))`）；
* consumer：SEPTN producer `sepK_eventually_of_smallAtTn_P6SN` ⇒ eventually 的 `hsepT ∧ hsep4`。
注意：SB 主定理（G7 / G8）把 `hsepT / hsep4` 写成 `∀ n`；SN producer 只给 eventually。kernel diagonal 前提
（`hacc ≤ 1/(n+1)`、`hrad2`、`hord`、`hRlt`）对平移 `n ↦ n + N` 单调，故以 `hsepK_forall_of_eventually_P6SN`
同法平移数据即可（本文件不做平移孪生）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **单 cap 常数换算（`_P6SB2`，PROVED，纯实数）**：`θ₀ ∈ (0, 1]`、`4·Qb·η ≤ 1`、`θ₀·η ≤ cs/Qb`；SB 年轻
（`age ≤ θ₀/s`）⇒ SN 年轻（`age ≤ 1/s`）⇒ `R < η·s` ⇒ SB `hsepT`（`θ₀·R ≤ cs/Qb·s`）与 `hsep4`
（`2·(2·(Qb·R)) < s`）。 -/
theorem sepSB_of_sepSN_real_P6SB2 {θ₀ η R s Qb cs age : ℝ} (hθ₀ : 0 < θ₀) (hθ1 : θ₀ ≤ 1)
    (hs : 0 < s) (hQb : 0 < Qb) (hη4 : 4 * Qb * η ≤ 1) (hηT : θ₀ * η ≤ cs / Qb)
    (hage : age ≤ θ₀ * s⁻¹) (hSN : age ≤ s⁻¹ → R < η * s) :
    θ₀ * R ≤ cs / Qb * s ∧ 2 * (2 * (Qb * R)) < s := by
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hage' : age ≤ s⁻¹ := hage.trans (by nlinarith)
  have hR := hSN hage'
  constructor
  · have h1 : θ₀ * R ≤ θ₀ * (η * s) := mul_le_mul_of_nonneg_left hR.le hθ₀.le
    have h2 : θ₀ * (η * s) ≤ cs / Qb * s := by
      have := mul_le_mul_of_nonneg_right hηT hs.le
      linarith [show θ₀ * (η * s) = θ₀ * η * s by ring]
    linarith
  · have h1 : 4 * Qb * R < 4 * Qb * (η * s) := mul_lt_mul_of_pos_left hR (by linarith)
    have h2 : 4 * Qb * (η * s) ≤ s := by
      have := mul_le_mul_of_nonneg_right hη4 hs.le
      linarith [show 4 * Qb * (η * s) = 4 * Qb * η * s by ring]
    linarith

/-- **SN ∀η eventually 形 ⇒ SB `hsepT ∧ hsep4` eventually 形（`_P6SB2`，PROVED）**：
`η := min (1/(4Qb′)) (c⋆/(Qb′·θ₀))`，`Qb′ = max (max 1 Cg) 1`，`c⋆ = 1/(2·max(Ctime′,1))`。 -/
theorem sepSB_ev_of_sepSN_P6SB2 {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {t R : ℕ → ℝ} {θ₀ Cg : ℝ} {Ctime' : ℝ≥0} (hθ₀ : 0 < θ₀) (hθ1 : θ₀ ≤ 1)
    (hSN : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount)
      (hi : T₀ n ≤ (K n).time i.succ) (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
      R n < η * ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
          ((recordsK n i hi).static b).neck.scale ∧
        2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale := by
  set Qb : ℝ := max (max 1 Cg) 1 with hQbdef
  set cs : ℝ := 1 / (2 * max (Ctime' : ℝ) 1) with hcsdef
  have hQb : 0 < Qb := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcs : 0 < cs := by
    have : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  set η : ℝ := min (1 / (4 * Qb)) (cs / (Qb * θ₀)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη4 : 4 * Qb * η ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (min_le_left (1 / (4 * Qb)) (cs / (Qb * θ₀)))
      (by positivity : (0 : ℝ) ≤ 4 * Qb)
    rwa [mul_one_div_cancel (by positivity)] at h
  have hηT : θ₀ * η ≤ cs / Qb := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (1 / (4 * Qb)) (cs / (Qb * θ₀))) hθ₀.le
    have he : θ₀ * (cs / (Qb * θ₀)) = cs / Qb := by
      field_simp
    linarith
  filter_upwards [hSN η hη] with n hn
  intro i hi b hl hage
  exact sepSB_of_sepSN_real_P6SB2 hθ₀ hθ1 ((recordsK n i hi).static b).neck.scale_pos hQb hη4
    hηT hage (hn i hi b hl)

/-- **consumer（`_P6SB2`）**：SEPTN producer `sepK_eventually_of_smallAtTn_P6SN`（∀ `η > 0`）⇒ SB 主定理
`hsepT ∧ hsep4` 的 eventually 形（`θ₀ ∈ (0, 1]`）。 -/
theorem sepSB_ev_of_smallAtTn_P6SB2 {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {T₀ Q : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {t Tn r R ρn : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htT : ∀ n, t n ≤ Tn n)
    (hhalf : ∀ n, Tn n - r n ^ 2 / 2 ≤ t n) (htime : ∀ n, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ n, 0 < R n) (hsel4 : ∀ n, R n ≤ (ρn n ^ 2)⁻¹)
    (hTn0 : ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ᶠ n in atTop, τ₀ ≤ Tn n)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n)
    {θ₀ Cg : ℝ} {Ctime' : ℝ≥0} (hθ₀ : 0 < θ₀) (hθ1 : θ₀ ≤ 1) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
          ((recordsK n i hi).static b).neck.scale ∧
        2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale :=
  sepSB_ev_of_sepSN_P6SB2 hθ₀ hθ1 fun _ hη =>
    sepK_eventually_of_smallAtTn_P6SN hjt htT hhalf htime hRpos hsel4 hTn0 hscaleK hδ hsm hη

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
