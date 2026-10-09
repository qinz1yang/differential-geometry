import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAlignedP6SB3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalUContractP6M5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalUFinalP6M6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbcadCCondP6DP3

/-!
# A2 统一切片 BCBD：kernel 帧 adapter（O-CH11-BCBD-A2 G1，后缀 `_A2B`）

分析车道 A2 的可证部分（结论见 `build-logs/resume/state-O-CH11-BCBD-A2.md`）：
* §1 `sepT_sep4_of_sepRho_ceiling_A2B` / `hsepT_hsep4_ev_of_sepRho_A2B`（PROVED）：G9″
  `sliceBCBD_kernel_fresh_sep_noProtC_aligned_P6SB3` 的 `hsepT / hsep4`（年轻 cap 支）⇐ 同一文件的
  (SEP-ρ⁺) 槽 `hsepρ` + 天花板 `R n ≤ ρs(t n)⁻²`（hPN 合同字段，`ρs := ρ̂(Tn)` 时逐字），**eventually** 形；
  G9″ 要 `∀ n`，差一个平移孪生（SLICE-BCBD2 G6 同法），本文件不做。
* §2 CXJD 族数值项（PROVED）：`hRa`、`T₀X / hT₀X`、`hRr`、`hlate` 由 hPN 字段推出。
* §3 `hclosC_of_HU_kernel_A2B` / `hclosCF_of_HU_final_kernel_A2B`（PROVISIONAL[`HU_P6M5` /
  `HU_final_P6M6`，登记合同]）：SLICEDICH F7 的 `hclosC` / `hclosCF` binder 逐字（生成器从 F7 源 :1283–1313 /
  :1337–1372 切片）⇐ P6M4 / P6M5 / P6M6 / DP3 已有链。A2③ 深度溢出在 F7 中的去向 = 这两个合同（无 traced-region
  前提，常数 `C_U(Rad, B, σ₁, σ₂, Dw, Dd)` 在 `n` 之前），本文件不证它们。
生成器 `build-logs/scratch/O-CH11-BCBD-A2/gen/gen1.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ### §1 `hsepT / hsep4` ⇐ (SEP-ρ⁺) 年轻 cap 支 + 天花板 -/

/-- 数值核（`_A2B`，PROVED）：`N·max(N, Q) ≤ S`、`R ≤ Q`、`N > 4M`、`N ≥ θ₀·M·c` ⇒ G9″ 的
`hsepT` / `hsep4` 体（`M = max (max 1 Cg) 1`，`c = 2·max Ct 1`）。 -/
theorem sepT_sep4_of_sepRho_ceiling_A2B {N Q R S θ₀ Cg Ct : ℝ} (hR : 0 < R) (hRQ : R ≤ Q)
    (hS : N * max N Q ≤ S) (hN4 : 4 * max (max 1 Cg) 1 < N)
    (hNθ : θ₀ * (max (max 1 Cg) 1 * (2 * max Ct 1)) ≤ N) :
    θ₀ * R ≤ 1 / (2 * max Ct 1) / max (max 1 Cg) 1 * S ∧
      2 * (2 * (max (max 1 Cg) 1 * R)) < S := by
  have hM1 : (1 : ℝ) ≤ max (max 1 Cg) 1 := le_max_right _ _
  have hCt : (0 : ℝ) < max Ct 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hN0 : 0 < N := by linarith
  have hNR : N * R ≤ S := by
    have h1 : N * R ≤ N * max N Q :=
      mul_le_mul_of_nonneg_left (hRQ.trans (le_max_right _ _)) hN0.le
    linarith
  refine ⟨?_, ?_⟩
  · have hpos : 0 < 2 * max Ct 1 * max (max 1 Cg) 1 := by positivity
    rw [div_div, one_div_mul_eq_div, le_div_iff₀ hpos]
    have h2 : θ₀ * (max (max 1 Cg) 1 * (2 * max Ct 1)) * R ≤ N * R :=
      mul_le_mul_of_nonneg_right hNθ hR.le
    nlinarith
  · have h3 : 4 * max (max 1 Cg) 1 * R < N * R := mul_lt_mul_of_pos_right hN4 hR
    linarith

/-- **G9″ `hsepT / hsep4` ⇐ `hsepρ` + 天花板（`_A2B`，PROVED，eventually 形）**：前提 `hsepρ` = G9″
(SEP-ρ⁺) 槽逐字；`hceil : R n ≤ ρs(t n)⁻²`（hPN 合同 `R k ≤ ρ̂(Tn k)⁻²`，取 SEPFIX A2 的 `ρs n := fun _ =>
ρ̂(Tn n)` 时逐字）。结论 = G9″ 的 `hsepT` 与 `hsep4` 体，对 eventually 所有 `n`。 -/
theorem hsepT_hsep4_ev_of_sepRho_A2B {Ctime' : ℝ≥0} {Cg θ₀ : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (ρs : ℕ → ℝ → ℝ)
    (hceil : ∀ n, R n ≤ (ρs n (t n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
          ((recordsK n i hi).static b).neck.scale ∧
        2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale := by
  set X : ℝ := max (4 * max (max 1 Cg) 1)
    (θ₀ * (max (max 1 Cg) 1 * (2 * max (Ctime' : ℝ) 1))) with hX
  filter_upwards [hsepρ 1 one_pos,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop X] with n hs hn
  intro i hi b hij hy
  have hX1 : 4 * max (max 1 Cg) 1 ≤ X := le_max_left _ _
  have hX2 : θ₀ * (max (max 1 Cg) 1 * (2 * max (Ctime' : ℝ) 1)) ≤ X := le_max_right _ _
  exact sepT_sep4_of_sepRho_ceiling_A2B (hRpos n) (hceil n) (hs i hi b hij (Or.inr hy))
    (by linarith) (by linarith)

/-! ### §2 CXJD 族数值项 ⇐ hPN 字段 -/

/-- `hRa`（`_A2B`，PROVED）：hPN `n + 1 ≤ R n` 与 `1 ≤ aSeed n` ⇒ `1 ≤ R n · aSeed n`。 -/
theorem hRa_of_hPN_A2B (R a : ℕ → ℝ) (hR : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (ha : ∀ n, 1 ≤ a n) : ∀ n, 1 ≤ R n * a n := fun n => by
  have h1 := hR n
  have h2 := ha n
  have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

/-- `T₀X / hT₀X`（`_A2B`，PROVED）：hPN `T₀ k ≤ c k · aSeed k`（原尺度 T₀）⇒
kernel 帧 `T₀ k / c k ≤ aSeed k`。 -/
theorem hT₀X_of_hPN_A2B (T₀ c a : ℕ → ℝ) (hc : ∀ n, 0 < c n) (h : ∀ n, T₀ n ≤ c n * a n) :
    ∀ n, T₀ n / c n ≤ a n := fun n => by
  rw [div_le_iff₀ (hc n)]
  linarith [h n]

/-- `hRr`（`_A2B`，PROVED）：`n + 1 ≤ R n`、`0 < rX` ⇒ `R n · rX² → ∞`
（P6M4 / P6M6 的 `hRr`，`r := fun _ => rX`）。 -/
theorem hRr_of_hRn1_A2B (R : ℕ → ℝ) (hR1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) {rX : ℝ}
    (hrX : 0 < rX) : Tendsto (fun n => R n * rX ^ 2) atTop atTop := by
  have hT : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => (le_add_of_nonneg_right zero_le_one).trans (hR1 n))
      tendsto_natCast_atTop_atTop
  exact hT.atTop_mul_const (pow_pos hrX 2)

/-- `hlate`（`_A2B`，PROVED）：`hwin` + `hRa` ⇒ `1 ≤ R n · (σ n − T / R n)` eventually。 -/
theorem hlate_of_hwin_hRa_A2B (R a s : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, a n ≤ s n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * a n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * (s n - T / R n) := by
  intro T hT
  filter_upwards [hwin T hT] with n hn
  exact (hRa n).trans (mul_le_mul_of_nonneg_left hn (hR n).le)

/-! ### §3 F7 的 `hclosC` / `hclosCF` ⇐ 登记合同 `HU_P6M5` / `HU_final_P6M6` -/

/-- **F7 `hclosC` ⇐ `HU_P6M5`（`_A2B`，PROVISIONAL[`HU_P6M5`]）**：结论 = SLICEDICH F7
`hbcadC_final_of_hclosC_sepRho_P6SD` 的 `hclosC` binder 逐字。链：`hscalU_of_HU_P6M5` →
`hclosG_of_firstExit_P6M4`（seed 半径 `r := fun _ => rX`，`hRr` / `hlate` 由 §2）→
`hclosC_of_hclosG_P6M4`。
`HU_P6M5` 无 traced-region 前提，常数在 `n` 之前、只依赖 `(Rad, B, σ₁, σ₂, Dw, Dd)`。 -/
theorem ObservedHistory.hclosC_of_HU_kernel_A2B (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (hL : Tendsto L atTop atTop)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * aSeed n) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (a₀ + s) x)
    (hU : ∀ B : ℝ, ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) :=
  ObservedHistory.hclosC_of_hclosG_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L
    (ObservedHistory.hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
      (fun _ => rX) hL hsmall hclock (hRr_of_hRn1_A2B R hRn1 hrX) hwin
      (hlate_of_hwin_hRa_A2B R (fun n => (aSeed n : ℝ)) (fun n => (σ n : ℝ)) hRpos hwin hRa)
      ha₀ hpin
      (ObservedHistory.hscalU_of_HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hU))

/-- **F7 `hclosCF` ⇐ `HU_final_P6M6`（`_A2B`，PROVISIONAL[`HU_final_P6M6`]）**：结论 = F7 的
`hclosCF` binder 逐字。链：`hclosGF_of_HU_final_P6M6` → `hclosCF_of_hclosGF_P6DP3`。 -/
theorem ObservedHistory.hclosCF_of_HU_final_kernel_A2B (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (hL : Tendsto L atTop atTop)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * aSeed n) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (a₀ + s) x)
    (hUF : ∀ B : ℝ,
      ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
      v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
        (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
          (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
              (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              w)),
        ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
          → τ ≤ v →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) :=
  ObservedHistory.hclosCF_of_hclosGF_P6DP3 Kh Tn aSeed σ haT hsT has pT seedTrace y R L
    (ObservedHistory.hclosGF_of_HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
      (fun _ => rX) hL hsmall hclock (hRr_of_hRn1_A2B R hRn1 hrX) hwin
      (hlate_of_hwin_hRa_A2B R (fun n => (aSeed n : ℝ)) (fun n => (σ n : ℝ)) hRpos hwin hRa)
      ha₀ hpin hUF)

/-- consumer（`_A2B`）：SEPFIX A2 的 `ρs n := fun _ => ρ̂(Tn n)` 取法 + hPN 天花板字段 ⇒ G9″ 的 `hsepT / hsep4`
（eventually）；`hsepρ` 由调用方（SEPFIX `sepRhoPlusK_branch_of_accuracy_P6SF`）给。 -/
example {Ctime' : ℝ≥0} {Cg θ₀ : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {T₀ Tn : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hceil : ∀ n, R n ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (Tn n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale := by
  filter_upwards [hsepT_hsep4_ev_of_sepRho_A2B (Ctime' := Ctime') (Cg := Cg) (θ₀ := θ₀)
    (recordsK := recordsK) (j := j) (t := t) R hRpos (fun n _ => (p n).neckRadius (Tn n))
    hceil hsepρ] with n hn
  exact fun i hi b hij hy => (hn i hi b hij hy).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
