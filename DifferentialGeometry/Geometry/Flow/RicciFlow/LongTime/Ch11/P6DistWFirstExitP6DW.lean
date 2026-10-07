import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SeedWindowFirstExit_P6DW

/-!
# (TR₀) `hdistW` ⇐ 首出时刻的 σ₂ = 0 基点版（O-CH11-HDISTW G1，后缀 `_P6DW`）

`P6ClosedConditionalP6CD:122–137` 的 `hdistW`（同 slab 基点窗口 seed 距离，余量 `L`）。
* **`hdistW_of_firstExit_P6DW`**：结论 = hdistW binder 逐字。top-inclusive 首出版本（anchor `v = σ_n`、
  `w = y_n`、`q_w = R_n`；`seed_window_firstExit_P6DW` 经 `distW_transport_P6DW`）。前提 = P6ANCH4
  `hclosG_of_firstExit_P6M4` 同款数据（K0 `hsmall/hclock`、`R r² → ∞`、HI `hpin`、`hwin`、`hL`）+ slab 结构
  `activeStage σ = e⁻` + **唯一残余 `hscalW`（Anchor₀ 义务）**：`∀ D T > 0, ∃ C ≥ 1, ∀ᶠ n`，
  `x ∈ B_σ(y, D/√R)`、开窗 `s ∈ (σ − T/R, σ)`（`time(activeStage σ) < s`）、单时刻 ExitGuard
  `d_s(O, x) ≤ d_σ(O, y) + L/√R` ⇒ `B_s(x, 1/√(CR))` 上 `R ≤ CR`（度量 `stageMetric (activeStage σ) s`）。
  `hlate` 由 `hwin (T + 1)` + `aSeed ≥ 0` 推出，不另设。
* `hscalW` 是 H_U 体在 `(σ₂ = 0, v = σ, x₁ = w = y, q_w = R)` 的实例，**不**被 L1（`σ₂ < 0` 严格）覆盖；按 D-3 /
  R-C11-8 D-7 单列，不与 L1 合并。它只对本序列（同一实际构造的重标度 retained selected family）陈述，不对任意
  `ObservedHistory` 全称化（R7）。`s → σ⁻` 的极限含 SLT anchor 的 σ 时刻结论 ⇒ 不是小叶子。
* `hdistW_top_P6DW`：hdistW 的 σ 切片（`v = σ`）无残余（三角不等式 + `L → ∞`）——σ-only anchor 的接口。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **(TR₀) `hdistW` ⇐ 首出时刻 σ₂ = 0 基点版（`_P6DW`）**：结论逐字 = `false_of_selection_eventSlab_late_
closed_cond_P6CD` 的 `hdistW` binder；唯一残余 `hscalW`（Anchor₀，开窗、单时刻 ExitGuard、`C` 在 `n` 之前）。 -/
theorem ObservedHistory.hdistW_of_firstExit_P6DW (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hσev : ∀ n, ∃ e : Fin (Kh n).eventCount, (Kh n).activeStage (σ n) = e.castSucc)
    (hscalW : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro D T hD hT
  obtain ⟨C, hC, hev⟩ := hscalW D T hD hT
  filter_upwards [hev, hwin (T + 1) (by linarith),
    hL.eventually_ge_atTop (max D 0 +
      8 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max T 0),
    hRr.eventually_ge_atTop
      (2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))))]
    with n hn hwn hLn hrn
  intro x hx v hav hvs hvT hvσ tr
  obtain ⟨e, he⟩ := hσev n
  have hRn := hR n
  by_cases htop : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) = ⊤
  · rw [htop, top_add]
    exact le_top
  have hv1 : (Kh n).time ((Kh n).activeStage (σ n)) ≤ v := by
    rw [← hvσ]
    exact (Kh n).activeStage_time_le v
  have hσdom := ((Kh n).mem_stageDomain_iff (σ n) e.castSucc).mpr he
  simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hσdom
  have hvσ' : (v : ℝ) ≤ σ n := hvs
  have hav' : (aSeed n : ℝ) ≤ v := hav
  have hRv : 1 ≤ R n * v := by
    have h0 : (0 : ℝ) ≤ aSeed n := (aSeed n).2.1
    have e1 : R n * ((T + 1) / R n) = T + 1 := by field_simp
    have e2 : R n * (T / R n) = T := by field_simp
    have h3 : 0 ≤ R n * σ n - R n * ((T + 1) / R n) := by
      rw [← mul_sub]
      exact mul_nonneg hRn.le (by linarith)
    have h4 : R n * σ n - R n * (T / R n) ≤ R n * v := by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left hvT hRn.le
    rw [e1] at h3
    rw [e2] at h4
    linarith
  exact (Kh n).distW_transport_P6DW (haT n) (hsmall n) (hclock n) (seedTrace n) ha₀ (hpin n)
    hvσ e he ((Kh n).activeStage_mono hav) ((Kh n).activeStage_mono (hvs.trans (hsT n)))
    ((Kh n).activeStage_mono (has n)) ((Kh n).activeStage_mono (hsT n))
    ((Kh n).activeStage_mono hvs) (y n) x tr (ENNReal.ofReal_toReal htop).symm
    ENNReal.toReal_nonneg hRn hC hrn hLn hx hvT hvσ' hv1 hσdom.2 hav' (hsT n) hRv (hn x hx)

/-- **hdistW 的 σ 切片（`_P6DW`，无残余）**：`v = σ` 时 hdistW 的结论只是 σ 时刻三角不等式
`d_σ(O, x) ≤ d_σ(O, y) + d_σ(y, x)`、`D ≤ L`（eventually）。σ-only anchor（G2 路线）只需要这一片。 -/
theorem ObservedHistory.hdistW_top_P6DW (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) → (v : ℝ) = σ n →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro D T hD _hT
  filter_upwards [hL.eventually_ge_atTop D] with n hLn
  intro x hx v hav hvs _hvT _hvσ hvv tr
  have hveq : v = σ n := Subtype.ext hvv
  subst hveq
  have hpt : tr.point ((Kh n).activeStage (σ n)) le_rfl ((Kh n).activeStage_mono hvs) = x :=
    tr.endpoint_eq
  rw [hpt]
  have hsR : 0 ≤ Real.sqrt (R n) := Real.sqrt_nonneg _
  calc riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono hav)
          ((Kh n).activeStage_mono (hvs.trans (hsT n)))) x ≤
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n) x :=
        riemannianEDistOf_triangle _ _ _ _
    _ ≤ riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) :=
        add_le_add le_rfl ((le_of_lt hx).trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hLn hsR)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
