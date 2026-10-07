import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaBridgeP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAge_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterGood_P6L

/-!
# P6 bridge 的 (D2) 时间余量重写与 D-5 固定 `A_*` 形（O-CH11-P6B2 G1，后缀 `_P6B2`）

背景：R-C11-2 D-6（`out/dispositions-R-C11-2-p6-w1-open-items.md`）——`s_n ≥ t_n − r_n²/2` **不推出**
`s_n − T/Q_n ≥ t_n − r_n²/2`；要 **(D2)** `Q_n (s_n − (t_n − r_n²/2)) → ∞`。已交
`tracedKappa_of_window_P6B`（`P6KappaBridgeP6B`）的 `hwin : ∀ T > 0, ∀ᶠ n, t − r²/2 ≤ s − T/R`
在 `R > 0` 下**恰与 (D2) 的 `Tendsto` 形等价**（`tendsto_margin_iff_window_P6B2`）——错的不是
`hwin` 的形，而是上游曾把它由 `s ≥ t − r²/2` 推出。本文件把前提换成 (D2) 的 `Tendsto` 形，并给出
P6A3 selection 输出（`T − r²/2 ≤ s − L²/Q`，`L → ∞`）直接入口。

* `eventually_window_of_margin_P6B2` / `tendsto_margin_of_eventually_window_P6B2` /
  `tendsto_margin_iff_window_P6B2`：`hmargin ⇔ hwin`（`R > 0` eventually）。
* `tendsto_margin_of_eventually_selection_P6B2`：P6A3 `tendsto_selection_time_margin_P6L` 的
  eventually 版（selection 只对 `n` 充分大给出点）。
* **`tracedKappa_of_window_margin_P6B2`**：`tracedKappa_of_window_P6B` 的 (D2) / D-5 版：
  `hwin` ↦ `hR + hmargin`；window κ 在 `A_*`、种子体积在 `A₀ ≤ A_*`（D-5：`A_*` 固定、不随 `D, T`），
  `hdist` 保持**显式**前提，右端 `A_* r_n`。结论与原 bridge 逐字相同。
* `hdist_fixed_of_D1_P6B2`：D-5 的中间形 (D1) `d ≤ A₀ r_n + C_{D,T} Q_n^{-1/2}` + `Q_n r_n² → ∞`
  ⇒ 固定 `A_* = A₀ + 1` 的 `hdist`。**D-5：任意 `C(A,T,D) r_n` 的 `hdist` 与单点 `y_n` 版不可
  替代固定 `A_*` 形**（window κ 的 `A` 同时控制放大距离与种子体积，不能随 `D, T` 变）；固定
  `A_*` ⇒ `C r_n` 形是平凡的（`C := A_*`），反向不成立，故只提供 (D1) ⇒ 固定 `A_*` 一个方向。
* 口径更正（D-9，R-C11-2 D-R-C11-2-9）：树内无条件的是 **`A ≤ 1/4` 的局部 κ**
  （`localKappaLateAt_of_le_quarter_P6B`，`P6LocalKappaP6B:143`）；`P6StatementP6A` 的 `A ≤ 1`
  （`largerBallCanonicalAt_of_le_one_P6A`，`:129–132`）是改进 canonical 结论的**空真分支**
  （`K₁ = 4`），与 κ 无关，二者不可互替；window 形 **不能** 降到 `A = 1`。
* consumer：selection 输出 ⇒ `hmargin`（纯数值，`∀ n` 经 P6A3 `tendsto_selection_time_margin_P6L`；
  真实 `exists_localized_canonical_time_control_point_selection` 的序列版经 eventually 版）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## (D2) 的数值部分 -/

/-- (D2) ⇒ 原 bridge 的 `hwin`：`Q_n (s_n − (t_n − r_n²/2)) → ∞`、`Q_n > 0` eventually ⇒ 对每个
固定 `T > 0`，eventually `t_n − r_n²/2 ≤ s_n − T/Q_n`。 -/
theorem eventually_window_of_margin_P6B2 {t s r Q : ℕ → ℝ} (hQ : ∀ᶠ n in atTop, 0 < Q n)
    (hmargin : Tendsto (fun n => Q n * (s n - (t n - r n ^ 2 / 2))) atTop atTop) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, t n - r n ^ 2 / 2 ≤ s n - T / Q n := by
  intro T _
  filter_upwards [hQ, hmargin.eventually_ge_atTop T] with n hq hm
  have h : T / Q n ≤ s n - (t n - r n ^ 2 / 2) := by
    rw [div_le_iff₀ hq]
    linarith
  linarith

/-- 反向：原 bridge 的 `hwin`（`∀ T > 0` eventually）⇒ (D2) `Tendsto` 形。 -/
theorem tendsto_margin_of_eventually_window_P6B2 {t s r Q : ℕ → ℝ}
    (hQ : ∀ᶠ n in atTop, 0 < Q n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, t n - r n ^ 2 / 2 ≤ s n - T / Q n) :
    Tendsto (fun n => Q n * (s n - (t n - r n ^ 2 / 2))) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hQ, hwin (max b 1) (lt_max_of_lt_right one_pos)] with n hq hw
  have h : max b 1 / Q n ≤ s n - (t n - r n ^ 2 / 2) := by linarith
  rw [div_le_iff₀ hq] at h
  linarith [le_max_left b 1]

/-- `hwin ⇔ (D2)`（`Q > 0` eventually）：原 bridge 的 `hwin` 本就是 (D2) 的 `∀ T` 形。 -/
theorem tendsto_margin_iff_window_P6B2 {t s r Q : ℕ → ℝ} (hQ : ∀ᶠ n in atTop, 0 < Q n) :
    Tendsto (fun n => Q n * (s n - (t n - r n ^ 2 / 2))) atTop atTop ↔
      ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, t n - r n ^ 2 / 2 ≤ s n - T / Q n :=
  ⟨eventually_window_of_margin_P6B2 hQ, tendsto_margin_of_eventually_window_P6B2 hQ⟩

/-- P6A3 `tendsto_selection_time_margin_P6L` 的 eventually 版：selection 输出
`T_n − r_n²/2 ≤ s_n − L_n²/Q_n`（`n` 充分大）、`Q_n > 0` eventually、`L_n → ∞` ⇒ (D2)。 -/
theorem tendsto_margin_of_eventually_selection_P6B2 {T s r Q L : ℕ → ℝ}
    (hQ : ∀ᶠ n in atTop, 0 < Q n)
    (hsel : ∀ᶠ n in atTop, T n - r n ^ 2 / 2 ≤ s n - L n ^ 2 / Q n)
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => Q n * (s n - (T n - r n ^ 2 / 2))) atTop atTop := by
  have hL2 : Tendsto (fun n => L n ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hL
  refine tendsto_atTop_mono' atTop ?_ hL2
  filter_upwards [hQ, hsel] with n hq hs
  have h : L n ^ 2 / Q n ≤ s n - (T n - r n ^ 2 / 2) := by linarith
  calc L n ^ 2 = Q n * (L n ^ 2 / Q n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hq.le

/-! ## bridge：(D2) 形前提 + D-5 固定 `A_*` -/

/-- **M5 → M8 bridge，(D2) / D-5 版**：`tracedKappa_of_window_P6B` 的 `hwin` 换成 (D2) 的
`Tendsto` 形 `hmargin`（+ `R > 0` eventually）。window κ 取在 `A_* = Astar`，种子体积取在
`A₀ ≤ Astar`（D-5：`A_*` 固定、不随 `D, T`；`A₀ = Astar` 即原 bridge），`hdist` 保持显式前提，
右端 `Astar * r n`。结论与原 bridge 逐字相同（即 `exists_local_ancient_limit_kappa_noncollapsed_P6B`
的 `hkappa`，`ρnc := fun n => r n / 200`）。 -/
theorem tracedKappa_of_window_margin_P6B2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A₀ Astar κ : ℝ} (hA₀ : 0 < A₀) (hA₀le : A₀ ≤ Astar)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) Astar κ) (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A₀⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ᶠ n in atTop, 0 < R n)
    (hmargin : Tendsto (fun n => R n * ((s n : ℝ) - ((t n : ℝ) - r n ^ 2 / 2))) atTop atTop)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (Astar * r n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvt : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r n / 200 →
        (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) r'' :=
  tracedKappa_of_window_P6B hW ind t p r hlate htime hsmall
    (fun n => (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (inv_anti₀ hA₀ hA₀le)
      (pow_nonneg (hsmall n).1.le 3))).trans (hvol n))
    aSeed haT hclock seedTrace s hst y R
    (eventually_window_of_margin_P6B2 (t := fun n => (t n : ℝ)) (s := fun n => (s n : ℝ))
      hR hmargin) hdist

/-! ## D-5：(D1) ⇒ 固定 `A_*` 的 `hdist` -/

/-- **D-5 adapter**：中间形 (D1)（`d ≤ A₀ r_n + C_{D,T} Q_n^{-1/2}`，`C` 可依赖 `D, T`）+
`Q_n r_n² → ∞` ⇒ 固定 `A_* = A₀ + 1`、与 `D, T` 无关的 `hdist`（`Q_n r_n² → ∞ ⇒
C Q_n^{-1/2} ≤ r_n` eventually）。**D-5：原形不可反向替代**——固定 `A_*` ⇒ `C(D,T) r_n` 形是平凡的
（`C := A_*`），但任意 `C(A,T,D) r_n` 形不给出与 `D, T` 无关的 `A_*`，不能喂 window κ。 -/
theorem hdist_fixed_of_D1_P6B2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A₀ : ℝ} (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n)
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ᶠ n in atTop, 0 < R n)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hD1 : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A₀ * r n + C / Real.sqrt (R n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal ((A₀ + 1) * r n) := by
  intro D T hD hT
  obtain ⟨C, hC⟩ := hD1 D T hD hT
  have hsq : Tendsto (fun n => Real.sqrt (R n * r n ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hX
  have hlim : Tendsto (fun n => Real.sqrt (R n) * r n) atTop atTop :=
    hsq.congr' (by
      filter_upwards [hR] with n hn
      rw [Real.sqrt_mul hn.le, Real.sqrt_sq (hr n).le])
  filter_upwards [hC, hR, hlim.eventually_ge_atTop C] with n hn hRn hCn
  intro x hx v hvs hv tr hav
  refine (hn x hx v hvs hv tr hav).trans_le (ENNReal.ofReal_le_ofReal ?_)
  have hCr : C / Real.sqrt (R n) ≤ r n := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hRn)]
    linarith
  linarith

/-! ## consumer：selection 输出 ⇒ (D2) -/

/-- consumer 1（纯数值，`∀ n`）：selection 输出 `T_n − r_n²/2 ≤ s_n − L_n²/Q_n`、`L_n → ∞`
（P6A3 `exists_selection_margin_scale_P6L` 的 `L`）、`Q_n > 0` ⇒ 经 P6A3
`tendsto_selection_time_margin_P6L` 得 (D2) `hmargin`，再得新 bridge 要的 `hwin` 形。 -/
example {T s r Q L : ℕ → ℝ} (hQ : ∀ n, 0 < Q n)
    (hsel : ∀ n, T n - r n ^ 2 / 2 ≤ s n - L n ^ 2 / Q n) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => Q n * (s n - (T n - r n ^ 2 / 2))) atTop atTop ∧
      ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, T n - r n ^ 2 / 2 ≤ s n - T' / Q n :=
  ⟨tendsto_selection_time_margin_P6L hQ hsel hL,
    eventually_window_of_margin_P6B2 (Eventually.of_forall hQ)
      (tendsto_selection_time_margin_P6L hQ hsel hL)⟩

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn in
/-- consumer 2（真实 selection ⇒ (D2)）：树内 point selection
`ObservedHistory.exists_localized_canonical_time_control_point_selection`（`R0_n r_n² → ∞`，取
P6A3 `exists_selection_margin_scale_P6L` 的 `L_n → ∞`）逐 `n`（充分大）给出坏点 `(s_n, y_n)`，
`s_n ≤ T_n`、`Q_n = R(s_n, y_n) > 0`、`T_n − r_n²/2 ≤ s_n − L_n²/Q_n`；对小 `n` 补 `(T_n, p_n)`；
得序列 `(s, y)`，`Q_n := R(s_n, y_n)` 满足新 bridge 的 `hR`、`hst`、(D2) `hmargin`
（`hwin` 形再由 `eventually_window_of_margin_P6B2` 得到）。 -/
example (H : ℕ → ObservedHistory.{u}) (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (z : ((H n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (z : ((H n).stageAt v).Carrier),
      (H n).time ((H n).activeStage v) < (v : ℝ) → (v : ℝ) < (H n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((H n).stageMetric ((H n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) z ^ 2)
    (T : ∀ n, Icc (0 : ℝ) (H n).horizon) (p : ∀ n, ((H n).stageAt (T n)).Carrier)
    (r A : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hA : ∀ n, 0 < A n)
    (aSeed : ∀ n, Icc (0 : ℝ) (H n).horizon) (haT : ∀ n, aSeed n ≤ T n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (T n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (H n) ((H n).activeStage (aSeed n))
      ((H n).activeStage (T n)) ((H n).activeStage_mono (haT n)) (p n))
    (x : ∀ n, ((H n).stageAt (T n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (T n)) (T n)) (p n)
      (A n * r n))
    (hR : ∀ n, 0 < metricScalarAt ((H n).stageMetric ((H n).activeStage (T n)) (T n)) (x n))
    (hbad : ∀ n, ¬ (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (T n) (x n))
    (hX : Tendsto (fun n =>
      metricScalarAt ((H n).stageMetric ((H n).activeStage (T n)) (T n)) (x n) * r n ^ 2)
      atTop atTop) :
    ∃ (L : ℕ → ℝ) (s : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (s n)).Carrier),
      Tendsto L atTop atTop ∧ (∀ n, s n ≤ T n) ∧
      (∀ᶠ n in atTop,
        0 < metricScalarAt ((H n).stageMetric ((H n).activeStage (s n)) (s n)) (y n)) ∧
      Tendsto (fun n =>
        metricScalarAt ((H n).stageMetric ((H n).activeStage (s n)) (s n)) (y n) *
          ((s n : ℝ) - ((T n : ℝ) - r n ^ 2 / 2))) atTop atTop := by
  obtain ⟨L, hL, hev⟩ := exists_selection_margin_scale_P6L hR hr hX
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (hL.eventually_gt_atTop 0))
  have hex : ∀ n, ∃ (s : Icc (0 : ℝ) (H n).horizon) (y : ((H n).stageAt s).Carrier),
      s ≤ T n ∧ (N ≤ n →
        0 < metricScalarAt ((H n).stageMetric ((H n).activeStage s) s) y ∧
        (T n : ℝ) - r n ^ 2 / 2 ≤ (s : ℝ) -
          L n ^ 2 / metricScalarAt ((H n).stageMetric ((H n).activeStage s) s) y) := by
    intro n
    by_cases hn : N ≤ n
    · obtain ⟨hn1, hLpos⟩ := hN n hn
      obtain ⟨s, has, hsT, y, hsel⟩ :=
        (H n).exists_localized_canonical_time_control_point_selection (q n) hC1 hC2 hCtime
          (hanti n) (hcanonical n) (hderivative n) (T n) (p n) (r n) (A n) (L n) (hr n) (hA n)
          hLpos (aSeed n) (haT n) (haSeed n) (seedTrace n) (x n) (hx n) (hR n) (hbad n)
          hn1.1 hn1.2
      dsimp only at hsel
      obtain ⟨-, hQ, -, -, -, hmargin, -⟩ := hsel
      exact ⟨s, y, hsT, fun _ => ⟨hQ, hmargin⟩⟩
    · exact ⟨T n, p n, le_rfl, fun h => absurd h hn⟩
  choose s y hsT hsel using hex
  have hQ : ∀ᶠ n in atTop,
      0 < metricScalarAt ((H n).stageMetric ((H n).activeStage (s n)) (s n)) (y n) :=
    eventually_atTop.2 ⟨N, fun n hn => (hsel n hn).1⟩
  refine ⟨L, s, y, hL, hsT, hQ, ?_⟩
  exact tendsto_margin_of_eventually_selection_P6B2
    (T := fun n => (T n : ℝ)) (s := fun n => (s n : ℝ)) hQ
    (eventually_atTop.2 ⟨N, fun n hn => (hsel n hn).2⟩) hL

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact

/-- consumer 3（端到端，(D2) 版）：window κ（`A_*`）+ (D2) 时间余量 `hmargin` + 固定 `A_*` 的
`hdist` + 坏点处 traced regions、种子体积、trace-local pinching ⇒ 坏点序列的局部古代极限对每个 `ρ`
是 `κ/250`-noncollapsed（与原 consumer 同结论；`hwin` 由 `hmargin` 经新 bridge 内部给出）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A₀ Astar κ : ℝ} (hκ : 0 < κ) (hA₀ : 0 < A₀)
    (hA₀le : A₀ ≤ Astar)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) Astar κ) (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A₀⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hmargin : Tendsto (fun n => R n * ((s n : ℝ) - ((t n : ℝ) - r n ^ 2 / 2))) atTop atTop)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (Astar * r n))
    (htraced : ∀ A' T : ℝ, 0 < A' → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (F.tower.history (ind n)).toHistory.isTracedRegion (s n) (y n)
        (A' / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel
          ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier
          ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n))
          (riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvt : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)))
          (Phi (metricScalarAt ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt))))) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P' : CheegerGromovCompactness.PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : CheegerGromovCompactness.PointedRiemannianConvergenceMaps
          ({ obj := fun n =>
            { M := ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier
              basepoint := y n
              metric := scaleMetric (R n) (hR n)
                ((F.tower.history (ind n)).toHistory.stageMetric
                  ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) } } :
            CheegerGromovCompactness.PointedRiemannianSeq.{u, 0, 0} ThreeModel) P' f),
        CheegerGromovCompactness.MetricComplete P' ∧ ConnectedSpace P'.M ∧
        ∃ (G : ℝ → SmoothRiemannianMetric ThreeModel P'.M)
          (_ : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P'.M)
            Perelman.CanonicalNeighborhood.ancientTimeInterval)),
          G 0 = P'.metric ∧
          ∀ ρ : ℝ, 0 < ρ → Perelman.ParabolicallyKappaNoncollapsedBelowScale
            ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P'.M)
              Perelman.CanonicalNeighborhood.ancientTimeInterval) (κ / 250) ρ :=
  ObservedHistory.exists_local_ancient_limit_kappa_noncollapsed_P6B
    (fun n => (F.tower.history (ind n)).toHistory) s y R hR hRlim htraced hr₀ hw hseed hκ
    (fun n => r n / 200) hradii
    (tracedKappa_of_window_margin_P6B2 hA₀ hA₀le hW ind t p r hlate htime hsmall hvol aSeed haT
      hclock seedTrace s hst y R (Eventually.of_forall hR) hmargin hdist) hPhi hpinch

end GC.LongTime.Ch11
