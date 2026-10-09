import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalUContractP6M5
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardScalar

/-!
# `hscalU` 的 short-depth 形 `HUshort_P6M5` + 时间部分引理（S-CH11-HSCALU G2，后缀 `_P6M5`）

R-C11-7 处置 D-1 / D-3：逐点导数界 `|∂ₛR| ≤ Ctime·R²` 只能给**浅深度**上的标量界；长深度 `HU_P6M5 B`
（G1）仍是独立 analytic obligation。本文件把"ODE 可付的时间部分"与"仍要显式 binder 的空间部分"分开登记。

* **时间部分（树内可用，本文件已证）**：`IncomingSlab.scalar_le_of_reciprocal_window_P6M5`
  （`1/max(q, R)` 的 `Ctime`-Lipschitz ⇒ `R(v, z) ≤ A` 推出 `R(s, z) ≤ B'`，`Ctime |v − s| ≤ A⁻¹ − B'⁻¹`）
  与 `scalar_le_two_mul_window_P6M5`（`R(v, z) ≤ C₀Q`、`0 ≤ B`、`2 Ctime C₀ B ≤ 1`、
  `s ∈ [v − B/Q, v] ∩ (a_j, b_j)` ⇒ `R(s, z) ≤ 2 C₀ Q`——D-1 的"深度 `≤ 1/(2 Ctime C₀)`"）。
  导数界的树内形 = `OrientedThreeStage.IncomingSlab.DerivativeBoundBefore`（= `EventSlabsDerivative` 的
  字段，`RetainedCoreHistory.hder_of_eventSlabsDerivative_P6M5` 一行接线）。
* **`ObservedHistory.HUshort_P6M5 … Ctime C₀ B : Prop`**：D-3 short-depth 形——`R_j(v, x) ≤ C₀ q_w`、
  `0 ≤ B`、`2 Ctime C₀ B ≤ 1`、同一 open slab、`ExitGuard(s, x)` ⇒ `∀ s ∈ [v − B/q_w, v] ∩ (a_j, b_j)`、
  `∀ z ∈ B_{g_j(s)}(x, (C_U q_w)^{-1/2})`，`R_j(s, z) ≤ C_U q_w`。**本文件不无条件证它**。
* `HUshort_of_HU_P6M5`：long ⇒ short（去掉 `R_j(v, x) ≤ C₀ q_w` 前提与预算前提即得；反向不成立，因深度）。
* `HU_P6M5_of_short_P6M5`：**short + 顶切片界 ⇒ long（`B` 在预算内）**。顶切片界 `htop`
  （`s = v` 的 `R_j(v, x) ≤ C₀ q_w`）是独立的显式 binder——D-4 "先核 Q 与 U 端点的归一化及顶切片界"。
* `HUshort_of_time_space_P6M5`：**short ⇐ 时间部分 + 空间部分显式 binder `hspace`**。
  `hspace`（witness-ball / gradient 链 + 小球上 `R(v, ·) ≤ (5/4) C₀ q_w`；定义域包含由 slab 的固定
  `Carrier` 自动给出）是剩余的空间义务；它**不独立于时间部分**（把 `s` 时刻的球输运到 `v` 需要窗内
  Ricci 界，那是首出 / continuity 论证），此处只作显式 binder，不声称已证。
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

/-! ### 时间部分（单 open slab，逐点导数界 ⇒ `1/max(q, R)` Lipschitz） -/

/-- **时间部分，一般形（`_P6M5`）**：固定点 `z`，`|∂ₛR| ≤ C R²`（`R > q` 处，开 slab `(a, b)` 内）。
`R(v, z) ≤ A`、`q ≤ A` 且 `C |v − s| ≤ A⁻¹ − B'⁻¹` ⇒ `R(s, z) ≤ B'`。 -/
theorem OrientedThreeStage.IncomingSlab.scalar_le_of_reciprocal_window_P6M5
    {P : OrientedThreeStage.{u}} {a b : ℝ} (G : P.IncomingSlab a b) {C : ℝ≥0} {q A B' s v : ℝ}
    (hq : 0 < q) (z : P.Carrier)
    (hbound : ∀ t ∈ Ioo a b, q < G.flow.scalar t z →
      |derivWithin (fun w => G.flow.scalar w z) (Iic t) t| ≤ C * G.flow.scalar t z ^ 2)
    (hqA : q ≤ A) (hB' : 0 < B') (hs : s ∈ Ioo a b) (hv : v ∈ Ioo a b)
    (hend : G.flow.scalar v z ≤ A) (htime : (C : ℝ) * |v - s| ≤ A⁻¹ - B'⁻¹) :
    G.flow.scalar s z ≤ B' := by
  have hlip := (G.lipschitzOnWith_inv_max_scalar_at hq z hbound).mono Ioo_subset_Ico_self
  have hd := hlip.dist_le_mul s hs v hv
  rw [Real.dist_eq, Real.dist_eq] at hd
  have hmv : 0 < max q (G.flow.scalar v z) := hq.trans_le (le_max_left _ _)
  have hms : 0 < max q (G.flow.scalar s z) := hq.trans_le (le_max_left _ _)
  have hinv : A⁻¹ ≤ (max q (G.flow.scalar v z))⁻¹ := inv_anti₀ hmv (max_le hqA hend)
  have habs : |s - v| = |v - s| := abs_sub_comm s v
  have hlow : B'⁻¹ ≤ (max q (G.flow.scalar s z))⁻¹ := by
    have h1 := (abs_le.mp hd).1
    rw [habs] at h1
    linarith
  exact (le_max_right _ _).trans ((inv_le_inv₀ hB' hms).mp hlow)

/-- **时间部分，D-1 形（`_P6M5`）**：`R(v, z) ≤ C₀ Q`、`0 < q ≤ C₀ Q`、`2 C C₀ B ≤ 1`、
`s ∈ [v − B/Q, v] ∩ (a, b)` ⇒ `R(s, z) ≤ 2 C₀ Q`（深度 `B/Q ≤ 1/(2 C C₀ Q)`；更深处不排除 backward
blow-up）。 -/
theorem OrientedThreeStage.IncomingSlab.scalar_le_two_mul_window_P6M5
    {P : OrientedThreeStage.{u}} {a b : ℝ} (G : P.IncomingSlab a b) {C : ℝ≥0}
    {q C₀ Q B s v : ℝ} (hq : 0 < q) (z : P.Carrier)
    (hbound : ∀ t ∈ Ioo a b, q < G.flow.scalar t z →
      |derivWithin (fun w => G.flow.scalar w z) (Iic t) t| ≤ C * G.flow.scalar t z ^ 2)
    (hQ : 0 < Q) (hC₀ : 0 < C₀) (hqA : q ≤ C₀ * Q) (hbud : 2 * C * C₀ * B ≤ 1)
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo a b) (hsv : s ≤ v) (hsB : v - B / Q ≤ s)
    (hend : G.flow.scalar v z ≤ C₀ * Q) : G.flow.scalar s z ≤ 2 * (C₀ * Q) := by
  have hCQ : 0 < C₀ * Q := mul_pos hC₀ hQ
  refine G.scalar_le_of_reciprocal_window_P6M5 hq z hbound hqA (by positivity) hs hv hend ?_
  have h1 : (C : ℝ) * |v - s| ≤ C * (B / Q) := by
    apply mul_le_mul_of_nonneg_left _ C.2
    rw [abs_of_nonneg (sub_nonneg.mpr hsv)]
    linarith
  have h2 : (C₀ * Q)⁻¹ - (2 * (C₀ * Q))⁻¹ = 1 / (2 * C₀ * Q) := by
    field_simp
    ring
  have h3 : (C : ℝ) * (B / Q) ≤ 1 / (2 * C₀ * Q) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hQ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hbud hQ.le]
  rw [h2]
  exact h1.trans h3

/-- 树内接线：`RetainedCoreHistory` 的 `EventSlabsDerivative`（最后一个 stage 之前的全部 slab）给出每个
incoming slab 的 `DerivativeBoundBefore`（`toHistory` 是 `abbrev`，定义等同）。 -/
theorem RetainedCoreHistory.hder_of_eventSlabsDerivative_P6M5 (K : RetainedCoreHistory.{u})
    {Ctime : ℝ≥0} {q : ℝ} (h : K.EventSlabsDerivative Ctime q (Fin.last K.eventCount))
    (j' : Fin K.eventCount) :
    (K.toHistory.event j').incoming.DerivativeBoundBefore Ctime q (K.toHistory.time j'.succ) :=
  h j' (Fin.castSucc_lt_last j')

/-! ### short-depth 形 -/

/-- **`HUshort_P6M5 … Ctime C₀ B`：`hscalU` 的 short-depth 形（D-3，`_P6M5`）**。
`R_j(v, x) ≤ C₀ q_w`、`0 ≤ B`、`0 < C₀`、`2 Ctime C₀ B ≤ 1`、同一 open slab、`ExitGuard(s, x)` ⇒
`∀ z ∈ B_{g_j(s)}(x, (C_U q_w)^{-1/2})`，`R_j(s, z) ≤ C_U q_w`（`C_U` 在 `n, j, v, w, x, s` 之前）。
**本文件不无条件证它**：时间部分已证（上），空间部分见 `HUshort_of_time_space_P6M5` 的 `hspace`。 -/
def ObservedHistory.HUshort_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (Ctime : ℝ≥0) (C₀ B : ℝ) : Prop :=
  0 ≤ B → 0 < C₀ → 2 * Ctime * C₀ * B ≤ 1 →
  ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
        ((Kh n).event j').incoming.flow.scalar v x ≤
          C₀ * ((Kh n).event j').incoming.flow.scalar v w →
      ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        (Kh n).time j'.castSucc < s →
        ObservedHistory.ExitGuard_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n j' h1 h2 s x →
        ∀ z : ((Kh n).stage j'.castSucc).Carrier,
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
            ((Kh n).event j').incoming.flow.scalar s z ≤
              C * ((Kh n).event j').incoming.flow.scalar v w

/-- **long ⇒ short（`_P6M5`）**：`HU_P6M5 B` 蕴含任意 `(Ctime, C₀)` 的 short 形（丢掉两个前提）。反向不成立：
short 形的预算 `2 Ctime C₀ B ≤ 1` 限制深度，long 形的 `B` 不受限（D-1：逐点 ODE 不能推长窗界）。 -/
theorem ObservedHistory.HUshort_of_HU_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (Ctime : ℝ≥0) (C₀ B : ℝ)
    (h : ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    ObservedHistory.HUshort_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L Ctime C₀ B := by
  intro _ _ _ Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨C, hC, hev⟩ := h Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨C, hC, hev.mono ?_⟩
  intro n hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx _ s hs1 hsv hs3 hg z hz
  exact hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx s hs1 hsv hs3 hg z hz

/-- **short + 顶切片界 ⇒ long（`B` 在预算内，`_P6M5`）**：`htop`（`s = v` 的 `R_j(v, x) ≤ C₀ q_w`，
宏观参数在 `∀ᶠ n` 之前）是独立的显式 binder——D-4 的"顶切片界（`R_j(v, x)` vs `q_w`）"。 -/
theorem ObservedHistory.HU_P6M5_of_short_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (Ctime : ℝ≥0) (C₀ B : ℝ) (hB : 0 ≤ B) (hC₀ : 0 < C₀) (hbud : 2 * Ctime * C₀ * B ≤ 1)
    (hshort : ObservedHistory.HUshort_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L Ctime C₀ B)
    (htop : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
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
        ((Kh n).event j').incoming.flow.scalar v x ≤
          C₀ * ((Kh n).event j').incoming.flow.scalar v w) :
    ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B := by
  intro Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨C, hC, hev⟩ := hshort hB hC₀ hbud Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, htop Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd] with n hn ht
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx s hs1 hsv hs3 hg z hz
  exact hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx (ht j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx) s hs1 hsv hs3 hg z hz

/-- **short ⇐ 时间部分 + 空间部分显式 binder（`_P6M5`）**。
* `hder`：每个 incoming slab 的逐点导数界（树内 `DerivativeBoundBefore`，阈值 `qthr n`）；
* `hqpos` / `hq`：阈值 `0 < qthr n ≤ (5/4) C₀ R n`（`R n ≤ q_w`）；
* **`hspace`（空间部分，独立 obligation）**：`R(v, x) ≤ C₀ q_w` 且 `ExitGuard(s, x)` 时，`s` 时刻小球
  `B_{g_j(s)}(x, (Cb q_w)^{-1/2})` 内的点 `z` 在**顶时刻 `v`** 有 `R(v, z) ≤ (5/4) C₀ q_w`（
  witness-ball / gradient 链 + 距离畸变输运；`5/4` 可换任意 `θ < 2`，对应结论常数 `2θ/(2−θ) C₀`）。
结论常数 `C_U = max Cb (4 C₀)`。时间部分用 `scalar_le_of_reciprocal_window_P6M5`（`A = (5/4) C₀ q_w`，
`B' = 4 C₀ q_w`，`A⁻¹ − B'⁻¹ = (11/20)/(C₀ q_w) ≥ 1/(2 C₀ q_w) ≥ Ctime B/q_w`）。 -/
theorem ObservedHistory.HUshort_of_time_space_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (Ctime : ℝ≥0) (qthr : ℕ → ℝ) (hqpos : ∀ n, 0 < qthr n)
    (hder : ∀ n (j' : Fin (Kh n).eventCount),
      ((Kh n).event j').incoming.DerivativeBoundBefore Ctime (qthr n) ((Kh n).time j'.succ))
    (C₀ B : ℝ) (hq : ∀ᶠ n in atTop, qthr n ≤ 5 / 4 * C₀ * R n)
    (hspace : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ Cb : ℝ, 1 ≤ Cb ∧ ∀ᶠ n in atTop,
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
        ((Kh n).event j').incoming.flow.scalar v x ≤
          C₀ * ((Kh n).event j').incoming.flow.scalar v w →
      ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        (Kh n).time j'.castSucc < s →
        ObservedHistory.ExitGuard_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n j' h1 h2 s x →
        ∀ z : ((Kh n).stage j'.castSucc).Carrier,
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt (Cb * ((Kh n).event j').incoming.flow.scalar v w)) →
            ((Kh n).event j').incoming.flow.scalar v z ≤
              5 / 4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w)) :
    ObservedHistory.HUshort_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L Ctime C₀ B := by
  intro _ hC₀ hbud Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨Cb, hCb, hev⟩ := hspace Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨max Cb (4 * C₀), le_max_of_le_left hCb, ?_⟩
  filter_upwards [hev, hq] with n hn hqn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx htopx s hs1 hsv hs3 hg z hz
  have hRn := hR n
  have hQ : 0 < ((Kh n).event j').incoming.flow.scalar v w := hRn.trans_le hRw
  have hCb0 : 0 < Cb := lt_of_lt_of_le one_pos hCb
  have hrad : 1 / Real.sqrt (max Cb (4 * C₀) * ((Kh n).event j').incoming.flow.scalar v w) ≤
      1 / Real.sqrt (Cb * ((Kh n).event j').incoming.flow.scalar v w) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos hCb0 hQ))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le))
  have hz' := hz.trans_le (ENNReal.ofReal_le_ofReal hrad)
  have hend := hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2
      w hwseed hwnear hRw x hx htopx s hs1 hsv hs3 hg z hz'
  have hqA : qthr n ≤ 5 / 4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w) := by
    have : 5 / 4 * C₀ * R n ≤ 5 / 4 * C₀ * ((Kh n).event j').incoming.flow.scalar v w :=
      mul_le_mul_of_nonneg_left hRw (by positivity)
    linarith
  have hsb : s ∈ Ioo ((Kh n).time j'.castSucc) ((Kh n).time j'.succ) := ⟨hs3, hsv.trans_lt hv2⟩
  have hvb : v ∈ Ioo ((Kh n).time j'.castSucc) ((Kh n).time j'.succ) := ⟨hv1, hv2⟩
  have hCQ : 0 < C₀ * ((Kh n).event j').incoming.flow.scalar v w := mul_pos hC₀ hQ
  have hC₀' := hC₀.ne'
  have hQ' := hQ.ne'
  have h1 : (Ctime : ℝ) * |v - s| ≤ Ctime * (B / ((Kh n).event j').incoming.flow.scalar v w) := by
    apply mul_le_mul_of_nonneg_left _ Ctime.2
    rw [abs_of_nonneg (sub_nonneg.mpr hsv)]
    linarith
  have h2 : (5 / 4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w))⁻¹ -
      (4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w))⁻¹ =
      11 / (20 * C₀ * ((Kh n).event j').incoming.flow.scalar v w) := by
    field_simp
    ring
  have h3 : (Ctime : ℝ) * (B / ((Kh n).event j').incoming.flow.scalar v w) ≤
      11 / (20 * C₀ * ((Kh n).event j').incoming.flow.scalar v w) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hQ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hbud hQ.le]
  have hlt : (Ctime : ℝ) * |v - s| ≤
      (5 / 4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w))⁻¹ -
        (4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w))⁻¹ := by
    rw [h2]
    exact h1.trans h3
  have htime := ((Kh n).event j').incoming.scalar_le_of_reciprocal_window_P6M5 (hqpos n) z
    (fun t ht hqt => hder n j' z t ht hqt) hqA
    (by positivity : 0 < 4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w)) hsb hvb hend hlt
  have hmax := mul_le_mul_of_nonneg_right (le_max_right Cb (4 * C₀)) hQ.le
  nlinarith [htime, hmax]

/-- **consumer（`_P6M5`）**：`hder`（树内导数界）+ `hq` + 显式空间 binder `hspace` ⇒ short 形 ⇒（加显式
顶切片界 `htop`）⇒ `B` 在预算内的 long 形 `HU_P6M5 … B`。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hR : ∀ n, 0 < R n) (Ctime : ℝ≥0) (qthr : ℕ → ℝ) (hqpos : ∀ n, 0 < qthr n)
    (hder : ∀ n (j' : Fin (Kh n).eventCount),
      ((Kh n).event j').incoming.DerivativeBoundBefore Ctime (qthr n) ((Kh n).time j'.succ))
    (C₀ B : ℝ) (hB : 0 ≤ B) (hC₀ : 0 < C₀) (hbud : 2 * Ctime * C₀ * B ≤ 1)
    (hq : ∀ᶠ n in atTop, qthr n ≤ 5 / 4 * C₀ * R n)
    (hspace : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ Cb : ℝ, 1 ≤ Cb ∧ ∀ᶠ n in atTop,
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
        ((Kh n).event j').incoming.flow.scalar v x ≤
          C₀ * ((Kh n).event j').incoming.flow.scalar v w →
      ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        (Kh n).time j'.castSucc < s →
        ObservedHistory.ExitGuard_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n j' h1 h2 s x →
        ∀ z : ((Kh n).stage j'.castSucc).Carrier,
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt (Cb * ((Kh n).event j').incoming.flow.scalar v w)) →
            ((Kh n).event j').incoming.flow.scalar v z ≤
              5 / 4 * (C₀ * ((Kh n).event j').incoming.flow.scalar v w))
    (htop : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
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
        ((Kh n).event j').incoming.flow.scalar v x ≤
          C₀ * ((Kh n).event j').incoming.flow.scalar v w) :
    ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B :=
  ObservedHistory.HU_P6M5_of_short_P6M5
    Kh Tn aSeed σ haT hsT has pT seedTrace y R L Ctime C₀ B hB hC₀ hbud
    (ObservedHistory.HUshort_of_time_space_P6M5
      Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR Ctime qthr hqpos hder C₀ B hq hspace)
    htop

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
