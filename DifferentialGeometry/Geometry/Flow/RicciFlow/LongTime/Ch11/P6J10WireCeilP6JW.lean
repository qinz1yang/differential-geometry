import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabProtCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CoreSurviveP6JC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10ExtendAtCeilingCXJF2

/-!
# J10WIRE G1：first-exit ceiling 接进 hceil / hsurvive（O-CH11-J10WIRE，后缀 `_P6JW`）

* `crossSlab_numerics_P6JW`（PROVED）：CXJD 的八条数值前提由 `ℓ = c/√R`、`K = R/c²` 付清
  （`c` 只依赖 `C₂′, Q_b, r`），剩下 `D + 8T/c < L/2`、`2ρ/√(2Q_b) ≤ L/2`、`1 ≤ R`，序列层由
  `L → ∞`、`R → ∞` 付。
* **G1** `ObservedHistory.hceil_of_firstExit_P6JW`（PROVISIONAL，CXJD binder 族）：
  `exists_crossSlab_ceiling_CXJD` 逐 `(x, w, B)` 应用 ⇒ 序列层 `hceil` 形（球上界 `≤ Cball·R` ⇒ 窗口内每个起点
  每条 backward trace 上 `R ≤ 2·Q_b·R`）。**无 `hslabW`、无 `hstopX`**；CXJD 不要求窗口跨 event，所以
  年龄分情形在这里**不需要**。binder：`hC2`、seed（`hsmall` / `hclock` / `seedTrace`，K0）、Hamilton–Ivey
  `hpin`（`a₀`）、`hgood`、`hQb`、`hσlast`（σ 在 event slab 内部）、`hwin`、`hRa`（`1 ≤ R·aSeed`）、records 族
  （`q`、`T₀ ≤ aSeed`、`records`、`hOld`、`hcan`、`hDm`、`hacc ≤ 1/(n+1)`、`hm`）、`hscale`（aSeed 之后的 event：
  `2·max{3/r², 2Q_bR} < scale`）、`hfin`（端点距离有限）、`hRlim`、`hL`。
* **G1″** `ObservedHistory.hceil_of_firstExit_extendAt_P6JW`（PROVISIONAL，同一 binder 族、
  **无** `hσlast`）：
  `Kh = extendAt` 族（`hKh`，即 J10CORE 的 `hHs` 形）上用 CX-J10FIN2 `exists_extendAt_ceiling_CXJF2`
  （σ 可等于 horizon）。J10CORE `hsurvive_noJ10_P6JC` 的 `hceil` 在 `(Hs n, ts n)` 上量化，
  `Hs = extendAt = extendHorizon`、`ts = extendAtTime = ⟨t, _, le_rfl⟩` = **horizon（final slab）**，所以
  CXJD 的 `hσlast` 与 CXJF 的 `σ < horizon` 在这里都恒假，只有 CXJF2 形可用。
* **G1 接线** `RetainedCoreHistory.hsurvive_noJ10_firstExit_P6JW`：`hsurvive_noJ10_P6JC` 以 G1″ 为
  `hceil`
  （`Q_b := max (max Cball Cg) 1`），结论逐字；**无 `hslabW`、无 `hstopX`、无 `hdistW`、无年龄分情形**
  （CXJD / CXJF2 都不要求窗口跨 event，老 / 年轻坏点一并覆盖）。新增 binder 只有 CXJD 族（`X` 后缀避免与
  hsurvive 自身的 `records` / `hscale` / `T₀` / `a₀` 重名）。
**R-C11-17 验收点对账**（CXJD 链）：
(1) 端点球控制：`hRicC_of_hgood_ceiling_CXJD` 的结论是两端点（seed trace 点与 `A` 的点）的**整个**
  `ℓ`-球、球内每点 `w`、每个切向量 `ξ` 上的 `Ric ≤ (3/ℓ²)g`，对 `(a, σ)` 内每个时刻 `t`（条件：`[t, σ]` 上 Good）
  ——满足。
(2) 跨 event 距离运输：`edist_trace_le_of_stage_bounds_C11D` 的 `hevent`（由 `event_crossing_bound_C11D`
  给）是 `d_{e⁻,t} ≤ d_{e⁺,τ} + (8/ℓ)(τ − t)`，跳跃为零（`surgery_no_shortcut_C11D` 的 terminal 极限对每个
  `δ > 0` 成立），所以 `E_cross = 0`，总误差是线性的 `(8/ℓ)(σ − v) ≤ (8/ℓ)(T/R)`，**与窗口内 crossing 次数无关**
  （次数 ≤ `eventCount`，不需要上界）——满足。
(3) 量词：`hstopX`（`P6J10PreTraceP6JT.lean:85–115`）要求整个顶层球、窗口内每个起始时刻 `w`、每条 partial
  trace `B`。G1 对每个 `(x ∈ B(y, D/√R), w ∈ [σ − T/R, σ], B)` 取 CXJD 的 `a := w`、`z := x`、`A := B`，
  逐 trace 覆盖到同一量词层——满足（event slab 内用 CXJD，extendAt 的 final slab 含 `σ = horizon` 用 CXJF2）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 数值核（`_P6JW`，PROVED）：`ℓ = c/√R`、`K = R/c²` 满足 CXJD 的八条数值前提。 -/
theorem crossSlab_numerics_core_P6JW {ρ Kc Qb r c R L D T : ℝ} (hKc : 0 < Kc) (hQb : 0 < Qb)
    (hc : 0 < c) (hcr : c ≤ r / 50) (hcK : c ≤ 1 / Real.sqrt Kc)
    (hcρ : c ≤ ρ / Real.sqrt (2 * Qb)) (hR1 : 1 ≤ R)
    (hL1 : D + 8 * T / c < L / 2) (hL2 : 2 * (ρ / Real.sqrt (2 * Qb)) ≤ L / 2) :
    0 < c / Real.sqrt R ∧ R / c ^ 2 * (c / Real.sqrt R) ^ 2 ≤ 1 ∧ c / Real.sqrt R ≤ r / 50 ∧
      1 / r ^ 2 ≤ R / c ^ 2 ∧ Kc * R ≤ R / c ^ 2 ∧
      c / Real.sqrt R ≤ ρ / Real.sqrt (2 * (Qb * R)) ∧
      2 * (ρ / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R ∧
      D / Real.sqrt R + 8 / (c / Real.sqrt R) * (T / R) < L / 2 / Real.sqrt R := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hs1 : 1 ≤ Real.sqrt R := Real.one_le_sqrt.2 hR1
  have hs2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
  have hsplit : Real.sqrt (2 * (Qb * R)) = Real.sqrt (2 * Qb) * Real.sqrt R := by
    rw [← mul_assoc, Real.sqrt_mul (by linarith)]
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  refine ⟨div_pos hc hs, ?_, (div_le_self hc.le hs1).trans hcr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_pow, hs2, div_mul_div_comm, mul_comm R (c ^ 2)]
    exact (div_self (mul_pos hc2 hR0).ne').le
  · have hcr' : c ≤ r := hcr.trans (by linarith)
    have h1 : 1 / r ^ 2 ≤ 1 / c ^ 2 :=
      one_div_le_one_div_of_le hc2 (pow_le_pow_left₀ hc.le hcr' 2)
    exact h1.trans ((div_le_div_iff_of_pos_right hc2).2 hR1)
  · have h1 : c * Real.sqrt Kc ≤ 1 := by
      rw [le_div_iff₀ (Real.sqrt_pos.2 hKc)] at hcK
      exact hcK
    have h3 : (c * Real.sqrt Kc) ^ 2 ≤ 1 :=
      pow_le_one₀ (mul_nonneg hc.le (Real.sqrt_nonneg _)) h1
    rw [mul_pow, Real.sq_sqrt hKc.le] at h3
    rw [le_div_iff₀ hc2]
    nlinarith [mul_nonneg hR0.le (sub_nonneg.2 h3)]
  · rw [hsplit, ← div_div]
    exact (div_le_div_iff_of_pos_right hs).2 hcρ
  · rw [hsplit, ← div_div,
      show 2 * (ρ / Real.sqrt (2 * Qb) / Real.sqrt R) =
        2 * (ρ / Real.sqrt (2 * Qb)) / Real.sqrt R by ring]
    exact (div_le_div_iff_of_pos_right hs).2 hL2
  · have key : ∀ s' : ℝ, 0 < s' → ∀ R' : ℝ, s' ^ 2 = R' →
        8 / (c / s') * (T / R') = 8 * T / c / s' := by
      intro s' hs' R' h
      subst h
      rw [div_div_eq_mul_div, div_mul_div_comm, div_div,
        div_eq_div_iff (mul_pos hc (pow_pos hs' 2)).ne' (mul_pos hc hs').ne']
      ring
    rw [key (Real.sqrt R) hs R hs2, ← add_div]
    exact (div_lt_div_iff_of_pos_right hs).2 hL1

/-- 数值前提的 `∃ c` 形（`_P6JW`，PROVED）：`c` 只依赖 `C₂′, Q_b, r`。 -/
theorem crossSlab_numerics_P6JW {C2' Qb r : ℝ} (hC2 : 0 ≤ C2') (hQb : 1 ≤ Qb) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ {R L D T : ℝ}, 1 ≤ R → D + 8 * T / c < L / 2 →
      2 * (localPropagationRadius C2' / Real.sqrt (2 * Qb)) ≤ L / 2 →
      ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ℓ ≤ r / 50 ∧ 1 / r ^ 2 ≤ K ∧
        2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K ∧
        ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)) ∧
        2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R ∧
        D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R := by
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hKc : 0 < 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) :=
    mul_pos (mul_pos two_pos (Real.sqrt_pos.2 (by norm_num)))
      (add_pos (by linarith) (lt_max_of_lt_right (mul_pos two_pos (Real.exp_pos 4))))
  have hQ2 : 0 < Real.sqrt (2 * Qb) := Real.sqrt_pos.2 (by linarith)
  have hsK := Real.sqrt_pos.2 hKc
  have hc : 0 < min (min (r / 50) (1 / Real.sqrt (2 * Real.sqrt 3 *
      (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4))))) (localPropagationRadius C2' /
        Real.sqrt (2 * Qb)) :=
    lt_min (lt_min (by linarith) (one_div_pos.2 hsK)) (div_pos hρ hQ2)
  refine ⟨_, hc, ?_⟩
  intro R L D T hR1 hL1 hL2
  exact ⟨_, _, crossSlab_numerics_core_P6JW hKc (by linarith) hc
    ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _))
    (min_le_right _ _) hR1 hL1 hL2⟩

namespace ObservedHistory

/-- **G1（`_P6JW`，PROVISIONAL：CXJD binder 族）**：`exists_crossSlab_ceiling_CXJD` 逐 `(x, w, B)` 应用
（`a := w`、`z := x`、`A := B`）⇒ 序列层 `hceil` 形。数值前提由 `crossSlab_numerics_P6JW` 付，records 精度
由 `hacc`（`≤ 1/(n+1)`）eventually `≤ ε₀`。无 `hslabW`、无 `hstopX`；σ 在 event slab 内部（`hσlast`）。 -/
theorem hceil_of_firstExit_P6JW {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb r : ℝ}
    (hC2 : 0 ≤ C2') (hr : 0 < r)
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (t : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage t) t) (a₀ n + t) x)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hσlast : ∀ n, (Kh n).activeStage (σ n) < Fin.last (Kh n).eventCount)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (records : ∀ n (e : Fin (Kh n).eventCount), T₀ n ≤ (Kh n).time e.succ →
      GeometricCutoffRecord (Kh n) e (q n))
    (hOld : ∀ n (e : Fin (Kh n).eventCount), T₀ n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hm : ∀ n, 2 ≤ (q n).modelOrder)
    (hscale : ∀ n (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      (aSeed n : ℝ) < (Kh n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((records n e he).static b).neck.scale)
    (hfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ D T : ℝ, 0 < D → 0 < T → 2 * Ctime' * Qb * T ≤ 1 → ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) x ≤ Cball * R n) →
      ∀ uu : Icc (0 : ℝ) (Kh n).horizon, (uu : ℝ) = σ n - T / R n →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (Kh n).horizon) (_ : uu ≤ w) (hwσ : w ≤ σ n)
        (B : BackwardPointTrace (Kh n) ((Kh n).activeStage w) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) (Kh n).horizon) (hwv : w ≤ v) (hvσ : v ≤ σ n),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (B.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hwv)
            ((Kh n).activeStage_mono hvσ)) ≤ 2 * (Qb * R n) := by
  obtain ⟨ε₀, hε₀, hCX⟩ := exists_crossSlab_ceiling_CXJD.{u}
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  obtain ⟨c, hc, hnum⟩ := crossSlab_numerics_P6JW (C2' := C2') hC2 hQ1 hr
  intro D T hD hT hstep
  have hacc0 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε₀ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε₀)
  filter_upwards [hacc0, hwin T hT, hRlim.eventually_ge_atTop 1,
    hL.eventually_gt_atTop (2 * (D + 8 * T / c)),
    hL.eventually_ge_atTop (4 * (localPropagationRadius C2' / Real.sqrt (2 * Qb))),
    hL.eventually_ge_atTop (T + 1)] with n hεn hwn hRn hL1 hL2 hL3
  intro hball uu huu x hx w huw hwσ B v hwv hvσ
  have huw' : (uu : ℝ) ≤ w := huw
  obtain ⟨ℓ, K, hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hmarg⟩ :=
    hnum (R := R n) (L := L n) (D := D) (T := T) hRn (by linarith) (by linarith)
  have haS : (aSeed n : ℝ) ≤ w := by linarith
  have hTL : T ≤ L n ^ 2 := by nlinarith [sq_nonneg (L n - 1)]
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ w := by
    have h := (div_le_div_iff_of_pos_right (hR n)).2 hTL
    linarith
  have hdepth : (σ n : ℝ) - w ≤ T / R n := by linarith
  have hRa' : 1 ≤ R n * w := (hRa n).trans (mul_le_mul_of_nonneg_left haS (hR n).le)
  exact hCX hC2 (Kh n) (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n)
    (has n) (y n) (L n) (hR n) (hgood n) hQb hstep haS hwσ (hσlast n) haL hdepth hRa'
    (hball x hx) B hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀ n).trans haS) (records n) (hOld n)
    (hcan n) (hDm n) ((hacc n).trans hεn) (hm n)
    (fun e he b hlt => hscale n e he b (lt_of_le_of_lt haS hlt)) hx (hfin n) hmarg v hwv hvσ


/-- **G1″（`_P6JW`，PROVISIONAL：CXJD binder 族，无 `hσlast`）**：`Kh = extendAt` 族（`hKh`）上
`exists_extendAt_ceiling_CXJF2` 逐 `(x, w, B)` 应用 ⇒ 序列层 `hceil` 形；σ 可在 final slab、可等于 horizon。 -/
theorem hceil_of_firstExit_extendAt_P6JW {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb r : ℝ}
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    (hC2 : 0 ≤ C2') (hr : 0 < r)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (Kh : ℕ → ObservedHistory.{u})
    (hKh : Kh = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (t : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt t).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage t) t) (a₀ n + t) x)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (records : ∀ n (e : Fin (Kh n).eventCount), T₀ n ≤ (Kh n).time e.succ →
      GeometricCutoffRecord (Kh n) e (q n))
    (hOld : ∀ n (e : Fin (Kh n).eventCount), T₀ n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hm : ∀ n, 2 ≤ (q n).modelOrder)
    (hscale : ∀ n (e : Fin (Kh n).eventCount) (he : T₀ n ≤ (Kh n).time e.succ) b,
      (aSeed n : ℝ) < (Kh n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((records n e he).static b).neck.scale)
    (hfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ D T : ℝ, 0 < D → 0 < T → 2 * Ctime' * Qb * T ≤ 1 → ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) x ≤ Cball * R n) →
      ∀ uu : Icc (0 : ℝ) (Kh n).horizon, (uu : ℝ) = σ n - T / R n →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (Kh n).horizon) (_ : uu ≤ w) (hwσ : w ≤ σ n)
        (B : BackwardPointTrace (Kh n) ((Kh n).activeStage w) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) (Kh n).horizon) (hwv : w ≤ v) (hvσ : v ≤ σ n),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (B.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hwv)
            ((Kh n).activeStage_mono hvσ)) ≤ 2 * (Qb * R n) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hCX⟩ := exists_extendAt_ceiling_CXJF2.{u}
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  obtain ⟨c, hc, hnum⟩ := crossSlab_numerics_P6JW (C2' := C2') hC2 hQ1 hr
  intro D T hD hT hstep
  have hacc0 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε₀ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε₀)
  filter_upwards [hacc0, hwin T hT, hRlim.eventually_ge_atTop 1,
    hL.eventually_gt_atTop (2 * (D + 8 * T / c)),
    hL.eventually_ge_atTop (4 * (localPropagationRadius C2' / Real.sqrt (2 * Qb))),
    hL.eventually_ge_atTop (T + 1)] with n hεn hwn hRn hL1 hL2 hL3
  intro hball uu huu x hx w huw hwσ B v hwv hvσ
  have huw' : (uu : ℝ) ≤ w := huw
  obtain ⟨ℓ, K, hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hmarg⟩ :=
    hnum (R := R n) (L := L n) (D := D) (T := T) hRn (by linarith) (by linarith)
  have haS : (aSeed n : ℝ) ≤ w := by linarith
  have hTL : T ≤ L n ^ 2 := by nlinarith [sq_nonneg (L n - 1)]
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ w := by
    have h := (div_le_div_iff_of_pos_right (hR n)).2 hTL
    linarith
  have hdepth : (σ n : ℝ) - w ≤ T / R n := by linarith
  have hRa' : 1 ≤ R n * w := (hRa n).trans (mul_le_mul_of_nonneg_left haS (hR n).le)
  exact hCX hC2 (H n) (hend n) (G n) (hGi n) (hat n) (hts n) (haT n) (hsmall n) (hclock n)
    (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n) (L n) (hR n) (hgood n) hQb hstep haS hwσ
    haL hdepth hRa'
    (hball x hx) B hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀ n).trans haS) (records n) (hOld n)
    (hcan n) (hDm n) ((hacc n).trans hεn) (hm n)
    (fun e he b hlt => hscale n e he b (lt_of_le_of_lt haS hlt)) hx (hfin n) hmarg v hwv hvσ

end ObservedHistory

namespace RetainedCoreHistory

/-- **G1 接线（`_P6JW`，PROVISIONAL：CXJD binder 族）**：J10CORE `hsurvive_noJ10_P6JC` 以 G1″
`hceil_of_firstExit_extendAt_P6JW`（`Kh := Hs`、`hKh := hHs`、`σ := ts`、`y := ys`）为 `hceil`，
`Q_b := max (max Cball Cg) 1`；结论逐字。无 `hslabW` / `hstopX` / `hdistW`。 -/
theorem hsurvive_noJ10_firstExit_P6JW
    {Ctime Ctime' : ℝ≥0} {phi : ℝ → ℝ} {eps C1' C2' Cg Cball r : ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℕ → ℝ} (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    (hC2 : 0 ≤ C2') (hr : 0 < r)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (a₀X : ℕ → ℝ) (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
    (L : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ ts n - T / R n)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (hOldX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (haccX : ∀ n : ℕ, (qX n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hmX : ∀ n, 2 ≤ (qX n).modelOrder)
    (hscaleX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      (aSeed n : ℝ) < (Hs n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (max (max Cball Cg) 1 * R n)) <
        ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤) :
    ∀ A T : ℝ, 0 < A → 0 < T → 2 * (Ctime' : ℝ) * max (max Cball Cg) 1 * T ≤ 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Cball * R n) →
      (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n) :=
  hsurvive_noJ10_P6JC hphi recordsF hHI hend hGi hcan hδF hqcan hpar hscale hbirthA hθcap hpinch
    hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn hRlim (le_max_right _ _)
    (ObservedHistory.hceil_of_firstExit_extendAt_P6JW hC2 hr hend hGi hat hts Hs hHs Tn aSeed ts
      haT hsT has pT hsmall hclock seedTrace a₀X ha₀X hpinX ys R L hR hRlim hL hgood le_rfl hwin
      hRa qX T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hscaleX hfinX)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
