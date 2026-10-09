import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvJ10SlotsDJ

/-!
# HSEPX G1：GAP[hsepX] 的 T/R 窗形孪生（`_HSX`）

G0（state-O-CH11-HSEPX）：J10GEN `hceil_of_firstExit_extendAt_ev_P6JG` 与 CXJP
`crossingDepthHI_extend_noJ10_CXJP` 对 scale separation 的唯一用法是 `hsc e he b (lt_of_le_of_lt haS hlt)`，
`hlt : w < time e.succ` 且 `w ≥ σ − T/R`（T 在 `∀ᶠ n` 前固定）⇒ 只需 `(σ − T/R, ·)` 窗内事件。
新前提 `hsepT : ∀ T > 0, ∀ C ≥ 0, ∀ᶠ n, ∀ e he b, ts − T/R < time e.succ → 2·max(3/r², C·R) < scale`
（= DrvResE_DW 合取 1 的形，E 帧）。本文件：
* `hceil_of_firstExit_extendAt_sepT_HSX` / `hceilQ_of_firstExit_sepT_HSX`（J10GEN G1b-1 / G1b-3 孪生）；
* `crossingDepthHI_extend_noJ10_sepT_HSX`（CXJP 孪生）；
* `drvSlots_K_of_J10_sepT_HSX`（DRV-J10F `drvSlots_K_of_J10_DJ` 孪生：消费端在新形下闭合）；
* `hsepT_of_hsepX_HSX`（PROVED：旧 `hsepX` + `hwin` ⇒ `hsepT`，新前提更弱）。
无 `hqR`；无新顶层 binder；原文件不动。由 build-logs/scratch/HSEPX/gen/g1.py 从 tracked 文本生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **G1（`_HSX`）**：J10GEN `hceil_of_firstExit_extendAt_ev_P6JG` 的 T/R 窗形孪生：`hscale`（aSeed 窗）
换为 `hsepT`（`∀ T C`，`σ − T/R` 窗，DrvResE 合取 1 形）；证明体逐字，只把 `aSeed ≤ w` 接口换成
`σ − T/R ≤ w`（`uu = σ − T/R ≤ w`）。 -/
theorem hceil_of_firstExit_extendAt_sepT_HSX {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb r : ℝ}
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
    (hsepT : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop, ∀ (e : Fin (Kh n).eventCount)
      (he : T₀ n ≤ (Kh n).time e.succ) b, (σ n : ℝ) - T / R n < (Kh n).time e.succ →
        2 * max (3 / r ^ 2) (C * R n) < ((records n e he).static b).neck.scale)
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
    hL.eventually_ge_atTop (T + 1),
    hsepT T hT (2 * Qb) (by linarith)] with n hεn hwn hRn hL1 hL2 hL3 hsc
  intro hball uu huu x hx w huw hwσ B v hwv hvσ
  have huw' : (uu : ℝ) ≤ w := huw
  have hTw : (σ n : ℝ) - T / R n ≤ w := huu ▸ huw'
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
    (fun e he b hlt => (mul_assoc (2 : ℝ) Qb (R n)) ▸
      hsc e he b (lt_of_le_of_lt hTw hlt))
    hx (hfin n) hmarg v hwv hvσ

/-- **G1（`_HSX`）**：`hceilQ_of_firstExit_sep_P6JG` 的 T/R 窗形孪生（`hsepX` ⇒ `hsepT`）；结论逐字。 -/
theorem hceilQ_of_firstExit_sepT_HSX {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg r : ℝ}
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
    (hsepT : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop, ∀ (e : Fin (Kh n).eventCount)
      (he : T₀ n ≤ (Kh n).time e.succ) b, (σ n : ℝ) - T / R n < (Kh n).time e.succ →
        2 * max (3 / r ^ 2) (C * R n) < ((records n e he).static b).neck.scale)
    (hfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ Q : ℝ, 2 ≤ Q → ∀ A T : ℝ, 0 < A → 0 < T →
      2 * Ctime' * max (max Q Cg) 1 * T ≤ 1 → ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) x ≤ Q * R n) →
      ∀ uu : Icc (0 : ℝ) (Kh n).horizon, (uu : ℝ) = σ n - T / R n →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (Kh n).horizon) (_ : uu ≤ w) (hwσ : w ≤ σ n)
        (B : BackwardPointTrace (Kh n) ((Kh n).activeStage w) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hwσ) x)
        (v : Icc (0 : ℝ) (Kh n).horizon) (hwv : w ≤ v) (hvσ : v ≤ σ n),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (B.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hwv)
            ((Kh n).activeStage_mono hvσ)) ≤ 2 * (max (max Q Cg) 1 * R n) := by
  intro Q hQ
  exact hceil_of_firstExit_extendAt_sepT_HSX (Cball := Q) hC2 hr hend hGi hat hts Kh hKh Tn aSeed σ
    haT hsT has pT hsmall hclock seedTrace a₀ ha₀ hpin y R L hR hRlim hL hgood le_rfl hwin hRa q T₀
    hT₀ records hOld hcan hDm hacc hm hsepT hfin

/-- 数值（`_HSX`，PROVED）：`0 ≤ a`、`0 ≤ C`、`1 ≤ x` ⇒ `2·max(a, C x) ≤ (2a + 2C)·x`。 -/
theorem two_max_le_HSX {a C x : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hx : 1 ≤ x) :
    2 * max a (C * x) ≤ (2 * a + 2 * C) * x := by
  rcases le_total a (C * x) with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

/-- **G1（`_HSX`，PROVED）旧 ⇒ 新**：aSeed 窗 `hsepX`（`∀ M`）+ `hwin` + `R → ∞` ⇒ T/R 窗 `hsepT`。
即新前提严格更弱（窗口 `(ts − T/R, ·) ⊆ (aSeed, ·)` eventually）。 -/
theorem hsepT_of_hsepX_HSX {r : ℝ} (hr : 0 < r)
    (Hs : ℕ → ObservedHistory.{u}) (ts aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (R : ℕ → ℝ)
    (hRlim : Tendsto R atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ ts n - T / R n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (aSeed n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (ts n : ℝ) - T / R n < (Hs n).time e.succ →
        2 * max (3 / r ^ 2) (C * R n) < ((recordsX n e he).static b).neck.scale := by
  intro T hT C hC
  filter_upwards [hsepX (2 * (3 / r ^ 2) + 2 * C), hwin T hT, hRlim.eventually_ge_atTop 1]
    with n h1 h2 h3
  intro e he b hlt
  have ha : (0 : ℝ) ≤ 3 / r ^ 2 := by positivity
  exact (two_max_le_HSX ha hC h3).trans_lt (h1 e he b (lt_of_le_of_lt h2 hlt))

end ObservedHistory

open ObservedHistory in
/-- **G1（`_HSX`）**：CXJP `crossingDepthHI_extend_noJ10_CXJP` 的 T/R 窗形孪生（`hsepX` ⇒ `hsepT`）；
结论逐字；证明体逐字，只改 `hscale'` 的来源（`t − Tg/R ≤ w` 窗）。 -/
theorem crossingDepthHI_extend_noJ10_sepT_HSX
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
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
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    {eps C1' C2' Cg : ℝ} {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
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
    {r : ℝ} (hC2 : 0 ≤ C2') (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀X : ℕ → ℝ) (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
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
    (hsepT : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (ts n : ℝ) - T / R n < (Hs n).time e.succ →
        2 * max (3 / r ^ 2) (C * R n) < ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤) :
    ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
    (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
    (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
    ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
        ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
        (A / Real.sqrt (R (σ i))),
    ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
      (w : ℝ) = ts (σ i) - T' / R (σ i) →
    ∀ (hwt : w ≤ ts (σ i))
      (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
        ((Hs (σ i)).activeStage (ts (σ i)))
        ((Hs (σ i)).activeStage_mono hwt) x),
      metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
        (Bt.point ((Hs (σ i)).activeStage w) le_rfl
          ((Hs (σ i)).activeStage_mono hwt)) ≤
        M * R (σ i)) →
    DepthExtendable Hs ts ys R σ
      (Tstar + 1 / (32 * (((Ctime' * (max Cg 1).toNNReal : ℝ≥0) : ℝ) + 1) * (M + 1)))  := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  have hRfun : R = fun n => (G n).flow.scalar (t n) (y n) := funext hRn
  subst hRfun
  intro φ hφ Tstar M hT hM hext hanc A hA
  -- 常数（只含 selected 侧 `Ctime′, Cg`；不比较 `Ctime` 与 `Ctime′`）
  have hCe : (((Ctime' * (max Cg 1).toNNReal : ℝ≥0) : ℝ)) = (Ctime' : ℝ) * max Cg 1 := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ ((zero_le_one).trans (le_max_right _ _))]
  rw [hCe]
  have hC0 : (0 : ℝ) ≤ Ctime' := Ctime'.coe_nonneg
  have hm1 : (1 : ℝ) ≤ max Cg 1 := le_max_right _ _
  set Ce : ℝ := (Ctime' : ℝ) * max Cg 1 with hCedef
  have hCe0 : 0 ≤ Ce := mul_nonneg hC0 (by linarith)
  set Tg : ℝ := Tstar + 1 / (32 * (Ce + 1) * (M + 1)) with hTg
  set Δ : ℝ := 1 / (8 * (Ce + 1) * (M + 1)) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  set T' : ℝ := max (Tstar - Δ / 2) (Tstar / 2) with hT'
  have hT'0 : 0 < T' := lt_max_of_lt_right (half_pos hT)
  have hT'lt : T' < Tstar := max_lt (by linarith) (by linarith)
  have hTgΔ : Tg = Tstar + Δ / 4 := by
    rw [hTg, hΔ]
    field_simp
    ring
  have hgap : Tg - T' ≤ 3 * Δ / 4 := by
    have := le_max_left (Tstar - Δ / 2) (Tstar / 2)
    linarith
  have hgap0 : 0 ≤ Tg - T' := by
    have : T' < Tstar := hT'lt
    linarith
  have hTg0 : 0 < Tg := by positivity
  set Qa : ℝ := max (max M Cg) 1 with hQadef
  have hQa1 : 1 ≤ Qa := le_max_right _ _
  have hQaCe : (Ctime' : ℝ) * Qa ≤ (Ce + 1) * (M + 1) := by
    have h1 : Qa ≤ max Cg 1 * (M + 1) := by
      refine max_le (max_le ?_ ?_) ?_ <;> nlinarith [le_max_left Cg 1]
    have h2 : (Ctime' : ℝ) * Qa ≤ Ce * (M + 1) := by
      rw [hCedef, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hC0
    nlinarith
  have hstep : 2 * (Ctime' : ℝ) * Qa * (Tg - T') ≤ 1 := by
    have hpos : 0 < (Ce + 1) * (M + 1) := by positivity
    have e1 : 2 * (Ctime' : ℝ) * Qa * (Tg - T') ≤ 2 * ((Ce + 1) * (M + 1)) * (3 * Δ / 4) := by
      have := mul_le_mul hQaCe hgap hgap0 hpos.le
      nlinarith
    have e2 : 2 * ((Ce + 1) * (M + 1)) * (3 * Δ / 4) = 3 / 16 := by
      rw [hΔ]
      field_simp
      ring
    linarith
  obtain ⟨K₁, hK₁, hev1⟩ := hext T' hT'0 hT'lt A hA
  have hev2 := hanc T' hT'0 hT'lt A hA
  set Qb : ℝ := max Qa (9 * K₁) with hQbdef
  have hQaQb : Qa ≤ Qb := le_max_left _ _
  have hQb1 : 1 ≤ Qb := hQa1.trans hQaQb
  have hK₁9 : 9 * K₁ ≤ 2 * Qb := by
    have := le_max_right Qa (9 * K₁)
    linarith
  have hCgQb : max Cg 1 ≤ Qb :=
    (max_le ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)).trans hQaQb
  obtain ⟨K₀, hK₀, hev3⟩ := RetainedCoreHistory.crossingTracedHI_noJ10_P6JC hphi recordsF hHI
    hend hGi hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hat hts hderG
    (eventually_one_le_of_tendsto_P6JC hRlim (fun _ => rfl)) hnot hT₀
    (A := A) (T := Tg) (Q := Qb) hA hTg0 hQb1
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  obtain ⟨c, hc, hnum⟩ := crossSlab_numerics_P6JW (C2' := C2') hC2 hQb1 hr
  have hεm : 0 < min ε₀ (1 / 2) := lt_min hε₀ (by norm_num)
  have hacc0 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ min ε₀ (1 / 2) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hεm)
  have hevn : ∀ᶠ n : ℕ in atTop, (1 / ((n : ℝ) + 1) ≤ min ε₀ (1 / 2) ∧
      (aSeed n : ℝ) ≤ t n - Tg / (G n).flow.scalar (t n) (y n)) ∧
      (1 ≤ (G n).flow.scalar (t n) (y n) ∧ 2 * (A + 8 * Tg / c) < L n) ∧
      (4 * (localPropagationRadius C2' / Real.sqrt (2 * Qb)) ≤ L n ∧ Tg + 1 ≤ L n) ∧
      ((∀ (e : Fin (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory).eventCount)
        (he : T₀X n ≤ ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.time
          e.succ) b,
        (t n : ℝ) - Tg / (G n).flow.scalar (t n) (y n) <
          ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.time e.succ →
        2 * max (3 / r ^ 2) (2 * Qb * (G n).flow.scalar (t n) (y n)) <
          ((recordsX n e he).static b).neck.scale) ∧
      Tg < (G n).flow.scalar (t n) (y n) * t n) := by
    filter_upwards [hacc0, hwin Tg hTg0, hRlim.eventually_ge_atTop 1,
      hL.eventually_gt_atTop (2 * (A + 8 * Tg / c)),
      hL.eventually_ge_atTop (4 * (localPropagationRadius C2' / Real.sqrt (2 * Qb))),
      hL.eventually_ge_atTop (Tg + 1), hsepT Tg hTg0 (2 * Qb) (by linarith),
      hRt.eventually_gt_atTop Tg] with n h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev1, hev2, hφ.tendsto_atTop.eventually hev3,
    hφ.tendsto_atTop.eventually hevn] with i h1 h2 h3 h4
  generalize φ i = n at h1 h2 h3 h4 ⊢
  obtain ⟨⟨hεn, hwn⟩, ⟨hRn1, hL1⟩, ⟨hL2, hL3⟩, hsc, hRtn⟩ := h4
  set KH := (H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n) with hKH
  set Rn : ℝ := (G n).flow.scalar (t n) (y n) with hRndef
  have hR' : 0 < Rn := by linarith only [hRn1]
  have hut0 : 0 ≤ t n - Tg / Rn := by
    rw [sub_nonneg, div_le_iff₀ hR']
    linarith
  let uu : Icc (0 : ℝ) KH.toHistory.horizon :=
    ⟨t n - Tg / Rn, hut0, show t n - Tg / Rn ≤ t n from sub_le_self _ (div_pos hTg0 hR').le⟩
  refine h3 (ys n) (hys n) uu rfl ?_
  intro x hx w huw hwt B v hwv hvt
  obtain ⟨-, -, a₁, ha₁t, ha₁, htr⟩ := h1
  obtain ⟨A₁, hA₁⟩ := htr x hx
  have huw' : t n - Tg / Rn ≤ (w : ℝ) := huw
  by_cases hwa : a₁ ≤ w
  · exact scalar_le_of_isRmBounded_CXJP KH.toHistory hwt ha₁t hR' hK₁9 hK₁ B A₁ hA₁ v hwv
      (hwa.trans hwv) hvt
  have hwa' : w ≤ a₁ := (lt_of_not_ge hwa).le
  -- 数值、窗口
  obtain ⟨ℓ, K, hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hmarg⟩ :=
    hnum (R := Rn) (L := L n) (D := A) (T := Tg) hRn1 (by linarith only [hL1])
      (by linarith only [hL2])
  have hL0 : 0 ≤ L n := by linarith only [hL3, hTg0]
  have hL1' : 1 ≤ L n := by linarith only [hL3, hTg0]
  have hTL : Tg ≤ L n ^ 2 :=
    calc Tg ≤ L n := by linarith only [hL3]
      _ = L n * 1 := by ring
      _ ≤ L n * L n := mul_le_mul_of_nonneg_left hL1' hL0
      _ = L n ^ 2 := by ring
  have haS : aSeed n ≤ w := show (aSeed n : ℝ) ≤ w by linarith only [hwn, huw']
  have haL : (t n : ℝ) - L n ^ 2 / Rn ≤ w := by
    have h := (div_le_div_iff_of_pos_right hR').2 hTL
    linarith only [h, huw']
  have hdepth : (t n : ℝ) - w ≤ Tg / Rn := by linarith only [huw']
  have hRa' : 1 ≤ Rn * w := (hRa n).trans (mul_le_mul_of_nonneg_left haS hR'.le)
  have ha₁' : (a₁ : ℝ) = t n - T' / Rn := ha₁
  have hdepthx : (a₁ : ℝ) - w ≤ (Tg - T') / Rn := by
    rw [ha₁', sub_div]
    linarith only [huw']
  -- anchor（本步独立）
  have hancB := h2 x hx a₁ ha₁ ha₁t (B.restrictFirst (KH.toHistory.activeStage_mono hwa')
    (KH.toHistory.activeStage_mono ha₁t))
  -- `hscalC`（traced region + anchor ceiling）
  have hscalC := hscalC_of_traced_anchor_CXJP (Qb := Qb) KH.toHistory (haT n) (seedTrace n)
    (hsT n) (has n) (ys n) (L n) hR' hL0 (hgood n) hstep hQaQb hK₁9 hK₁ haS hwa' ha₁t haL
    hdepthx B A₁ hA₁ hancB
  -- crossing 条件保护
  have hnc : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀X n ≤ KH.toHistory.time e.succ)
      (w' : (KH.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (KH.toHistory.event e).outputMetric w' <
        ((recordsX n e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (KH.toHistory.event e).RetainedBoundaryIndex)
        (x' : standardCapWindow (qX n).modelRadius),
        w' = ((recordsX n e he).static b).window x' ∧ ‖x'.val‖ < (qX n).modelRadius := by
    intro e he w' hw'
    have h := hnc0 (recordsX n e he) ((haccX n).trans (hεn.trans (min_le_left _ _))) (hmX n)
      (hcanX n e he) (Dcap := (qX n).modelRadius - 1) (le_of_eq (sub_add_cancel _ _)) w' hw'
    simpa only [sub_add_cancel] using h
  have hscale' : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀X n ≤ KH.toHistory.time e.succ) b,
      (w : ℝ) < KH.toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * Rn)) < ((recordsX n e he).static b).neck.scale := by
    intro e he b hlt
    exact (mul_assoc (2 : ℝ) Qb Rn) ▸ hsc e he b (lt_of_le_of_lt huw' hlt)
  have hprotC := hprotC_scalC_CXJP KH (haT n) (hsmall n) (hclock n) (seedTrace n) (hsT n)
    (has n) (ys n) (L n) haS hwt B hscalC (recordsX n) (hDmX n) hnc hscale'
  have hgV := hgoodV_scalC_CXJP hC2 KH (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀X n)
    (hpinX n) (hsT n) (has n) (ys n) (L n) hR' (hgood n) hCgQb haS hwt
    (hUSCtop_extendAt_CXJF2 (H n) (hend n) (G n) (hGi n) (hat n) (hts n) _)
    haL hdepth hRa' B hscalC hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀X n).trans haS) (recordsX n)
    (hOldX n) (hcanX n) ((haccX n).trans (hεn.trans (min_le_right _ _))) (hDmX n) hprotC hx
    (hfinX n) hmarg
  exact hscalC v hwv hvt fun v' hav' hv'σ _ => hgV v' hav' hv'σ

namespace ObservedHistory

/-- **G1（`_HSX`，PROVISIONAL[CXJP binder 块，`hsepX` 换 `hsepT`]）**：DRV-J10F `drvSlots_K_of_J10_DJ` 的
孪生；结论逐字（DrvResE_DW 两槽）；证明体逐字，三处 producer 换 `_HSX` 孪生。 -/
theorem drvSlots_K_of_J10_sepT_HSX
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
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
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    {eps C1' C2' Cg : ℝ} {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (pT : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
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
    {r : ℝ} (hC2 : 0 ≤ C2') (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀X : ℕ → ℝ) (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
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
    (hsepT : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (ts n : ℝ) - T / R n < (Hs n).time e.succ →
        2 * max (3 / r ^ 2) (C * R n) < ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤)
    (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount) (tK : ℕ → ℝ)
    (hjt : ∀ n, (K n).time (j n).castSucc < tK n) (htj : ∀ n, tK n < (K n).time (j n).succ)
    (hHsK : ∀ n, Hs n = ((K n).eventPrefix (j n) (tK n) (hjt n) (htj n)).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hysK : ∀ n, HEq (ys n) (yK n)) :
    ∃ (Cst : ℝ≥0),
    (∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric
            ((K n).toHistory.activeStage (σ n)) (σ n)) (yK n) (A / Real.sqrt (R n)),
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            z ≤ Q * R n) →
        (K n).toHistory.isTracedRegion (σ n) (yK n) (A / Real.sqrt (R n)) (T / R n) (Kc * R n)) ∧
    (∀ σs : ℕ → ℕ, StrictMono σs → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable (fun n => (K n).toHistory) σ yK R σs T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σs i)).toHistory.stageMetric
          ((K (σs i)).toHistory.activeStage (σ (σs i))) (σ (σs i))) (yK (σs i))
          (A / Real.sqrt (R (σs i))),
      ∀ (w : Icc (0 : ℝ) (K (σs i)).toHistory.horizon),
        (w : ℝ) = σ (σs i) - T' / R (σs i) →
      ∀ (hwt : w ≤ σ (σs i))
        (Bt : BackwardPointTrace (K (σs i)).toHistory ((K (σs i)).toHistory.activeStage w)
          ((K (σs i)).toHistory.activeStage (σ (σs i)))
          ((K (σs i)).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σs i)).toHistory.stageMetric ((K (σs i)).toHistory.activeStage w) w)
          (Bt.point ((K (σs i)).toHistory.activeStage w) le_rfl
            ((K (σs i)).toHistory.activeStage_mono hwt)) ≤
          M * R (σs i)) →
      DepthExtendable (fun n => (K n).toHistory) σ yK R σs
        (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1)))) := by
  have hceilQ := hceilQ_of_firstExit_sepT_HSX (eps := eps) (C1' := C1') (C2' := C2')
    (Ctime' := Ctime') (Cg := Cg) hC2 hr hend hGi hat hts Hs hHs Tn aSeed ts haT hsT has pT
    hsmall hclock seedTrace a₀X ha₀X hpinX ys R L hR hRlim hL hgood hwin hRa qX T₀X hT₀X recordsX
    hOldX hcanX hDmX haccX hmX hsepT hfinX
  have hextE := crossingDepthHI_extend_noJ10_sepT_HSX hphi recordsF hHI hend hGi hcan hδF hqcan hpar
    hscale hbirthA hθcap hpinch hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn hR
    hRlim Tn aSeed haT hsT has pT seedTrace L hL hgood hwin hC2 hr hsmall hclock a₀X ha₀X hpinX
    hRa qX T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepT hfinX
  refine ⟨Ctime' * Real.toNNReal (max Cg 1) + Ctime' * Real.toNNReal (max Cg 1),
    hsurvive_K_of_eventPrefix_DJ hHsK hσ hysK ?_,
    hextend_K_of_eventPrefix_DJ hHsK hσ hysK (hextend_lower_P6JG Hs ts ys R hR hextE)⟩
  intro A T Q hA hT hQ hstep
  exact RetainedCoreHistory.hsurvive_noJ10_P6JC (Cball := Q) hphi recordsF hHI hend hGi hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hat hts hderG hnot hT₀ hRt Hs ts ys R hHs hts' hys
    hRn hRlim (le_max_right _ _) (hceilQ Q hQ) A T hA hT (sideCond_noJ10_P6JG hQ hT hstep)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
