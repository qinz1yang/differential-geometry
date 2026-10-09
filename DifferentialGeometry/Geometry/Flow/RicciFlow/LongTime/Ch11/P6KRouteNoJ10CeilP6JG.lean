import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteNoJ10P6JG

/-!
# J10GEN G1b（方案 c）：`hceilQ` 降到 J10WIRE 原 binder 族（O-CH11-J10GEN，后缀 `_P6JG`）

G1 `kRouteHICond_noJ10_P6JG` 的 `hceilQ : ∀ Q ≥ 2, hceil(Q)` 不能由 J10WIRE G1″
`hceil_of_firstExit_extendAt_P6JW` 逐 `Q` 直接付：后者的 `hscale` 是 `∀ n`（含 `Q_b`），对所有 `Q` 同时成立
等于 neck scale 无界。本文件：
* `hceil_of_firstExit_extendAt_ev_P6JG`（PROVISIONAL，CXJD / CXJF2 binder 族）：G1″ 的孪生，`hscale` 放宽为
  `∀ᶠ n`（证明体逐字，`hscale` 并入同一个 `filter_upwards`）；
* `hscale_ev_of_sep_P6JG`（PROVED）：scale separation
  `hsepX : ∀ M, ∀ᶠ n, 窗口 event 的 neck scale > M·R_n` + `R → ∞` ⇒ 每个 `Q_b ≥ 0` 的
  eventual `hscale`（取 `M := 2·(3/r²) + 4·Q_b`）；
* `hceilQ_of_firstExit_sep_P6JG`（PROVISIONAL）：二者合成 G1 的 `hceilQ` 槽（`Cball := Q`、
  `Q_b := max (max Q Cg) 1`）；
* **`kRouteHICond_noJ10_firstExit_P6JG`**
  （PROVISIONAL：J10WIRE (B) 族 + `hsepX` + `hdistC` + `hextend`）：G1 以上式付 `hceilQ`，结论逐字。
  `hsepX` 的 producer 候选 = O-CH11-HSCALE `WindowNeckScaleBudget_P6HS`
  （`scale ≥ c/(δ⁴ρ²)`，`δ → 0`）。
由 build-logs/scratch/O-CH11-J10GEN/gen1b.py 从 tracked 文本生成。
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

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **G1b-1（`_P6JG`，PROVISIONAL：CXJD / CXJF2 binder 族）**：`hceil_of_firstExit_extendAt_P6JW` 的孪生，
`hscale` 只要求 `∀ᶠ n`（证明体逐字，`hscale` 并入 `filter_upwards`）。 -/
theorem hceil_of_firstExit_extendAt_ev_P6JG {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb r : ℝ}
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
    (hscale : ∀ᶠ n in atTop, ∀ (e : Fin (Kh n).eventCount)
      (he : T₀ n ≤ (Kh n).time e.succ) b,
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
    hL.eventually_ge_atTop (T + 1), hscale] with n hεn hwn hRn hL1 hL2 hL3 hsc
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
    (fun e he b hlt => hsc e he b (lt_of_le_of_lt haS hlt)) hx (hfin n) hmarg v hwv hvσ

/-- 数值核（`_P6JG`，PROVED）：`1 ≤ x`、`0 ≤ Q_b` ⇒ `2·max(3/r², 2Q_b x) ≤ (2·(3/r²) + 4Q_b)·x`。 -/
theorem two_max_le_sep_P6JG {r Qb x : ℝ} (hr : 0 < r) (hQb : 0 ≤ Qb) (hx : 1 ≤ x) :
    2 * max (3 / r ^ 2) (2 * (Qb * x)) ≤ (2 * (3 / r ^ 2) + 4 * Qb) * x := by
  have ha : 0 < 3 / r ^ 2 := by positivity
  have h1 : 0 ≤ 3 / r ^ 2 * (x - 1) := mul_nonneg ha.le (by linarith)
  have h2 : 0 ≤ Qb * x := mul_nonneg hQb (by linarith)
  rcases le_total (3 / r ^ 2) (2 * (Qb * x)) with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

/-- **G1b-2（`_P6JG`，PROVED）**：scale separation `hsepX`（`∀ M, ∀ᶠ n`）+ `R → ∞` ⇒ 给定 `Q_b ≥ 0` 的
eventual `hscale`（CXJD 形 `2·max(3/r², 2Q_b R) < scale`）。 -/
theorem hscale_ev_of_sep_P6JG {r Qb : ℝ} (hr : 0 < r) (hQb : 0 ≤ Qb)
    (Hs : ℕ → ObservedHistory.{u}) (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (R : ℕ → ℝ)
    (hRlim : Tendsto R atTop atTop) (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (aSeed n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      (aSeed n : ℝ) < (Hs n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((recordsX n e he).static b).neck.scale := by
  filter_upwards [hsepX (2 * (3 / r ^ 2) + 4 * Qb), hRlim.eventually_ge_atTop 1] with n hn hR1
  intro e he b hlt
  exact (two_max_le_sep_P6JG hr hQb hR1).trans_lt (hn e he b hlt)

/-- **G1b-3（`_P6JG`，PROVISIONAL：CXJD / CXJF2 binder 族 + `hsepX`）**：G1 的 `hceilQ` 槽
（`Cball := Q`、`Q_b := max (max Q Cg) 1`）⇐ G1b-1 + G1b-2。 -/
theorem hceilQ_of_firstExit_sep_P6JG {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg r : ℝ}
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
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Kh n).eventCount)
      (he : T₀ n ≤ (Kh n).time e.succ) b, (aSeed n : ℝ) < (Kh n).time e.succ →
        M * R n < ((records n e he).static b).neck.scale)
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
  have hQb0 : (0 : ℝ) ≤ max (max Q Cg) 1 := le_trans zero_le_one (le_max_right _ _)
  exact hceil_of_firstExit_extendAt_ev_P6JG (Cball := Q) hC2 hr hend hGi hat hts Kh hKh Tn aSeed σ
    haT hsT has pT hsmall hclock seedTrace a₀ ha₀ hpin y R L hR hRlim hL hgood le_rfl hwin hRa q T₀
    hT₀ records hOld hcan hDm hacc hm
    (hscale_ev_of_sep_P6JG hr hQb0 Kh aSeed R hRlim q T₀ records hsepX) hfin

/-- **G1b（`_P6JG`，PROVISIONAL：J10WIRE (B) 族 + `hsepX` + `hdistC` + `hextend`）**：G1
`kRouteHICond_noJ10_P6JG` 以 `hceilQ_of_firstExit_sep_P6JG` 付 `hceilQ`；结论逐字。binder 相对 G1：删
`hceilQ`，加 CXJD / CXJF2 族（`hC2` `hr` `hsmall` `hclock` `a₀X` `hpinX` `hRa` records-X 族 `hfinX`）与
scale separation `hsepX`（取代 J10WIRE 的 `∀ n` 形 `hscaleX`）。 -/
theorem kRouteHICond_noJ10_firstExit_P6JG
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
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n)
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
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
        (ts n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvs) x,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))
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
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (aSeed n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
          ((Hs n).activeStage_mono (hsT n))) (ys n) ≠ ⊤)
    {Cext : ℝ≥0}
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
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
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cext : ℝ) + 1) * (M + 1)))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T :=
  kRouteHICond_noJ10_P6JG hphi recordsF hHI hend hGi hcan hδF hqcan hpar hscale hbirthA hθcap hpinch
    hslab hat hts hderG hnot hT₀ hRt hanchor0 Hs ts ys R hHs hts' hys hRn hr₀ hw hseed hκ ρnc hradii
    hkappa hε hεX hεN hqs hwitC hbcadC hR hRlim Tn aSeed haT hsT has pT seedTrace L hL hgood hwin
    hdistC
    (hceilQ_of_firstExit_sep_P6JG hC2 hr hend hGi hat hts Hs hHs Tn aSeed ts haT hsT has pT hsmall
      hclock seedTrace a₀X ha₀X hpinX ys R L hR hRlim hL hgood hwin hRa qX T₀X hT₀X recordsX hOldX
      hcanX hDmX haccX hmX hsepX hfinX) hextend

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
