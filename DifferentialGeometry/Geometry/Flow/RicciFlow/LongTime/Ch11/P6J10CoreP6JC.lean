import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingTracedHI_P6LL

/-!
# 无 J10 的 crossing traced-region 包装（O-CH11-J10CORE G1，R-C11-16 D-4 第二步 T2，后缀 `_P6JC`）

`exists_eventually_isTracedRegion_extendAt_lateHI_P6LL`（`Local/CrossingTracedHI_P6LL.lean:74`）的孪生
`RetainedCoreHistory.crossingTracedHI_noJ10_P6JC`：删掉 J10 型坏点比较
`hqR : ∀ n, qcan n < R_n`（qcap < R），换成 `hR1 : ∀ᶠ n, 1 ≤ R_n`。原文里 `hqR` 只有两处真实用途：
* `:195` `hR0 : 0 < R_n`（`hq0.trans (hqR n)`）→ 改为 `1 ≤ R_n`（`hR1`）；
* `:226` B5 at-scale 前提 `1 ≤ Q·R`（`nlinarith [hqR n]`，经 `1 ≤ qcan < R`）→ 改由 `1 ≤ Q` 与 `1 ≤ R_n`
  付（`nlinarith [hRn1, hQ]`）。
B5（`exists_isTracedRegion_or_capWindowPoint_at_scale_win_P6LL`）**不动**：它的 `hdin`
（`hslab` / `hderG` 经 `derivativeBound_inputs_extendAt`，阈值 `2·qcan`）只进 cap age bound，并与 birth 比较
`2·qcan ≤ Cbirth·scale` 共用同一 `qcan` 参数——改成 q_sel 阈值会引入 D-3 禁止的 `q_sel ≤ C_birth·scale`，
所以 `hslab` / `hderG` 保留为 **cap 输入**（J9 型 qcap 数据，D-2：`hderG` 在 `2·qcan` 以上成立、不用坏点
`hQR`），不是 J10。结论逐字；证明除上面三处（filter 多取 `hR1`、`hR0`、`1 ≤ Q·R`，并删掉只为
`nlinarith [hqR n]` 服务的 `hq1`）外逐字。生成器 `build-logs/scratch/O-CH11-J10CORE/gen1.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- **G1（`_P6JC`，无 J10）**：`exists_eventually_isTracedRegion_extendAt_lateHI_P6LL` 去掉
`hqR : qcan n < R_n`，改吃 `hR1 : ∀ᶠ n, 1 ≤ R_n`；`hslab` / `hderG` 只作 B5 的 cap 输入（`2·qcan` 阈值）。
结论逐字。 -/
theorem crossingTracedHI_noJ10_P6JC
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
    (hR1 : ∀ᶠ n in atTop, 1 ≤ (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    {A T Q : ℝ} (hA : 0 < A) (hT : 0 < T) (hQ : 1 ≤ Q) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
      ∀ ŷ : (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageAt
          ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))).Carrier,
      HEq ŷ (y n) →
      ∀ uu : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon,
        (uu : ℝ) = t n - T / (G n).flow.scalar (t n) (y n) →
      (∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
            ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) ŷ
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (w : Icc (0 : ℝ)
            ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon)
          (_ : uu ≤ w) (hwt : w ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))
          (B : BackwardPointTrace ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage w)
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
              hwt) x)
          (v : Icc (0 : ℝ)
            ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon)
          (hwv : w ≤ v) (hvt : v ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)),
          metricScalarAt
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageMetric
                (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage v)
                v)
            (B.point
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage v)
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
                hwv)
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
                hvt)) ≤
            2 * (Q * (G n).flow.scalar (t n) (y n))) →
      ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.isTracedRegion
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) ŷ
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))
        (T / (G n).flow.scalar (t n) (y n)) (K₀ * (G n).flow.scalar (t n) (y n)) := by
  obtain ⟨c, hc, hB5⟩ := exists_isTracedRegion_or_capWindowPoint_at_scale_win_P6LL.{u}
  have hφ0 := hphi.pos 0
  have hφ1 := hphi.pos 1
  have hTQ : 0 < 8 * T * Q := by positivity
  set θ₁ : ℝ := max (1 / 4) (1 - c / (8 * T * Q)) with hθ₁def
  have hθ₁ : θ₁ < 1 := max_lt (by norm_num) (by have := div_pos hc hTQ; linarith)
  have hΘ0 : 0 < (θ₁ + 1) / 2 := by
    have := le_max_left (1 / 4 : ℝ) (1 - c / (8 * T * Q))
    linarith
  obtain ⟨Cbirth, hCb, hB5⟩ := hB5 ((θ₁ + 1) / 2) hΘ0 (by linarith) (2 * Ctime)
  set Dcap : ℝ := 2 * StandardCap.transitionEnd + Real.sqrt (8 * Q) *
    Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A + 1 with hDcap
  have hDs : StandardCap.transitionEnd < Dcap := by
    have := StandardCap.transitionEnd_pos
    have : 0 ≤ Real.sqrt (8 * Q) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A := by positivity
    linarith
  obtain ⟨Rrad, -, m₀, -, ζ₀, δ₀, hζ₀, -, hδ₀, hB5⟩ := hB5 Dcap hDs
  have hev := persistence_inputs_eventually_lateHI_P6LL hqcan hpar hscale hbirthA
  have hDev : ∀ᶠ n : ℕ in atTop, Dcap ≤ D n := by
    obtain ⟨N, hN⟩ := exists_nat_ge Dcap
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(hpar n).2.1]
  have hθev : ∀ᶠ n : ℕ in atTop, θ₁ ≤ θcap n := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - θ₁))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 0 < 1 - θ₁ := by linarith
    have h2 : 1 / ((n : ℝ) + 2) ≤ 1 - θ₁ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at hN
      nlinarith
    linarith [hθcap n]
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Q, by positivity, ?_⟩
  filter_upwards [hev Rrad ζ₀ δ₀ (Cbirth / 2) m₀ hζ₀ hδ₀ (half_pos hCb), hDev, hθev, hT₀ T, hR1]
    with n hn hDn hθn hTn hRn1
  obtain ⟨hδn, hRn, hmn, hζn, hbirth, hq0⟩ := hn
  intro ŷ hŷ uu huu hscal
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := lt_of_lt_of_le one_pos hRn1
  have hlast : ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) =
        Fin.last (H n).eventCount :=
    (H n).activeStage_extendHorizon_eq_last ((hend n) ▸ (hat n).le)
      ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n)
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) (hat n).le
  have hut : uu ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n) := by
    change (uu : ℝ) ≤ t n
    rw [huu]
    linarith [div_pos hT hR0]
  have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    (by linarith) (hslab n) (hderG n)
  rcases hB5 ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n))
      (fun i hi => (records n i hi).extendHorizon (t n) ((hend n) ▸ (hat n).le)
        ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n))
      (fun i hi b => hcan n i hi b) hRn hmn hζn
      (fun i => (recordsF n i).extendHorizon (t n) ((hend n) ▸ (hat n).le)
        ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n))
      (δb n) (fun i hi => hδF n i hi) hδn (2 * qcan n) (a₀ n) (by linarith)
      (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (fun i hi b => le_of_le_of_eq (show 2 * qcan n ≤
        Cbirth * ((records n i hi).static b).neck.scale by linarith [(hbirth i hi b).1]) rfl)
      (fun i hi b => (hbirth i hi b).2) phi hphi
      (hpinch n).1 uu
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) hut (by rw [huu]; exact hTn)
      (fun _ => extendHorizon_finalSlab_phiAlmostNonnegative_window_P6LL (H := H n)
        (hHT := (hend n) ▸ (hat n).le) (hpinch n).2)
      hdin.1 hdin.2.1 hdin.2.2 ŷ
      ((G n).flow.scalar (t n) (y n)) A T Q Dcap θ₁ hR0 hA hT
      (by nlinarith [hRn1, hQ]) huu
      (le_max_left _ _) (le_max_right _ _) (by linarith) le_rfl hscal
      (by rw [hDcap]; linarith) with htr | hcw
  · rw [mul_assoc]
    exact htr
  · obtain ⟨j, hj, hl, B, b, x, hx, hxn, hage⟩ := lateCWP_of_extendHorizon_P6LL (H n) (records n)
      ((hend n) ▸ (hat n).le) ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n) hlast hŷ hcw
    exact absurd ⟨j, hj, hl, B, b, x, hx, by linarith, hage.trans (mul_le_mul_of_nonneg_right hθn
      (inv_nonneg.mpr ((records n j hj).static b).neck.scale_pos.le))⟩ (hnot n)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
