import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayGuardedKernelP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinchGateLateP6HP2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WBAdaptStarP6WA2

/-!
# FOOT3 terminal kernel / gate 的 guarded 孪生（HSTAY-A4 G2，后缀 `_P6HS`；D-21-8 第三路线）

FOOT3 gate `hlocBCD_of_localSupplies_gate_late_P6HP2`（`P6HpinchGateLateP6HP2.lean` l.223）
在 l.614 / 617 以 `T = 3·Bw`、`r = max(2·Rad, 1)` 实例化 `hderivL` / `hgradL`
（`(Rad, Bw)` = P6F3 kernel 的 ∃ 常数，P6WB 反证 `Bw n = n + 1 + θ`）
⇒ 需要整窗 `[t − 3Bw/R_k, t)` 上、无比值上界的点上的导数 = `hstaySlot`（BLOCKED）。
本文件把 kernel 换成 G1 的 guarded kernel（⇐ `shortSLT_guarded_C11KX`），重验原调用：
* **`RetainedCoreHistory.terminal_scalar_bound_local_late_guarded_P6HS`**（PROVED）：
  P6HP2 terminal late kernel 逐字，`hslabE` / `hderE` / `hgradE` 的每个求值点多 c⋆ guard
  `(t − v′)·max(q, R(t, z)) ≤ 1/(2·max(Cder, 1))`（`z` = trace 终端点 / 当前点，`t` = top 时刻）；
  内部以 `Ĉ := max Cder 1` 调 G1（`Bw := 1/2`）。结论逐字。
* **`hlocBCD_of_localSupplies_gate_late_guarded_P6HS`**（PROVISIONAL：binder 同 P6HP2 gate，
  `hderivL` / `hgradL` 换 c⋆ guard 形）：两槽在原文的阈值 `Cg·R_k < R(v′, ·)` 后多
  `(t − v′)·max(max 4 Cg·R_k, R(t, z)) ≤ 1/(2·max(Cder, 1))`
  （= SLTPROD G3c `hstayLocStar_of_firstExit_P6SP` 结论的 guard 形，`Ctime′ := Cder`）；
  其余 binder（`hmargin hrecords hpinch hkappaL`）与结论逐字。
  原调用 l.614 / 617 全覆盖：gate 是 `hderivL` / `hgradL` 的唯一消费者（台账 L7）；槽 guard 的阈值取 kernel 的
  `q = max 4 Cg·R_k`（逐字传递，无需单调换算；G3c 的 `Cg′ := max 4 Cg ≥ 1`）。
**不声称** `hstaySlot` 已付：槽的 guarded 形仍需 producer（hgood + c⋆ stay，gate 帧 `t ↑ σ`）。
生成：build-logs/scratch/HSTAY-A4/gen/gen2.py（P6HP2 l.36–43 / 50–217 / 223–695 切文本 + 断言替换）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open ObservedHistory

/-- `√a ≤ 2√b`（`a ≤ 4b`；BCDT 私有引理的副本）。 -/
private theorem sqrt_le_two_mul_sqrt_P6HS {a b : ℝ} (h : a ≤ 4 * b) :
    Real.sqrt a ≤ 2 * Real.sqrt b := by
  have h4 : Real.sqrt (4 * b) = 2 * Real.sqrt b := by
    rw [Real.sqrt_mul (by norm_num) b, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt h

/-- **terminal late kernel guarded 孪生（`_P6HS`，PROVED ⇐ G1）**：
`terminal_scalar_bound_local_late_P6HP2` 逐字，U 侧导数 / 梯度只在 c⋆ guard 上要求。 -/
theorem RetainedCoreHistory.terminal_scalar_bound_local_late_guarded_P6HS {ε : ℝ}
    (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ)
    (hκ : 0 < κ) (Cder Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A) (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ 0 < ζ₀ ∧ 0 < Bw ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ (x : (K.toHistory.event j).incoming.terminalRegularOpen) (Rk q ρ : ℝ),
      metricScalarAt (K.toHistory.event j).terminal.metric x = Rk → 0 < Rk →
      0 < q → q ≤ Cq * Rk →
      2 * Λ ≤ Rk → 4 * Λ ≤ Rk * K.time j.succ → 2 * Λ ≤ ρ * Real.sqrt Rk →
      T₀ ≤ K.time j.succ - 3 * Bw / Rk →
      (∀ᶠ t in 𝓝[<] K.time j.succ,
        ∀ (first : Fin (K.eventCount + 1)) (hfl : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ (B : BackwardPointTrace K.toHistory first j.castSucc hfl z)
          (i : Fin K.eventCount) (hf : first ≤ i.castSucc) (hij : i.castSucc < j.castSucc),
        ∀ v' ∈ Ioo (K.time i.castSucc) (K.time i.succ), t - 3 * Bw / Rk ≤ v' →
          q < (K.toHistory.event i).incoming.flow.scalar v' (B.point i.castSucc hf hij.le) →
          (t - v') * max q ((K.toHistory.event j).incoming.flow.scalar t z) ≤
            1 / (2 * max (Cder : ℝ) 1) →
          |derivWithin (fun w' => (K.toHistory.event i).incoming.flow.scalar w'
              (B.point i.castSucc hf hij.le)) (Iic v') v'| ≤
            Cder * (K.toHistory.event i).incoming.flow.scalar v'
              (B.point i.castSucc hf hij.le) ^ 2) →
      (∀ᶠ t in 𝓝[<] K.time j.succ,
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ v' ∈ Ioo (K.time j.castSucc) t, t - 3 * Bw / Rk ≤ v' →
          q < (K.toHistory.event j).incoming.flow.scalar v' z →
          (t - v') * max q ((K.toHistory.event j).incoming.flow.scalar t z) ≤
            1 / (2 * max (Cder : ℝ) 1) →
          |derivWithin (fun w' => (K.toHistory.event j).incoming.flow.scalar w' z) (Iic v') v'| ≤
            Cder * (K.toHistory.event j).incoming.flow.scalar v' z ^ 2) →
      (∀ᶠ t in 𝓝[<] K.time j.succ,
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ v' ∈ Ioo (K.time j.castSucc) t, t - 3 * Bw / Rk ≤ v' →
          q < (K.toHistory.event j).incoming.flow.scalar v' z →
          (t - v') * max q ((K.toHistory.event j).incoming.flow.scalar t z) ≤
            1 / (2 * max (Cder : ℝ) 1) →
          ∀ ξ : TangentSpace ThreeModel z,
            |scalarDifferential (K.toHistory.event j).incoming.flow v' z ξ| ≤
              Cgrad * (K.toHistory.event j).incoming.flow.scalar v' z *
                Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' z) *
                Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner z ξ ξ)) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        t - 3 * Bw / Rk ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ∀ x' : (K.stage j.castSucc).Carrier,
        riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1 x' <
            ENNReal.ofReal (2 * Rad / Real.sqrt Rk) →
        q < (K.toHistory.event j).incoming.flow.scalar t x' →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric t)
          ε C1 C2 x', W.capTubeHasNeckChart ε) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ)
        (hl : i.succ ≤ j.castSucc) (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl x.1)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (w : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window w ∧ ‖w.val‖ < Dcap + 1 ∧
          t - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (K.toHistory.event j).terminal.metric x (A / Real.sqrt Rk),
        metricScalarAt (K.toHistory.event j).terminal.metric z ≤ 2 * Q * Rk := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, -, -, hζ₀, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_localDeriv_guarded_P6HS hεle κ C1 C2 hκ (max Cder 1)
      Cgrad hphi (2 * A) (by positivity) (2 * Cq)
  obtain ⟨Bw, hBwdef⟩ : ∃ Bw : ℝ, Bw ∈ ({1 / 2} : Set ℝ) := ⟨_, rfl⟩
  have hBw : (0 : ℝ) < Bw := by rw [Set.mem_singleton_iff.mp hBwdef]; norm_num
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hζ₀, hBw, ?_⟩
  intro K j p T₀ records hcan hRr hord hacc hpinch x Rk q ρ hRx hRk hq hqC hΛR hΛt hΛρ
    hT₀ hslabE hderE hgradE hncE hW hnot z hz
  have hs : K.time j.castSucc < K.time j.succ := K.time_strictMono Fin.castSucc_lt_succ
  have hs0 : 0 < K.time j.succ := by
    by_contra hneg
    have : Rk * K.time j.succ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hRk.le (not_lt.mp hneg)
    linarith
  have hBR : 0 < Bw / Rk := div_pos hBw hRk
  have hxlim := (K.toHistory.event j).terminal.tendsto_metricScalarAt x
  rw [hRx] at hxlim
  have hxev := hxlim (Ioo_mem_nhds (show Rk / 2 < Rk by linarith) (show Rk < 2 * Rk by linarith))
  apply le_of_tendsto ((K.toHistory.event j).terminal.tendsto_metricScalarAt z)
  filter_upwards [Ioo_mem_nhdsLT hs,
    Ioo_mem_nhdsLT (show K.time j.succ / 2 < K.time j.succ by linarith),
    Ioo_mem_nhdsLT (show K.time j.succ - Bw / Rk < K.time j.succ by linarith), hxev,
    (K.toHistory.event j).terminal.eventually_riemannianEDistOf_lt x z hz, hW, hnot,
    hslabE, hderE, hgradE, hncE]
    with t ht1 ht2 ht3 hRt hdt hWt hnott hslt hdert hgradt hnct
  have hRt' : Rk / 2 < (K.toHistory.event j).incoming.flow.scalar t x.1 ∧
      (K.toHistory.event j).incoming.flow.scalar t x.1 < 2 * Rk := hRt
  set Rt := (K.toHistory.event j).incoming.flow.scalar t x.1 with hRtdef
  have hRt0 : 0 < Rt := by linarith [hRt'.1]
  have hsRt : 0 < Real.sqrt Rt := Real.sqrt_pos.mpr hRt0
  have hsRk : 0 < Real.sqrt Rk := Real.sqrt_pos.mpr hRk
  have hkt : Real.sqrt Rk ≤ 2 * Real.sqrt Rt :=
    sqrt_le_two_mul_sqrt_P6HS (by linarith [hRt'.1])
  have htk : Real.sqrt Rt ≤ 2 * Real.sqrt Rk :=
    sqrt_le_two_mul_sqrt_P6HS (by linarith [hRt'.2])
  have hpinchW : ∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
      (K.toHistory.event i).incoming.flow
      (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi :=
    hpinch
  have hBt : Bw / Rt ≤ 2 * Bw / Rk := by
    rw [div_le_div_iff₀ hRt0 hRk]
    nlinarith [hRt'.1]
  have h3B : 3 * Bw / Rk = Bw / Rk + 2 * Bw / Rk := by ring
  have hT₀t : T₀ ≤ t - Bw / Rt := by
    linarith [ht3.1]
  have hwinT : t - 3 * Bw / Rk ≤ t - Bw / Rt := by
    linarith
  have hCq : 0 ≤ Cq := by
    by_contra hneg
    have : Cq * Rk < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hRk
    linarith
  have hqC' : q ≤ 2 * Cq * Rt := by
    nlinarith [mul_le_mul_of_nonneg_left hRt'.1.le hCq]
  have hΛt' : Λ ≤ Rt * t := by
    have h1 : Rk / 2 * (K.time j.succ / 2) ≤ Rt * t :=
      mul_le_mul hRt'.1.le ht2.1.le (by linarith) hRt0.le
    nlinarith
  have hρ0 : 0 < ρ := by
    by_contra hneg
    have : ρ * Real.sqrt Rk ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hsRk.le
    linarith
  have hΛρ' : Λ ≤ ρ * Real.sqrt Rt := by
    have : ρ * Real.sqrt Rk ≤ ρ * (2 * Real.sqrt Rt) := mul_le_mul_of_nonneg_left hkt hρ0.le
    nlinarith
  have hU : ∀ w ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (Rad / Real.sqrt Rt), w ∈ riemannianBallOf
        ((K.toHistory.event j).incoming.flow.base.metric t) x.1 (2 * Rad / Real.sqrt Rk) := by
    intro w hw
    rcases le_or_gt 0 Rad with hRad | hRad
    · refine lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRt hsRk]
      nlinarith [mul_le_mul_of_nonneg_left hkt hRad]
    · have h0 : ENNReal.ofReal (Rad / Real.sqrt Rt) = 0 :=
        ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hRad.le hsRt.le)
      have hw' : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1 w <
          ENNReal.ofReal (Rad / Real.sqrt Rt) := hw
      rw [h0] at hw'
      exact absurd hw' (not_lt_zero)
  have hzt : z.1 ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (2 * A / Real.sqrt Rt) := by
    refine lt_of_lt_of_le hdt (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ hsRk hsRt]
    nlinarith [mul_le_mul_of_nonneg_left htk hA.le]
  have hBwdef' : Bw = 1 / 2 := Set.mem_singleton_iff.mp hBwdef
  subst hBwdef'
  have hC1 : (1 : ℝ) ≤ ((max Cder 1 : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right Cder 1
  have hC0 : (0 : ℝ) < ((max Cder 1 : ℝ≥0) : ℝ) := zero_lt_one.trans_le hC1
  have hb := hmain K j T₀ records hcan hRr hord hacc hpinchW t ht1.1 ht1.2 x.1 q ρ hT₀t hq hqC'
    (by linarith [hRt'.1]) hΛt' hΛρ'
    (riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (2 * Rad / Real.sqrt Rk)) hU
    (fun w hw hqw => hWt w hw hqw)
    (fun first hfl z' hz' B i hf hij v' hv' hwin hqv hg => abs_le_maxOne_mul_sq_P6WA2
      (hslt first hfl z' hz' B i hf hij v' hv' (hwinT.trans hwin) hqv
        (by rw [← coe_max_one_P6WA2]; exact mul_max_le_cstar_of_guard_P6WA2 hC0 hg)))
    (fun z' hz' v' hv' hwin hqv hg => abs_le_maxOne_mul_sq_P6WA2
      (hdert z' hz' v' hv' (hwinT.trans hwin) hqv
        (by rw [← coe_max_one_P6WA2]; exact mul_max_le_cstar_of_guard_P6WA2 hC0 hg)))
    (fun z' hz' v' hv' hwin hqv hg ξ => hgradt z' hz' v' hv' (hwinT.trans hwin) hqv
        (by rw [← coe_max_one_P6WA2]; exact mul_max_le_cstar_of_guard_P6WA2 hC0 hg) ξ)
    (fun τ hτ1 hτ2 hτ3 hτ4 z' hz' zz hzz b hb0 hbρ hctrl =>
      hnct τ (hwinT.trans hτ1) hτ2 hτ3 hτ4 z' hz' zz hzz b hb0 hbρ hctrl)
    hnott z.1 hzt
  change (K.toHistory.event j).incoming.flow.scalar t z.1 ≤ 2 * Q * Rk
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  calc (K.toHistory.event j).incoming.flow.scalar t z.1 ≤ Q * Rt := hb
    _ ≤ Q * (2 * Rk) := mul_le_mul_of_nonneg_left hRt'.2.le hQ0
    _ = 2 * Q * Rk := by ring

/-- **FOOT3 gate guarded 孪生（`_P6HS`，PROVISIONAL：binder 同 P6HP2 gate，`hderivL` / `hgradL` 换 c⋆
guard 形）**：结论逐字；kernel = `terminal_scalar_bound_local_late_guarded_P6HS`。 -/
theorem hlocBCD_of_localSupplies_gate_late_guarded_P6HS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Aseed : ℝ}
    {q : CutoffParameters}
    (hεle : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cg : ℝ} {Cder Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hmargin :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ)
    (hrecords :
      ∀ (Rrad ζ₀ B Dcap : ℝ), 0 < ζ₀ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (T₀ : ℝ)
          (records : ∀ i' : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time i'.succ →
            GeometricCutoffRecord (Kh k) i' pp),
          (∀ i' hT b, ((records i' hT).static b).hasCanonicalWindow) ∧
          Rrad ≤ pp.modelRadius ∧ 2 ≤ pp.modelOrder ∧ pp.modelAccuracy ≤ ζ₀ ∧
          T₀ ≤ (σ k : ℝ) - B / R k ∧
          ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ¬ ∃ (i' : Fin (Kh k).eventCount)
              (hT : T₀ ≤ (Kh k).time i'.succ) (hl : i'.succ ≤ (i k).castSucc)
              (Btr : BackwardPointTrace (Kh k) i'.succ (i k).castSucc hl p')
              (b : ((Kh k).event i').RetainedBoundaryIndex)
              (w : standardCapWindow pp.modelRadius),
              Btr.point i'.succ le_rfl hl = ((records i' hT).static b).window w ∧
                ‖w.val‖ < Dcap + 1 ∧
                t - (Kh k).time i'.succ ≤ 1 / 2 * (((records i' hT).static b).neck.scale)⁻¹)
    (hpinch :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ i' : Fin (Kh k).eventCount,
          Perelman.PhiAlmostNonnegative ((Kh k).event i').incoming.flow
            (Ico ((Kh k).time i'.castSucc) ((Kh k).time i'.succ) ∩ Ici (1 / 2)) phi)
    (hderivL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Cder : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Cder * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Cder : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Cder * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2)
    (hgradL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Cder : ℝ) 1) →
                ∀ ξ : TangentSpace ThreeModel z,
                  |scalarDifferential ((Kh k).event (i k)).incoming.flow v' z ξ| ≤
                    Cgrad * ((Kh k).event (i k)).incoming.flow.scalar v' z *
                      Real.sqrt (((Kh k).event (i k)).incoming.flow.scalar v' z) *
                      Real.sqrt
                        ((((Kh k).event (i k)).incoming.flow.base.metric v').inner z ξ ξ))
    (hkappaL :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∃ ρ : ℕ → ℝ, Tendsto (fun k => ρ k * Real.sqrt (R k)) atTop atTop ∧
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : Icc (0 : ℝ) (Kh k).horizon,
              t - T / R k ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
              (Kh k).time (i k).castSucc < τ → (τ : ℝ) < (Kh k).time (i k).succ →
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (zz : ((Kh k).stageAt τ).Carrier), HEq zz z →
              ∀ (b : ℝ), 0 < b → b ≤ ρ k →
                (Kh k).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh k).stageAt τ).Carrier
                    ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
                    (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage τ) τ) zz b)) :
      ∀ A : ℝ, 0 < A → ∃ QA : ℝ, 0 < QA ∧
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
          (∀ k, 2 < (Tn k : ℝ)) →
          (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
            q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ∀ hcross : ((Kh k).event (i k)).RegularCrossing p' q,
          ∀ z ∈ riemannianBallOf ((Kh k).event (i k)).terminal.metric
              ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ (A / Real.sqrt (R k)),
            metricScalarAt ((Kh k).event (i k)).terminal.metric z ≤ QA * R k := by
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.terminal_scalar_bound_local_late_guarded_P6HS hεle κ C1 C2 hκ Cder Cgrad
      hphi A hA
      (max 4 Cg)
  refine ⟨2 * Q, by positivity, ?_⟩
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
      hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ i hi
  have hrad : (0 : ℝ) < max (2 * Rad) 1 := lt_max_of_lt_right one_pos
  have h3B : (0 : ℝ) < 3 * Bw := by positivity
  have hrec := hrecords Rrad ζ₀ (3 * Bw) Dcap hζ₀
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hpi := hpinch
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hma := hmargin
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hde := hderivL (3 * Bw) (max (2 * Rad) 1) h3B hrad
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hgr := hgradL (3 * Bw) (max (2 * Rad) 1) h3B hrad
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  obtain ⟨ρ, hρlim, hka⟩ := hkappaL (3 * Bw) (max (2 * Rad) 1) h3B hrad
    ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hdσ i hi
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hrec, hpi, hde, hgr, hka, hma, hRlim.eventually_ge_atTop (4 * Λ),
    hρlim.eventually_ge_atTop (2 * Λ), hL.eventually_ge_atTop (max (4 * Rad) 1),
    haS 1 one_pos, haS (3 * Bw) h3B] with k hrk hpk hdk hgk hkk hmk hR4 hρk hLk haSk haSk3
  intro p' q hq hcross
  obtain ⟨pp, T₀, records, hcan, hRr', hord, hacc, hT₀, hnotk⟩ := hrk
  have hRk := hRpos k
  have hsR : 0 < Real.sqrt (R k) := Real.sqrt_pos.mpr hRk
  have hLpos : 0 < L k := by linarith [le_max_right (4 * Rad) 1]
  have haσ : (aSeed k : ℝ) < σ k := by
    have := div_pos one_pos hRk
    linarith
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hσT : (σ k : ℝ) ≤ Tn k := Subtype.coe_le_coe.mpr (hsT k)
  have h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc :=
    (Kh k).activeStage_le_castSucc_P6HE (i k) (aSeed k) (by rw [← hσs]; exact haσ)
  have h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k) :=
    (Kh k).le_activeStage (Tn k) (i k).castSucc (by rw [← hσs] at hcs; linarith)
  have hRx : metricScalarAt ((Kh k).event (i k)).terminal.metric
      ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ = R k := by
    rw [MetricCutCapEvent.RegularCrossing.scalar_eq ((Kh k).event (i k))
        (p := ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩) hcross, hRdef k,
      (Kh k).scalar_eq_of_heq_P6BT (i k) (hi k) hq]
  have hq4 : 4 * R k ≤ max 4 Cg * R k :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hRk.le
  have hCgq : Cg * R k ≤ max 4 Cg * R k :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hRk.le
  have hqpos : 0 < max 4 Cg * R k := mul_pos (lt_max_of_lt_left (by norm_num)) hRk
  have hr : 2 * Rad / Real.sqrt (R k) ≤ L k / (2 * Real.sqrt (R k)) := by
    rw [div_le_div_iff₀ hsR (by positivity)]
    have h4 : 4 * Rad ≤ L k := (le_max_left _ _).trans hLk
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) hsR.le]
  have hδ : 0 < L k / (2 * Real.sqrt (R k)) := by positivity
  have hCN := RetainedCoreHistory.eventually_witness_of_hwin_P6BT
    ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (i k) (haT k) (seedTrace k) (hsT k)
    (has k) (hi k) (y k) hRk hLpos haσ (hgood k) h1 h2 p' (hmk p' q hq hcross h1 h2 _ hδ) hr hq4
  have hσ1 : 1 ≤ (σ k : ℝ) := (hone k).trans (Subtype.coe_le_coe.mpr (has k))
  have hΛt : 4 * Λ ≤ R k * (Kh k).time (i k).succ := by
    rw [← hσs]
    nlinarith
  have hball : ∀ (t : ℝ) (z' : ((Kh k).stage (i k).castSucc).Carrier),
      z' ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (2 * Rad / Real.sqrt (R k)) →
      z' ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (max (2 * Rad) 1 / Real.sqrt (R k)) := fun t z' hz' =>
    lt_of_lt_of_le hz' (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le))
  have hdk' := hdk p' q hq hcross
  have hgk' := hgk p' q hq hcross
  have hkk' := hkk p' q hq hcross
  let records' := records_raise_P6HP2 (H := Kh k) (p := pp) (T₀ := T₀) (1 / 2) records
  exact hmain ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (i k) (max T₀ (1 / 2))
    records'
    (fun i' hT b => hcan i' ((le_max_left T₀ (1 / 2)).trans hT) b) hRr' hord hacc
    (hpinch_slot_threshold_P6HP2 (Kh := Kh k) hpk T₀)
    ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ (R k)
    (max 4 Cg * R k) (ρ k) hRx hRk hqpos le_rfl (by linarith) hΛt hρk
    (by rw [hσs] at hT₀ haSk3; exact max_le hT₀ (by linarith [hone k]))
    (hdk'.mono fun t ht first hfl z' hz' B i' hf hij v' hv' hwin hqv hg =>
      ht.1 first hfl z' (hball t z' hz') B i' hf hij v' hv' hwin (lt_of_le_of_lt hCgq hqv) hg)
    (hdk'.mono fun t ht z' hz' v' hv' hwin hqv hg =>
      ht.2 z' (hball t z' hz') v' hv' hwin (lt_of_le_of_lt hCgq hqv) hg)
    (hgk'.mono fun t ht z' hz' v' hv' hwin hqv hg ξ =>
      ht z' (hball t z' hz') v' hv' hwin (lt_of_le_of_lt hCgq hqv) hg ξ)
    (hkk'.mono fun t ht τ hτ1 hτ2 hτ3 hτ4 z' hz' zz hzz b hb0 hbρ hctrl =>
      ht τ hτ1 hτ2 hτ3 hτ4 z' (hball t z' hz') zz hzz b hb0 hbρ hctrl)
    hCN ((hnotk p' q hq hcross).mono fun t ht hex => ht (by
      obtain ⟨i', hT, hl, Btr, b, w, hw⟩ := hex
      exact ⟨i', (le_max_left T₀ (1 / 2)).trans hT, hl, Btr, b, w, hw⟩))


/-- consumer（G2）：guarded gate 的类型检查（binder 对齐 = 本陈述）。 -/
example := @hlocBCD_of_localSupplies_gate_late_guarded_P6HS.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
