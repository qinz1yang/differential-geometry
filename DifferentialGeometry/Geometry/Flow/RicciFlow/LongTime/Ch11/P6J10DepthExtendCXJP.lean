import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10DepthScalCXJP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireCeilP6JW

/-!
# hextend 深度步 G3：无 J10 的 `hextend` 槽（CX-J10DEPTH，后缀 `_CXJP`）

`hextend_of_extendAt_lateHI_P6LT`（`P6TracedDepthHIP6LT:333`，内部 `Local/CrossingDepthHI_P6LL`）的无 J10
孪生 `crossingDepthHI_extend_noJ10_CXJP`：删 `hqR`。原文 `hqR` 的三处用途：
* `:95` `0 < R`：`hR` / `hRlim`（`eventually_one_le_of_tendsto_P6JC`）；
* 核调用：`crossingTracedHI_noJ10_P6JC`（吃 `hR1`；B5 / `hslab` / `hderG` 为 cap 输入，不动）；
* `:198` 延伸窗 `[w, a₁)` 的 trace ODE（`nlinarith [hqR n]`，cap 阈值 `2·qcan ≤ 2(M+1)R`）：改为
  G1/G2 —— 上一步 traced region（`[a₁, t]`，`|Rm| ≤ K₁R`）+ **本步独立 anchor**（`R(a₁) ≤ M·R`）⇒
  `hscalC` ⇒ first-exit 整窗定位（CXJF2 的 `hUSCtop` 由 extendAt 付；crossing 条件保护由 `hsepX`）⇒
  hgood 时间分量 ceiling ODE（阈值 `Cg·R`）。
结论 = J10GEN state §hextend 槽逐字，`Cext := Ctime′·max(Cg,1)`（只含 selected 侧常数，不比较 `Ctime`
与 `Ctime′`；单步即满足 ODE 深度条件 `2·Ctime′·max(M,Cg,1)·(Tg − T′) ≤ 3/16`，无需子步）。
输入只用 B5 核族 + J10WIRE (B) 族 + `hR`/`hRlim`；无 `qcan < R`、无 `hqcan2`、无 isTracedRegion 目标前提
（traced region 只取 `hext` 已给的上一步数据）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 数值（`_CXJP`）：`0 ≤ a`、`0 ≤ Q_b`、`1 ≤ R` ⇒ `2·max(a, 2Q_bR) ≤ (2a + 4Q_b)·R`。 -/
theorem two_max_le_CXJP {a Qb R : ℝ} (ha : 0 ≤ a) (hQb : 0 ≤ Qb) (hR : 1 ≤ R) :
    2 * max a (2 * (Qb * R)) ≤ (2 * a + 4 * Qb) * R := by
  rcases le_total a (2 * (Qb * R)) with hle | hle
  · rw [max_eq_right hle]
    nlinarith
  · rw [max_eq_left hle]
    nlinarith

open ObservedHistory in
/-- **无 J10 的 `hextend` 槽（`_CXJP`）**：见文件头。 -/
theorem crossingDepthHI_extend_noJ10_CXJP
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
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (aSeed n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale)
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
        (aSeed n : ℝ) < ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.time
          e.succ →
        (2 * (3 / r ^ 2) + 4 * Qb) * (G n).flow.scalar (t n) (y n) <
          ((recordsX n e he).static b).neck.scale) ∧
      Tg < (G n).flow.scalar (t n) (y n) * t n) := by
    filter_upwards [hacc0, hwin Tg hTg0, hRlim.eventually_ge_atTop 1,
      hL.eventually_gt_atTop (2 * (A + 8 * Tg / c)),
      hL.eventually_ge_atTop (4 * (localPropagationRadius C2' / Real.sqrt (2 * Qb))),
      hL.eventually_ge_atTop (Tg + 1), hsepX (2 * (3 / r ^ 2) + 4 * Qb),
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
    have h := hsc e he b (lt_of_le_of_lt haS hlt)
    have hr2 : 0 ≤ 3 / r ^ 2 := by positivity
    exact lt_of_le_of_lt (two_max_le_CXJP hr2 (zero_le_one.trans hQb1) hRn1) h
  have hprotC := hprotC_scalC_CXJP KH (haT n) (hsmall n) (hclock n) (seedTrace n) (hsT n)
    (has n) (ys n) (L n) haS hwt B hscalC (recordsX n) (hDmX n) hnc hscale'
  have hgV := hgoodV_scalC_CXJP hC2 KH (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀X n)
    (hpinX n) (hsT n) (has n) (ys n) (L n) hR' (hgood n) hCgQb haS hwt
    (hUSCtop_extendAt_CXJF2 (H n) (hend n) (G n) (hGi n) (hat n) (hts n) _)
    haL hdepth hRa' B hscalC hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀X n).trans haS) (recordsX n)
    (hOldX n) (hcanX n) ((haccX n).trans (hεn.trans (min_le_right _ _))) (hDmX n) hprotC hx
    (hfinX n) hmarg
  exact hscalC v hwv hvt fun v' hav' hv'σ _ => hgV v' hav' hv'σ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
