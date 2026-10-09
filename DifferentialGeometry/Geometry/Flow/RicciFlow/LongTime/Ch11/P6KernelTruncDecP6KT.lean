import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelAssembleDecP6JK2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DbbMinRescaleP6KT

/-!
# kernel 截断孪生：event dec（rings / closed / notK）（O-CH11-KTRUNC1 G2，`_P6KT`）

J10KERNEL 的 kernel producer（`_P6JK2`）在 kernel body 槽改**截断形**后的孪生（lead 10-08 裁定 `tK := Tn`）：
陈述逐字，`hslabK`（final：(D1)(D2)）终点换 `min … (tK n)`，`{Q T₀ tK}`，`has` 后加 `hTnK`；结论逐字（`False`）。
证明逐字；只在 rings 层两处使用点做 min 处理（G0 核查：全部使用点 `≤ t n = σ n ≤ Tn n ≤ tK n`），
closed / notK 层只多传 `hTnK`。PROVISIONAL 与原 `_P6JK2` 同槽（anchor `hWBloc`/`hslabsLoc`、slice `hbcadC`、(B)
行），
无新 binder。孪生对：`false_of_selection_eventSlab_lateHI_closed_rings_noJ10_dec_P6JK2` ↦
`false_of_selection_eventSlab_lateHI_closed_rings_noJ10_dec_P6KT`,
`false_of_selection_eventSlab_lateHI_closed_noJ10_dec_P6JK2` ↦
`false_of_selection_eventSlab_lateHI_closed_noJ10_dec_P6KT`,
`false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_noJ10_dec_P6JK2` ↦
`false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_noJ10_dec_P6KT`。
生成：`build-logs/scratch/O-CH11-KTRUNC1/gen/gen_g2.py`（替换计数断言）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6)

namespace ObservedHistory

/-- **`false_of_selection_eventSlab_lateHI_closed_rings_noJ10_dec_P6JK2` 的截断孪生（O-CH11-KTRUNC1
G2，`_P6KT`，PROVISIONAL 同原：槽 = 原同名 binder）**：陈述 = 原陈述逐字，`hslabK` 换截断形（`{Q T₀ tK}`，终点 `min … (tK
n)`，`has` 后加 `hTnK : ∀ n, (Tn n : ℝ) ≤ tK n`）；结论逐字。证明逐字 + 使用点 min 处理（`hderG`：当前 slab 到 `t n` ⇐
`lt_min`；prefix slab：`time i.succ ≤ time (j n).castSucc < t n ≤ tK n`）。 -/
theorem false_of_selection_eventSlab_lateHI_closed_rings_noJ10_dec_P6KT {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hC1 : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (hC2 : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁) (hCt : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁)
    {C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2' : 0 ≤ C2') :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ tK : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (hslabK : ∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (hnotK : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) →
      {κd : ℝ} → (hκd : 0 < κd) →
      (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) →
      {aP : ℝ} → (haP : 0 < aP) →
      (hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) →
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
            Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) →
      (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) 1) →
      (hhalf : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n) →
      (ha₀ : ∀ n, 0 < a₀ n) →
      (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (p n).modelRadius) →
      (hT₀X : ∀ n, T₀ n ≤ aSeed n) →
      (hRa : ∀ n, 1 ≤ (aSeed n : ℝ)) →
      (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount)
        (hi : T₀ n ≤ (K n).time i.succ) b, (aSeed n : ℝ) < (K n).time i.succ →
          M * R n < ((recordsK n i hi).static b).neck.scale) →
      (hfinX : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) →
      False := by
  intro Ctime phi hphi K j t hjt htj Q T₀ tK p pF recordsK recordsF yG a₀ hHI hcanK hδF hacc hrad
    hord hscaleK hbirthA hpinchK0 hslabK hnotK Kh hKh σ y R hσ hyG hRn hRpos hRlt κd hκd hvolK aP
    haP hpinL hT₀ Tn aSeed haT hsT has hTnK pT seedTrace L hL Cg hgood hwin hdistC hanchor0 hbcadC
    hclock hsmall hhalf ha₀ hDmX hT₀X hRa hsepX hfinX hsel
  -- (1b) 条件形 witness / 导数界（`hdistC` 余量 `L/4 ≤ L`；closed-kappa 原文）
  obtain ⟨hwitC, hderivKC⟩ := hwitC_hderivC_of_hdistC_Cg_P6CD Kh Tn aSeed σ haT hsT has pT seedTrace
    y R L hRpos hL hgood hwin (fun φ hφ D T Kc hD hT hKc htr => by
      filter_upwards [hdistC φ hφ D T Kc hD hT hKc htr,
        (hL.eventually_ge_atTop 0).filter_mono hφ.tendsto_atTop] with n hn hL0
      intro x hx v hav hvs hvT tr
      refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hRlt n).le)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨qcan, θcap, D, hqc, hθ, hD, hqcan, hQq, hθcap, hDn⟩ := exists_params_P6D Q
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hscale : ∀ (n : ℕ) (i : Fin ((K n).prefixAt (j n).castSucc).eventCount) hi b,
      ((n : ℝ) + 1) * qcan n ≤
        (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale :=
    fun n i hi b => by
      rw [hqc n]
      exact hscaleK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi b
  have hslabT' : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (qcan n)
        (min ((K n).time i.succ) (tK n)) :=
    fun n i y v hv hR => hslabK n i y v hv ((hQq n).trans_lt hR)
  -- 截断点（KTRUNC1 G0）：使用点都在 `t n = σ n ≤ Tn n ≤ tK n` 之前
  have htTK : ∀ n, t n ≤ tK n := fun n => by
    have h1 : (σ n : ℝ) ≤ (Tn n : ℝ) := hsT n
    rw [← hσ n]
    exact h1.trans (hTnK n)
  have hpreT : ∀ n (i : Fin (K n).eventCount), i.castSucc < (j n).castSucc →
      (K n).time i.succ ≤ tK n := fun n i hi => by
    have h1 : i.succ ≤ (j n).castSucc := by
      rw [Fin.lt_def] at hi
      rw [Fin.le_def]
      simp only [Fin.val_castSucc, Fin.val_succ] at hi ⊢
      omega
    have h2 := (K n).time_strictMono.monotone h1
    linarith [hjt n, htTK n]
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  have hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n) := fun n x v hv hR => by
    have hlt : qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x := by
      have := hq0 n
      linarith
    have h := hslabT' n (j n) x v
      ⟨hv.1, lt_min (hv.2.trans (htj n)) (hv.2.trans_le (htTK n))⟩ hlt
    rw [hctime]
    have h0 : 0 ≤ (Ctime : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 :=
      mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
    linarith
  have hnot := fun n => (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n)
    (yG n) (hnotK n)
  have hnot' : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θcap n *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    fun n => by
      rw [hD n, hθ n]
      exact hnot n
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK0 n (j n)⟩
  have hbirthA' : ∀ᶠ n in atTop, ∀ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount) hi b,
      1 ≤ a₀ n *
        (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale :=
    hbirthA.mono fun n hn i hi b => hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi b
  have hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) :=
    fun n => (K n).eventSlabsDerivative_prefixAt _
      (fun i hi => ((K n).toHistory.event i).incoming.derivativeBoundBefore_mono
        (le_min le_rfl (hpreT n i hi)) (hslabT' n i))
  have hHI' := fun n => (K n).hHI_prefixAt_P6LT (j n).castSucc (hHI n)
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n)
  have hδF' : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ 1 / ((n : ℝ) + 1) :=
    fun n i hi => hδF n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hi
  have hk := exists_tracedKappa_of_kseq_P6D2 hvolK
  obtain ⟨ρnc, hradii, hkappa⟩ := hk
  obtain ⟨Phi, hPhi, hpinchK⟩ := exists_tracedPinching_of_late_P6CK (y := y) haP hpinL
  subst hKh
  have hC20 : 0 ≤ C2' := hC2'
  -- E 帧（`Hs n = (K n).eventPrefix (j n) (t n)`；P6CD 原式）
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  -- (B) seed：J10GEN2A G5（hgapJ 合同 seed `r = 1` ⇒ E seed，`rX = 1/100`）
  obtain ⟨aE, haTE, pTE, seedE, haa, hseedC, hsmallE, hclockE⟩ :=
    exists_seedSeq_hsmall_eventPrefix_P6JA (K := K) (j := j) (t := t) (hjt := hjt) (htj := htj)
      (Hs := Hs) (fun _ => rfl) (ts := ts) (σ := σ) hσ' Tn aSeed haT hsT has pT seedTrace
      hclock hsmall hhalf
  have hrX : (0 : ℝ) < 1 / 100 := by norm_num
  -- (B) hpinX：HIPROP K 层 HI 传播 + C11G2 eventPrefix 搬运（`a₀X := a₀`）
  have hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ n + τ) x :=
    fun n τ x => (K n).inFixedHI_eventPrefix_C11G2 (j n) (hjt n) (htj n)
      (ObservedHistory.hiActive_of_records_P6HP (K n).toHistory (recordsF n) (ha₀ n) (hHI n)) τ x
  -- (B) records-X ⇐ recordsK 限制（C11G2 eventPrefix records，`qX := p`、`T₀X := T₀`）
  let recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (p n) := fun n =>
    (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recordsK n)
  have hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow := fun n =>
    (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recordsK n) (hcanK n)
  have hmX : ∀ n, 2 ≤ (p n).modelOrder := fun n => (Nat.le_add_left 2 n).trans (hord n)
  have hT₀E : ∀ n, T₀ n ≤ aE n := fun n => (hT₀X n).trans (haa n)
  have hRaE : ∀ n, 1 ≤ R n * aE n := fun n => by
    have h1 : (1 : ℝ) ≤ R n := by
      have := hRlt n
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    exact one_le_mul_of_one_le_of_one_le h1 ((hRa n).trans (haa n))
  have hsepE : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀ n ≤ (Hs n).time e.succ) b, (aE n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale :=
    fun M => (hsepX M).mono fun n hn e he b hae =>
      hn (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) e) he b ((haa n).trans_lt hae)
  -- (B) hfinX ⇐ K 层行 `hfinX`（C11G2 距离搬运 + G5 seed 兼容）
  have hfinE : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
      ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (haTE n))
        ((Hs n).activeStage_mono (le_refl (ts n)))) (ys n) ≠ ⊤ := fun n => by
    have hm : (K n).toHistory.activeStage (σ n) =
        (K n).eIdx_C11G2 (j n) (hjt n) (htj n) ((Hs n).activeStage (ts n)) :=
      (Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n)
        (hσ' n))).symm
    have hpt := hseedC n (ts n) (σ n) (hσ' n) ((Hs n).activeStage_mono (haTE n))
      ((Hs n).activeStage_mono (le_refl (ts n))) ((K n).toHistory.activeStage_mono (has n))
      ((K n).toHistory.activeStage_mono (hsT n))
    have hK := hfinX n
    rw [← hσ' n] at hK
    exact ne_of_eq_of_ne ((K n).edist_eventPrefix_C11G2 (j n) (hjt n) (htj n) hm _ hpt (hysK n)) hK
  -- hctrl 环：J10GEN2A `exists_hctrl_lateHI_noJ10_P6JA`（无 `hqR`）
  obtain ⟨r₀, hr₀, hctrl⟩ := exists_hctrl_lateHI_noJ10_P6JA
    (records := fun n => (K n).prefixLateRecords_P6N (j n).castSucc (recordsK n)) hphi hjt htj
    (fun n => (K n).prefixRecords (j n).castSucc (recordsF n)) hHI' hcan hδF' hqcan hpar hscale
    hbirthA' hθcap hpinch hslab hderG hnot' hT₀' hRt hanchor0 (fun n => (K n).toHistory) rfl σ y R
    hσ hyG hRn hRpos hRlim Hs rfl ts HEq.rfl ys hys Tn aSeed haT hsT has pT seedTrace L hL hgood
    ts aE haTE (fun n => le_refl (ts n)) haTE pTE seedE haa hseedC hC20 hrX hsmallE hclockE a₀
    (fun n => (ha₀ n).le) hpinX hRaE p T₀ hT₀E recordsX (fun _ _ _ => rfl) hcanX hDmX hacc hmX hsepE
    hfinE
  have hctrl' := hctrl r₀ hr₀ le_rfl
  -- prefix 环：J10GEN2A `false_of_selection_eventSlab_lateHI_prefix_full_P6JA`
  exact false_of_selection_eventSlab_lateHI_prefix_full_dec_P6JA hη hε hεW hεX hεN hC1 hC2 hCt
    hphi hjt htj
    (records := fun n => (K n).prefixLateRecords_P6N (j n).castSucc (recordsK n))
    (fun n => (K n).prefixRecords (j n).castSucc (recordsF n)) hHI' hcan hδF' hqcan hpar
    hscale hbirthA' hθcap hpinch hslab hderG hnot' hT₀' hRt hanchor0 (fun n => (K n).toHistory)
    rfl σ y R hσ hyG hRn hr₀ hκd (hseed_of_tracedKappa_P6M hRpos ρnc hradii hkappa hr₀ hctrl') hκd
    ρnc hradii hkappa hPhi hpinchK (Cs := Cg) (Cq := Cg) (qs := fun n => Cg * R n)
    (qd := fun n => Cg * R n) (fun _ => le_rfl) (fun _ => le_rfl) hwitC hderivKC hbcadC hRpos hRlim
    Hs rfl ts HEq.rfl ys hys Tn aSeed haT hsT has pT seedTrace L hL hgood
    (fun φ hφ D T Kc hD hT hKc htr => by
      filter_upwards [hdistC φ hφ D T Kc hD hT hKc htr,
        (hL.eventually_ge_atTop 0).filter_mono hφ.tendsto_atTop] with n hn hL0
      intro x hx v hav hvs hvT tr
      refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
    ts aE haTE (fun n => le_refl (ts n)) haTE pTE seedE haa hseedC hC20 hrX hsmallE hclockE a₀
    (fun n => (ha₀ n).le) hpinX hRaE p T₀ hT₀E recordsX (fun _ _ _ => rfl) hcanX hDmX hacc hmX hsepE
    hfinE hsel

/-- **`false_of_selection_eventSlab_lateHI_closed_noJ10_dec_P6JK2` 的截断孪生（O-CH11-KTRUNC1
G2，`_P6KT`，PROVISIONAL 同原：槽 = 原同名 binder）**：陈述 = 原陈述逐字，`hslabK` 换截断形（`{Q T₀ tK}`，终点 `min … (tK
n)`，`has` 后加 `hTnK : ∀ n, (Tn n : ℝ) ≤ tK n`）；结论逐字。证明逐字 + 下层调用多传 `hTnK`（`tK` 由 `hslabK` 的类型合一）。 -/
theorem false_of_selection_eventSlab_lateHI_closed_noJ10_dec_P6KT
    (hWBloc : ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ c →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y)
    {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεcone : ε ≤ coneAccuracy)
    {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hC1 : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (hC2 : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁) (hCt : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁)
    {C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2' : 0 ≤ C2') :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ tK : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (hslabK : ∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (hnotK : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) →
      {κd : ℝ} → (hκd : 0 < κd) →
      (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) →
      {aP : ℝ} → (haP : 0 < aP) →
      (hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hslabsLoc : ∀ Rad B c : ℝ, ∀ᶠ n in atTop,
        ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
          (((K n).prefixAt (j n).castSucc).time i.succ),
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        (t n - v) * max (Cg * R n)
            (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤ c →
        Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
              (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
            (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) →
      (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) 1) →
      (hhalf : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n) →
      (ha₀ : ∀ n, 0 < a₀ n) →
      (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (p n).modelRadius) →
      (hT₀X : ∀ n, T₀ n ≤ aSeed n) →
      (hRa : ∀ n, 1 ≤ (aSeed n : ℝ)) →
      (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount)
        (hi : T₀ n ≤ (K n).time i.succ) b, (aSeed n : ℝ) < (K n).time i.succ →
          M * R n < ((recordsK n i hi).static b).neck.scale) →
      (hfinX : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) →
      False := by
  intro Ctime phi hphi K j t hjt htj Q T₀ tK p pF recordsK recordsF yG a₀ hHI hcanK hδF hacc hrad
    hord hscaleK hbirthA hpinchK0 hslabK hnotK Kh hKh σ y R hσ hyG hRn hRpos hRlt κd hκd hvolK aP
    haP hpinL hT₀ Tn aSeed haT hsT has hTnK pT seedTrace L hL Cg hCg hgood hwin hdistC hdistW
    hslabsLoc
    hbcadC hclock hsmall hhalf ha₀ hDmX hT₀X hRa hsepX hfinX hsel
  have hC20 : 0 ≤ C2' := hC2'
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  -- anchor 环：SLTLOCAL `hanchor0_eventSlab_local_P6SL`（prefix 形参数照 closed-kappa 原文）
  obtain ⟨qcan, θcap, D, hqc, hθ, hD, hqcan, hQq, hθcap, hDn⟩ := exists_params_P6D Q
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot := fun n => (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n)
    (yG n) (hnotK n)
  have hnot' : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θcap n *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    fun n => by
      rw [hD n, hθ n]
      exact hnot n
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK0 n (j n)⟩
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n)
  have hanchor0 := hanchor0_eventSlab_local_P6SL hWBloc hεcone hC20 hphi hjt htj hcan hpar hθcap
    hpinch hnot' hT₀' hRt Kh hKh σ hσ y hyG R hRpos hRn hRlt hκd hvolK Tn aSeed haT hsT has pT
    seedTrace L hL hCg hgood hwin hdistW hslabsLoc
  -- prefix / hctrl 环：G1
  exact false_of_selection_eventSlab_lateHI_closed_rings_noJ10_dec_P6KT
    hη hε hεW hεX hεN hC1 hC2 hCt hC2' hphi hjt htj recordsF hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA
    hpinchK0 hslabK hnotK Kh hKh σ y R hσ hyG hRn hRpos hRlt hκd hvolK haP hpinL hT₀ Tn aSeed haT
    hsT has hTnK pT seedTrace L hL Cg hgood hwin hdistC hanchor0 hbcadC hclock hsmall hhalf ha₀
    hDmX hT₀X hRa hsepX hfinX hsel

/-- **`false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_noJ10_dec_P6JK2`
的截断孪生（O-CH11-KTRUNC1 G2，`_P6KT`，PROVISIONAL 同原：槽 = 原同名 binder）**：陈述 = 原陈述逐字，`hslabK` 换截断形（`{Q T₀
tK}`，终点 `min … (tK n)`，`has` 后加 `hTnK : ∀ n, (Tn n : ℝ) ≤ tK n`）；结论逐字。证明逐字 + 下层调用多传 `hTnK`（`tK` 由
`hslabK` 的类型合一）。 -/
theorem false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_noJ10_dec_P6KT
    (hWBloc : ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ c →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y) :
    ∀ {η₁ : ℝ}
    (_ : 0 < η₁ ∧ η₁ < 1 / 11)
    {ε : ℝ}
    (_ : 0 < ε)
    (_ : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (_ : ε ≤ crossingWindowNeckAccuracy.{u})
    (_ : ε ≤ crossingNeckAccuracy.{u})
    (_ : ε ≤ coneAccuracy)
    {C1₁ C2₁ : ℝ}
    {Ctime₁ : ℝ≥0}
    (_ : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (_ : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁)
    (_ : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁)
    {C1' C2' : ℝ}
    {Ctime' : ℝ≥0}
    (_ : 0 ≤ C2'),
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} →
      {Q T₀ tK : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (hslabK : ∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (hpos : ∀ n, ∃ j : Fin (Kh n).eventCount, (Kh n).time j.castSucc < (σ n : ℝ) ∧
        (σ n : ℝ) < (Kh n).time j.succ) →
      (R : ℕ → ℝ) →
      (hRdef : ∀ n, R n =
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) →
      (hnotKs : ∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' → (K n).time j'.castSucc < (σ n : ℝ) → (σ n : ℝ) < (K n).time j'.succ →
        ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ j'.castSucc hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      {κd : ℝ} → (hκd : 0 < κd) →
      (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) →
      {aP : ℝ} → (haP : 0 < aP) →
      (hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvs) x,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (hdistσ : ∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
      (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
      (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
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
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hslabsLoc : ∀ (j : ∀ n, Fin (K n).eventCount)
        (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier),
        (∀ n, (K n).time (j n).castSucc < (σ n : ℝ)) →
        (∀ n, (σ n : ℝ) < (K n).time (j n).succ) → (∀ n, HEq (y n) (yG n)) →
        ∀ Rad B c : ℝ, ∀ᶠ n in atTop,
        ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (σ n : ℝ))
            (yG n)
            (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) (yG n))),
        ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
          (((K n).prefixAt (j n).castSucc).time i.succ),
        (σ n : ℝ) - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) (yG n) ≤ v →
        ((σ n : ℝ) - v) * max (Cg * R n)
            (((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) z) ≤ c →
        Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
              (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
            (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) →
      (hbcadC : 0 < κ →
        (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
        (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
        (∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
        (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
        (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
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
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
        ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) →
      (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) 1) →
      (hhalf : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n) →
      (ha₀ : ∀ n, 0 < a₀ n) →
      (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (p n).modelRadius) →
      (hT₀X : ∀ n, T₀ n ≤ aSeed n) →
      (hRa : ∀ n, 1 ≤ (aSeed n : ℝ)) →
      (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount)
        (hi : T₀ n ≤ (K n).time i.succ) b, (aSeed n : ℝ) < (K n).time i.succ →
          M * R n < ((recordsK n i hi).static b).neck.scale) →
      (hfinX : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) →
      False := by
  intro η₁ hη ε hε hεW hεX hεN hεcone C1₁ C2₁ Ctime₁ hC1 hC2 hCt C1' C2' Ctime' hC2'
    Ctime phi hphi K Q T₀ tK p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 hslabK Kh hKh σ y hpos R hRdef hRpos hRlt hnotKs κd hκd hvolK aP haP hpinL
    Tn aSeed haT hsT has hTnK hT₀ pT seedTrace L hL Cg hCg hgood hwin hdistC hdistW _κ _Aκ hκ _r _ρV
    hρV hroom hdistσ hκR hclosG hslabsLoc hbcadC hclock hsmall hhalf ha₀ hDmX hT₀X
    hRa hsepX hfinX hsel
  subst hKh
  have hev := RetainedCoreHistory.eventInterior_data_P6X σ y hpos
  obtain ⟨j, yG, hjt, htj, hyG, hsc⟩ := hev
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans (hsc n)
  exact false_of_selection_eventSlab_lateHI_closed_noJ10_dec_P6KT
    hWBloc hη hε hεW hεX hεN hεcone hC1 hC2 hCt hC2' hphi (K := K) (t := fun n => (σ n : ℝ)) hjt
    htj (recordsK := recordsK)
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK
    (fun n => hnotKs n (j n) (yG n) (hyG n) (hjt n) (htj n)) _ rfl σ y R (fun _ => rfl) hyG hRn
    hRpos hRlt hκd hvolK haP hpinL hT₀ Tn aSeed haT hsT has hTnK pT seedTrace L hL Cg hCg hgood hwin
    hdistC hdistW (hslabsLoc j yG hjt htj hyG) (hbcadC hκ hρV hroom hdistσ hκR hclosG)
    hclock hsmall hhalf ha₀ hDmX hT₀X hRa hsepX hfinX hsel

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
