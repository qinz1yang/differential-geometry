import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedHICondKappaP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRoutePrefixFullP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HctrlNoJ10P6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationP6HP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTransportC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixHdistC11G2

/-!
# J10KERNEL G1：closed-kappa kernel 的 prefix 环 + hctrl 环无 J10 形（O-CH11-J10KERNEL，`_P6JK2`）

`false_of_selection_eventSlab_lateHI_closed_cond_kappaOnly_P6CK`（P6ClosedHICondKappaP6CK:35）的
**rings 孪生**：删 `hqR`（J10，`max (n+1) Q < R`），prefix 环换 J10GEN2A
`false_of_selection_eventSlab_lateHI_prefix_full_P6JA`，hctrl 环换 `exists_hctrl_lateHI_noJ10_P6JA`；
anchor 环与 slice 环**不在本文件**：其结论 `hanchor0` / `hbcadC` 作为环结论槽（prefix_full binder 逐字），
owner 分别为 SLTLOCAL `hanchor0_eventSlab_local_P6SL`[hWBloc→WBADAPT, hslabsLoc→SLTPROD] 与
SLTPROD G2（slice (i)）+ birth (ii) 合同行。因此 closed-kappa 中只服务 anchor / slice 的 binder
（`hCg`、`hdistW`、`κ Aκ hκ r ρV hρV hroom hdistσ hκR hclosG`、`ε ≤ coneAccuracy`）在本孪生里删去。

E 帧 (B) 族全部由 **K 层行**付（逐项）：
* seed：`hclock hsmall hhalf`（hgapJ 合同形，`r = 1`）⇒ J10GEN2A G5
  `exists_seedSeq_hsmall_eventPrefix_P6JA`；
* `hpinX` ⇐ `ha₀ : 0 < a₀ n` + HIPROP `hiActive_of_records_P6HP` +
  C11G2 `inFixedHI_eventPrefix_C11G2`；
* records-X ⇐ `recordsK` 限制（C11G2 `eventPrefixRecords_C11G2`，`qX := p`、`T₀X := T₀`）；`hOldX` = `rfl`
  （RetainedCoreHistory 的 event `old` 定义即 retained core）；`hcanX` ⇐ `hcanK`；`haccX` = `hacc`；
  `hmX` ⇐ `hord`；`hDmX` = 行（K 层 `p`）；E 层 `hT₀X` ⇐ 行 `hT₀X : T₀ ≤ aSeed` + G5 `aSeed ≤ aE`；
* `hsepX` ⇐ K 层行 `hsepX`（J10GEN3 G2 `hsepX_of_paramCompat_P6JG3` 在 `Hs := K` 的输出形）；
* `hRa` ⇐ 合同行 `1 ≤ aSeed` + `hRlt`；`hfinX` ⇐ K 层行 `hfinX`（C11G2 `edist_eventPrefix_C11G2`
  + G5 seed 兼容）。
生成器 `build-logs/scratch/O-CH11-J10KERNEL/gen/gen1.py`（closed-kappa 陈述切片 + assert 删项）。
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

namespace ObservedHistory

/-- **G1（`_P6JK2`，PROVISIONAL[anchor 结论槽 `hanchor0`、slice 结论槽 `hbcadC`、(B) K 层行
`hclock hsmall hhalf ha₀ hDmX hT₀X hRa hsepX hfinX`]）**：closed-kappa kernel 的 rings 孪生——
prefix 环 + hctrl 环无 J10（无 `hqR` / `Q < R`），结论逐字（`False`）。 -/
theorem false_of_selection_eventSlab_lateHI_closed_rings_noJ10_P6JK2 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
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
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
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
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_lateHI_prefix_full_P6JA.{u}
  refine ⟨epsW, hepsW, fun ε hε h11 hεW hεX hεN => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε h11 hεW hεX hεN
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K j t hjt htj Q T₀ p pF recordsK recordsF yG a₀ hHI hcanK hδF hacc hrad
    hord hscaleK hbirthA hpinchK0 hslabK hnotK Kh hKh σ y R hσ hyG hRn hRpos hRlt κd hκd hvolK aP
    haP hpinL hT₀ Tn aSeed haT hsT has pT seedTrace L hL Cg hgood hwin hdistC hanchor0 hbcadC
    hclock hsmall hhalf ha₀ hDmX hT₀X hRa hsepX hfinX hsel
  have hC2' : 0 ≤ C2' := by linarith
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
  have hslab' : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount) :=
    fun n => RetainedCoreHistory.eventSlabsDerivative_mono_P6D (hslabK n) (hQq n)
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
    have h := hslab' n (j n) (Fin.castSucc_lt_last _) x v ⟨hv.1, hv.2.trans (htj n)⟩ hlt
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
      (fun i _ => hslab' n i (Fin.castSucc_lt_last i))
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
  exact hB' hC1 hC2 hCt hphi hjt htj
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

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
