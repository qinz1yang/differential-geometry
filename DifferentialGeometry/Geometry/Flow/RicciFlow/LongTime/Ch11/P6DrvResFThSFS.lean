import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResFThDefFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvHIDHTHFT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvHIDHTCgHFT

/-!
# FSUP G1：过渡形 ThS ⇒ `DrvResF_DT`（HI / κ / pinching 族桥内付，`_FS`）

`drvResF_DT_of_ThS_FS` / `drvResF_DT_Cg_of_ThS_FS`：F 线的 E3 桥。结论 `DrvResF_DT` /
`DrvResF_DT_Cg_DF`（final 帧 driver 剩余输入核，38 项），前提 `DrvResF_DT_ThS_FS`（records 族 +
`Cst hsurv hext` + `hscaleK hbirthA` + θ₀ 尾）。`r₀ w hseed Phi hPhi hpinch κU phi a₀K hHI hδF
hpinchK0 hpinchF hκR hκRF hpinchK0′ hpinchF′` 由桥内付：`hpinch_of_initial_P6HP`（同一 Phi，event /
final 常值族）、`hanchor0_hPN_frame_final_RU`（final anchor，`hevF`）、`hkappaC_driver_of_drv_J11S`
（`hσH` ⇐ `hevF.2`）、FRESH 逐 n 窗口 `hκR_K_DH` / `hκRF_K_DH`；证明体 = `hDext_of_drvRes3_DT_HFT`
（E3）与 `hDextJF_of_drvResF_DT`（F 桥）逐段拼接（`j` 换 `hevF`，records 域 T₀K 抬到 `T₁`）。
PROVED 相对引擎级前提 `hfresh / records / hfine / hder / hanti / ha₀ / hHI0 / hT₀δ`；无新 binder。
生成器 `build-logs/scratch/O-CH11-FSUP/gen/g1_bridge.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

theorem drvResF_DT_of_ThS_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (hres : DrvResF_DT_ThS_FS F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvResF_DT F q records ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hevF hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, Cst, hsurv, hext, hscaleK,
    hbirthA, θ₀, hθ₀, hsepρ⟩ :=
    hres A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hevF hlt
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k => (hevF k).2
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hevF n).1.trans (hevF n).2
  -- Q 统一（§0.4）：hslabK / hderF 截断于 Tn，由 TDS 先验在原尺度天花板 Tno = c·Tn 处付
  obtain ⟨hslab0, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime
        ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
        (min ((K n).time j₀.succ) (Tn n : ℝ)) := fun n j₀ => by
    have h := hslab0 n j₀
    beta_reduce at h
    rwa [hQe n, hTc n] at h
  have hderF : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n => by
    have h := hderF0 n (hfin n)
    beta_reduce at h
    rw [hQe n, hTc n] at h
    exact h
  -- T₁ := max (max 1 (T₀/c)) T₀K：records 定义域限制，使 1 ≤ T₁ 且 δ 阈值过
  obtain ⟨T₁, hT₁a, hT₁b, hT₁c, hT₁ev⟩ : ∃ T₁ : ℕ → ℝ, (∀ n, 1 ≤ T₁ n) ∧
      (∀ n, T₀ n / c n ≤ T₁ n) ∧ (∀ n, T₀K n ≤ T₁ n) ∧
      ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₁ n ≤ (σ n : ℝ) - T / R n := by
    refine ⟨fun n => max (max 1 (T₀ n / c n)) (T₀K n),
      fun n => (le_max_left _ _).trans (le_max_left _ _),
      fun n => (le_max_right _ _).trans (le_max_left _ _), fun n => le_max_right _ _, ?_⟩
    intro T hT
    filter_upwards [hT₀K T hT, hwin T hT] with n hn1 hn2
    refine max_le (max_le ?_ ?_) hn1
    · linarith [h1 n]
    · have : T₀ n / c n ≤ (aSeed n : ℝ) := (div_le_iff₀ (hc n)).2 (by rw [mul_comm]; exact hlate n)
      linarith
  let recK' : ∀ n (i : Fin (K n).eventCount), T₁ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n) :=
    fun n i hi => recK n i ((hT₁c n).trans hi)
  have hsep' : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₁ n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recK' n i hi).static b).neck.scale :=
    fun T hT C hC => (hsep T hT C hC).mono fun n hn i hi b hlt => hn i ((hT₁c n).trans hi) b hlt
  have hcanK' : ∀ n i hi b, ((recK' n i hi).static b).hasCanonicalWindow :=
    fun n i hi b => hcanK n i _ b
  have hscaleK' : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recK' n i hi).static b).neck.scale := fun n i hi b => hscaleK n i _ b
  have hbirthA' : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ / c n * ((recK' n i hi).static b).neck.scale :=
    hbirthA.mono fun n hn i hi b => hn i _ b
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3 + 7) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep0 := fun k => ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k)
    hA0 (Tno k).2.1 (h2r k) (hvolo k) (hR1 k) (hRρ k)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hkN
    have h1' : (N : ℝ) ≤ k := by exact_mod_cast hkN
    exact (ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
      (by linarith [hk k]) (h2r k) (hvolo k) (hR1 k) (hRρ k)).1
  -- 同一个 Phi：HI、pinching（event / final）
  have ha₀K : ∀ n, 0 < a₀ / c n := fun n => div_pos ha₀ (hc n)
  have hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ / c n) x ∧
      -3 / (a₀ / c n) ≤ metricScalarAt ((K n).initialMetric 0) x :=
    fun n => (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (hHI0 (ind n))
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)
  have hP1 := hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₁ ha₀K
    (fun n => by have := hT₁a n; have := (ha₀K n).le; linarith) hHIK
  have hpinchK0 := hP1.1
  have hGinit : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n =>
    (K n).toHistory.final_initial (hfin n)
  have hpinchF : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₁ n)) Phi :=
    fun n => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => T₁ n) (fun _ => ha₀K n)
      (fun _ => by have := hT₁a n; have := (ha₀K n).le; linarith) (fun _ => hHIK n)).2
      (fun _ => (K n).horizon) (fun _ => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl
        (hfin n) le_rfl) (fun _ => hGinit n) 0
  have hTn2 : ∀ n, 1 ≤ a₀ / c n + ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) := fun n => by
    have h2 := (hprep0 n).2.1
    have h3 := (ha₀K n).le
    norm_num at h2 ⊢
    linarith
  have hpinchK0' : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) Phi :=
    (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n)
      (fun n => (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) ha₀K hTn2 hHIK).1
  have hpinchF' : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) Phi :=
    fun n => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) (fun _ => ha₀K n)
      (fun _ => hTn2 n) (fun _ => hHIK n)).2
      (fun _ => (K n).horizon) (fun _ => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl
        (hfin n) le_rfl) (fun _ => hGinit n) 0
  have hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))) := by
    intro D T _ hT
    filter_upwards [hT₁ev T hT] with n hn x _ v hvt hv tr
    have hvh : (v : ℝ) < (K n).horizon := lt_of_le_of_lt hvt (hσH n)
    exact ObservedHistory.curvatureOperatorLowerBoundAt_stage_of_pinched_HF (K n) (hpinchK0 n)
      (fun _ => hpinchF n) v (hn.trans hv) hvh _
  -- hanchor0 ⇐ G9SHIFT final（FRESH 经 rescale adapter）
  have hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory := by
    intro Aseed hAs
    obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (Aseed + 7) (by linarith)
    exact ⟨κ, hκ, Tf, GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup⟩
  have hanc := hanchor0_hPN_frame_final_RU
    hεle hC2 hanti hder T₀ hsupA hPhi hθ₀ records hfine hA ind Tno pTo r hr hk h2r hsmo hvolo
    aSeed haT hclock h1 hsm hlate seedTrace σ y R hsT has L hRdef hRpos hRr hL hgood hwin hwin'
    hRρ hball hdistσ hpinchK0' (fun k => (hevF k).1) (fun k => (hevF k).2) hpinchF' hsepρ
  -- hkappaC ⇐ J11STAY（Aseed := A + 3）
  have hdσ' : ∀ᶠ k in atTop,
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3 + 3) * 1) :=
    hdistσ.mono fun k hk => hk.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hkap := ObservedHistory.hkappaC_driver_of_drv_J11S (Cg := 4) (haT := haT) hC2 K hclock h1
    hsm seedTrace σ y R hsT has L hRpos hRr hL hgood hσH
    (fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
    qK T₁ recK' hsep' hT₁ev hcanK' hacc hrad hord (by linarith : (0 : ℝ) < A + 3)
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => by simpa using (hprep0 k).2.1) (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2)
    hwin hwin' hdσ'
  -- hseed ⇐ hsurvive（A = 2·1，小 T）+ hanchor0 + hkappaC
  obtain ⟨Qa, hQa2, hQaev⟩ := hanc (2 * 1) (by norm_num)
  have hCst0 : (0 : ℝ) ≤ (Cst : ℝ) := NNReal.coe_nonneg Cst
  have hden : 0 < 4 * (Cst : ℝ) * Qa + 1 := by
    have := mul_nonneg hCst0 (by linarith : (0 : ℝ) ≤ Qa)
    linarith
  have hT0pos : 0 < 1 / (4 * (Cst : ℝ) * Qa + 1) := by positivity
  have hT04 : 4 * (Cst : ℝ) * Qa * (1 / (4 * (Cst : ℝ) * Qa + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨K1, hK1, hev1⟩ := hsurv (2 * 1) (1 / (4 * (Cst : ℝ) * Qa + 1)) Qa (by norm_num) hT0pos
    hQa2 hT04
  have hTR1 : ∀ᶠ n in atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * 1 / Real.sqrt (R n))
      ((1 / (4 * (Cst : ℝ) * Qa + 1)) / R n) (K1 * R n) :=
    (hev1.and hQaev).mono fun n hn => hn.1 hn.2
  have hkap1 := hkap id strictMono_id 1 (1 / (4 * (Cst : ℝ) * Qa + 1)) K1 one_pos hT0pos hK1
    (by rw [Filter.map_id]; exact hTR1)
  rw [Filter.map_id] at hkap1
  have hr₀pos : 0 < min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) :=
    lt_min (lt_min one_pos hT0pos) (by positivity)
  have hr₀1 : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hr₀T : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤
      1 / (4 * (Cst : ℝ) * Qa + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hr₀K : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) * (K1 + 1) ≤ 1 := by
    have h := min_le_right (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1))
    have hK1' : 0 < K1 + 1 := by linarith
    calc _ ≤ 1 / (K1 + 1) * (K1 + 1) := mul_le_mul_of_nonneg_right h hK1'.le
      _ = 1 := by field_simp
  have hctrl := hTR1.mono fun n hn => ObservedHistory.controlled_of_traced_DH (Kh n) (σ n) (y n)
    (hRpos n) hK1 hr₀pos hr₀1 hr₀T hr₀K hn
  have hseed := ObservedHistory.hseed_of_tracedKappa_smallT_DH hRpos (fun _ : ℕ => (1 : ℝ) / 200)
    hradii hT0pos hkap1 hr₀pos hctrl
  -- hκR / hκRF ⇐ 逐 n FRESH 窗口
  have hvolW : ∀ k, ENNReal.ofReal ((A + 3 + 7)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 :=
    fun k => le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (inv_anti₀ (by linarith) (by linarith)) (by norm_num))) (hprep0 k).2.2.1
  have hκR := ObservedHistory.hκR_K_DH Kh hκ.le (by linarith : A + 3 ≤ A + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) hsupK Tn aSeed haT pT
    seedTrace (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by simpa using (hprep0 k).2.1) hsm
    hvolW hclock (fun _ => by norm_num) (fun k w h1 h2 => (hprep0 k).2.2.2 w h1 h2)
  have hκRF := ObservedHistory.hκRF_K_DH Kh hκ.le (by linarith : A + 3 ≤ A + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) hsupK Tn aSeed haT pT
    seedTrace (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by simpa using (hprep0 k).2.1) hsm
    hvolW hclock (fun _ => by norm_num) (fun k w h1 h2 => (hprep0 k).2.2.2 w h1 h2)
  have hδF' : ∀ n (i : Fin (K n).eventCount), T₁ n ≤ (K n).time i.succ →
      (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1) :=
    fun n i hi => RetainedCoreHistory.hδF_rescale_P6X3 (F.tower.history (ind n)) (hc n)
      (fun i' hi' => hT₀δ n _ hi') i (max_le (hT₁a n) (hT₁b n) |>.trans hi)
  exact ⟨qK, T₁, recK', hsep', hT₁ev, hcanK', hacc, hrad, hord, Cst, hsurv, hext,
    _, _, hr₀pos, hκ, hseed, Phi, hPhi, hpinch, κ, Phi, hκ, hPhi, fun n => a₀ / c n, hHIK, hδF',
    hscaleK', hbirthA', hpinchK0, hpinchF, hκR, hκRF, hpinchK0', hpinchF', θ₀, hθ₀, hsepρ⟩


theorem drvResF_DT_Cg_of_ThS_FS {Cg : ℝ} (hCg : 4 ≤ Cg)
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (hres : DrvResF_DT_Cg_ThS_FS F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀) :
    DrvResF_DT_Cg_DF F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hevF hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, Cst, hsurv, hext, hscaleK,
    hbirthA, θ₀, hθ₀, hsepρ⟩ :=
    hres A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hevF hlt
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k => (hevF k).2
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hevF n).1.trans (hevF n).2
  -- Q 统一（§0.4）：hslabK / hderF 截断于 Tn，由 TDS 先验在原尺度天花板 Tno = c·Tn 处付
  obtain ⟨hslab0, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime
        ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
        (min ((K n).time j₀.succ) (Tn n : ℝ)) := fun n j₀ => by
    have h := hslab0 n j₀
    beta_reduce at h
    rwa [hQe n, hTc n] at h
  have hderF : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n => by
    have h := hderF0 n (hfin n)
    beta_reduce at h
    rw [hQe n, hTc n] at h
    exact h
  -- T₁ := max (max 1 (T₀/c)) T₀K：records 定义域限制，使 1 ≤ T₁ 且 δ 阈值过
  obtain ⟨T₁, hT₁a, hT₁b, hT₁c, hT₁ev⟩ : ∃ T₁ : ℕ → ℝ, (∀ n, 1 ≤ T₁ n) ∧
      (∀ n, T₀ n / c n ≤ T₁ n) ∧ (∀ n, T₀K n ≤ T₁ n) ∧
      ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₁ n ≤ (σ n : ℝ) - T / R n := by
    refine ⟨fun n => max (max 1 (T₀ n / c n)) (T₀K n),
      fun n => (le_max_left _ _).trans (le_max_left _ _),
      fun n => (le_max_right _ _).trans (le_max_left _ _), fun n => le_max_right _ _, ?_⟩
    intro T hT
    filter_upwards [hT₀K T hT, hwin T hT] with n hn1 hn2
    refine max_le (max_le ?_ ?_) hn1
    · linarith [h1 n]
    · have : T₀ n / c n ≤ (aSeed n : ℝ) := (div_le_iff₀ (hc n)).2 (by rw [mul_comm]; exact hlate n)
      linarith
  let recK' : ∀ n (i : Fin (K n).eventCount), T₁ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n) :=
    fun n i hi => recK n i ((hT₁c n).trans hi)
  have hsep' : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₁ n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recK' n i hi).static b).neck.scale :=
    fun T hT C hC => (hsep T hT C hC).mono fun n hn i hi b hlt => hn i ((hT₁c n).trans hi) b hlt
  have hcanK' : ∀ n i hi b, ((recK' n i hi).static b).hasCanonicalWindow :=
    fun n i hi b => hcanK n i _ b
  have hscaleK' : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recK' n i hi).static b).neck.scale := fun n i hi b => hscaleK n i _ b
  have hbirthA' : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ / c n * ((recK' n i hi).static b).neck.scale :=
    hbirthA.mono fun n hn i hi b => hn i _ b
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3 + 7) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hprep0 := fun k => ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k)
    hA0 (Tno k).2.1 (h2r k) (hvolo k) (hR1 k) (hRρ k)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hkN
    have h1' : (N : ℝ) ≤ k := by exact_mod_cast hkN
    exact (ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
      (by linarith [hk k]) (h2r k) (hvolo k) (hR1 k) (hRρ k)).1
  -- 同一个 Phi：HI、pinching（event / final）
  have ha₀K : ∀ n, 0 < a₀ / c n := fun n => div_pos ha₀ (hc n)
  have hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ / c n) x ∧
      -3 / (a₀ / c n) ≤ metricScalarAt ((K n).initialMetric 0) x :=
    fun n => (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (hHI0 (ind n))
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)
  have hP1 := hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₁ ha₀K
    (fun n => by have := hT₁a n; have := (ha₀K n).le; linarith) hHIK
  have hpinchK0 := hP1.1
  have hGinit : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n =>
    (K n).toHistory.final_initial (hfin n)
  have hpinchF : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₁ n)) Phi :=
    fun n => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => T₁ n) (fun _ => ha₀K n)
      (fun _ => by have := hT₁a n; have := (ha₀K n).le; linarith) (fun _ => hHIK n)).2
      (fun _ => (K n).horizon) (fun _ => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl
        (hfin n) le_rfl) (fun _ => hGinit n) 0
  have hTn2 : ∀ n, 1 ≤ a₀ / c n + ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) := fun n => by
    have h2 := (hprep0 n).2.1
    have h3 := (ha₀K n).le
    norm_num at h2 ⊢
    linarith
  have hpinchK0' : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) Phi :=
    (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n)
      (fun n => (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) ha₀K hTn2 hHIK).1
  have hpinchF' : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) Phi :=
    fun n => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2) (fun _ => ha₀K n)
      (fun _ => hTn2 n) (fun _ => hHIK n)).2
      (fun _ => (K n).horizon) (fun _ => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl
        (hfin n) le_rfl) (fun _ => hGinit n) 0
  have hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))) := by
    intro D T _ hT
    filter_upwards [hT₁ev T hT] with n hn x _ v hvt hv tr
    have hvh : (v : ℝ) < (K n).horizon := lt_of_le_of_lt hvt (hσH n)
    exact ObservedHistory.curvatureOperatorLowerBoundAt_stage_of_pinched_HF (K n) (hpinchK0 n)
      (fun _ => hpinchF n) v (hn.trans hv) hvh _
  -- hanchor0 ⇐ G9SHIFT final（FRESH 经 rescale adapter）
  have hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory := by
    intro Aseed hAs
    obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (Aseed + 7) (by linarith)
    exact ⟨κ, hκ, Tf, GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup⟩
  have hanc := hanchor0_hPN_frame_final_RU_Cg_DF (by linarith)
    hεle hC2 hanti hder T₀ hsupA hPhi hθ₀ records hfine hA ind Tno pTo r hr hk h2r hsmo hvolo
    aSeed haT hclock h1 hsm hlate seedTrace σ y R hsT has L hRdef hRpos hRr hL hgood hwin hwin'
    hRρ hball hdistσ hpinchK0' (fun k => (hevF k).1) (fun k => (hevF k).2) hpinchF' hsepρ
  -- hkappaC ⇐ J11STAY（Aseed := A + 3）
  have hdσ' : ∀ᶠ k in atTop,
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3 + 3) * 1) :=
    hdistσ.mono fun k hk => hk.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hkap := ObservedHistory.hkappaC_driver_of_drv_J11S (Cg := Cg) (haT := haT) hC2 K hclock h1
    hsm seedTrace σ y R hsT has L hRpos hRr hL hgood hσH
    (fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
    qK T₁ recK' hsep' hT₁ev hcanK' hacc hrad hord (by linarith : (0 : ℝ) < A + 3)
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => by simpa using (hprep0 k).2.1) (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2)
    hwin hwin' hdσ'
  -- hseed ⇐ hsurvive（A = 2·1，小 T）+ hanchor0 + hkappaC
  obtain ⟨Qa, hQa2, hQaev⟩ := hanc (2 * 1) (by norm_num)
  have hCst0 : (0 : ℝ) ≤ (Cst : ℝ) := NNReal.coe_nonneg Cst
  have hden : 0 < 4 * (Cst : ℝ) * Qa + 1 := by
    have := mul_nonneg hCst0 (by linarith : (0 : ℝ) ≤ Qa)
    linarith
  have hT0pos : 0 < 1 / (4 * (Cst : ℝ) * Qa + 1) := by positivity
  have hT04 : 4 * (Cst : ℝ) * Qa * (1 / (4 * (Cst : ℝ) * Qa + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨K1, hK1, hev1⟩ := hsurv (2 * 1) (1 / (4 * (Cst : ℝ) * Qa + 1)) Qa (by norm_num) hT0pos
    hQa2 hT04
  have hTR1 : ∀ᶠ n in atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * 1 / Real.sqrt (R n))
      ((1 / (4 * (Cst : ℝ) * Qa + 1)) / R n) (K1 * R n) :=
    (hev1.and hQaev).mono fun n hn => hn.1 hn.2
  have hkap1 := hkap id strictMono_id 1 (1 / (4 * (Cst : ℝ) * Qa + 1)) K1 one_pos hT0pos hK1
    (by rw [Filter.map_id]; exact hTR1)
  rw [Filter.map_id] at hkap1
  have hr₀pos : 0 < min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) :=
    lt_min (lt_min one_pos hT0pos) (by positivity)
  have hr₀1 : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hr₀T : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤
      1 / (4 * (Cst : ℝ) * Qa + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hr₀K : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) * (K1 + 1) ≤ 1 := by
    have h := min_le_right (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1))
    have hK1' : 0 < K1 + 1 := by linarith
    calc _ ≤ 1 / (K1 + 1) * (K1 + 1) := mul_le_mul_of_nonneg_right h hK1'.le
      _ = 1 := by field_simp
  have hctrl := hTR1.mono fun n hn => ObservedHistory.controlled_of_traced_DH (Kh n) (σ n) (y n)
    (hRpos n) hK1 hr₀pos hr₀1 hr₀T hr₀K hn
  have hseed := ObservedHistory.hseed_of_tracedKappa_smallT_DH hRpos (fun _ : ℕ => (1 : ℝ) / 200)
    hradii hT0pos hkap1 hr₀pos hctrl
  -- hκR / hκRF ⇐ 逐 n FRESH 窗口
  have hvolW : ∀ k, ENNReal.ofReal ((A + 3 + 7)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 :=
    fun k => le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (inv_anti₀ (by linarith) (by linarith)) (by norm_num))) (hprep0 k).2.2.1
  have hκR := ObservedHistory.hκR_K_DH Kh hκ.le (by linarith : A + 3 ≤ A + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) hsupK Tn aSeed haT pT
    seedTrace (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by simpa using (hprep0 k).2.1) hsm
    hvolW hclock (fun _ => by norm_num) (fun k w h1 h2 => (hprep0 k).2.2.2 w h1 h2)
  have hκRF := ObservedHistory.hκRF_K_DH Kh hκ.le (by linarith : A + 3 ≤ A + 3 + 7)
    (nr := fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) hsupK Tn aSeed haT pT
    seedTrace (fun _ => 1) (fun _ => 1 / 200) hTf (fun k => by simpa using (hprep0 k).2.1) hsm
    hvolW hclock (fun _ => by norm_num) (fun k w h1 h2 => (hprep0 k).2.2.2 w h1 h2)
  have hδF' : ∀ n (i : Fin (K n).eventCount), T₁ n ≤ (K n).time i.succ →
      (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1) :=
    fun n i hi => RetainedCoreHistory.hδF_rescale_P6X3 (F.tower.history (ind n)) (hc n)
      (fun i' hi' => hT₀δ n _ hi') i (max_le (hT₁a n) (hT₁b n) |>.trans hi)
  exact ⟨qK, T₁, recK', hsep', hT₁ev, hcanK', hacc, hrad, hord, Cst, hsurv, hext,
    _, _, hr₀pos, hκ, hseed, Phi, hPhi, hpinch, κ, Phi, hκ, hPhi, fun n => a₀ / c n, hHIK, hδF',
    hscaleK', hbirthA', hpinchK0, hpinchF, hκR, hκRF, hpinchK0', hpinchF', θ₀, hθ₀, hsepρ⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
