import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalSupplyFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnrTupleFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResFThSFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResE4ThMJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagDTRXHND

/-!
# FSUP W3：F 线引擎供给——`DrvResF_DT_ThS_FS` 与 `DrvResF_DT` 由 SCRS⁺ 实际 records 上的引擎数据直接生产

`drvResF_ThS_of_engine_FS` / `drvResF_DT_Cg_ThS_of_engine_FS`：不带任何核假设，在**实际 records**
（`hrcs` 随带）上证出 `DrvResF_DT_ThS_FS`（records 族、`∃ Cst, hsurv ∧ hext`、`hscaleK hbirthA`、θ₀ 尾）：
* records 族 / `hscaleK hbirthA` ⇐ T0K 供给 `drvResE_records_of_engine_T0K`（`T₀K := aSeed`，j 无关），元组由
  `(ε, Ctime)` 定出（`hnotPackExF_FS`，final hnot 的 `Cb Rn ζ δ₀ m₀`）；
* `Cst hsurv hext` ⇐ `finalSurvExt_of_engine_FS`（final 帧 J10 供给 + `hnotK_final_cww`）；
* θ₀ 尾 ⇐ `birthN_aSeed_T0K`（`θ₀ := 1`，同 `drvResE4_DT_Th_of_engine_MJ`；析取前提不用）。
`hsep / hscale / θ₀ 尾` 比 Perelman 字面 `h ≤ δ²r` 强（要和后来时刻 `Tn` 的 ρ 比），但由 haccuracy 合同
（C12-7′c builder cap `δ(u)²ρ(u) < ρ(2u)/(u+1)`）经 recent birth（`RecentCutoffSupply_C11S`）导出，不是独立假设。
合成 `drvResF_DT_of_engine_FS` / `drvResF_DT_Cg_of_engine_FS` 与消费结论 `hDextJF_of_engine_FS` /
`hDextJF8_of_engine_FS` 在 `P6HgwResJFEngFS`。无新 binder / Prop。
生成器 `build-logs/scratch/O-CH11-FSUP/gen/g3_eng.py`。
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

theorem drvResF_ThS_of_engine_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hC1 : GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C1) (hC2' : GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C2)
    (hCt : GC.LongTime.Ch11.ctHN_CH2.{u} ε ≤ Ctime) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hδq : Tendsto q.delta atTop (𝓝 0))
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
    (hT : ∀ n, thetaF_FS.{u} records hrcs hanti hδq hfine ha₀ hHI0 hε hε' Ctime n ≤ T₀ n)
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    DrvResF_DT_ThS_FS F q records ε C1 C2 Ctime T₀ Qt a₀ := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hevF hlt
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hevF n).1.trans (hevF n).2
  -- Icc → 数值
  have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
    have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
    rw [this]; field_simp [(hc k).ne']
  have hTno0 : ∀ k, 0 ≤ (Tno k : ℝ) := fun k => (Tno k).2.1
  have h2c : ∀ k, 2 * c k < (Tno k : ℝ) := fun k => h2r k
  have hρK : ∀ k, ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ =
      c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [hTno k]; exact RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q (Tn k : ℝ)
  have hRρ' : ∀ k, R k ≤ c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [← hρK k]; exact hRρ k
  -- 单一元组与供给
  have hspec := hnotPackF_spec_FS.{u} hε hε' Ctime
  have hspec5 := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackExF_FS.{u} hε hε' Ctime)))))
  obtain ⟨-, -, -, -, -, -, -, -, hprod⟩ := hspec5
  have hsup := Classical.choose_spec (drvResE_records_of_engine_T0K records hrcs hanti hδq hfine
    ha₀ hHI0 (hnotNfF_FS.{u} hε hε' Ctime) (hnotζF_FS.{u} hε hε' Ctime)
    (hnotRnF_FS.{u} hε hε' Ctime) (hnotδF_FS.{u} hε hε' Ctime)
    (hnotmF_FS.{u} hε hε' Ctime)
    hspec.2.1 hspec.2.2.2.2.2.1) T₀ hT ind c (fun k => (σ k : ℝ)) L R (fun k => (Tn k : ℝ))
    (fun k => (Tno k : ℝ)) (fun k => (aSeed k : ℝ)) hc hTno hTno0 h2c hclock h1 hlate hroom hRr
    hRρ' hwin
  obtain ⟨p, recKHo, haccK, hradK, hordK, hcanH, hδK, hbirthK, hbirthAK, hHIK, hT0X, htail⟩ := hsup
  let qK : ℕ → CutoffParameters := fun n => (p n).rescale_P6N (c n) (hc n)
  let T₀K : ℕ → ℝ := fun n => max 1 (c n * (aSeed n : ℝ) / c n)
  let recK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n) :=
    fun n i hi => (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi
  have hcanK : ∀ n i hi b, ((recK n i hi).static b).hasCanonicalWindow :=
    fun n i hi b => (F.tower.history (ind n)).hcanK_rescale_P6X3 (hc n) (recKHo n) (hcanH n)
      i hi b
  have ha₀K : ∀ n, 0 < a₀ / c n := fun n => div_pos ha₀ (hc n)
  have hslabK := hslabK_of_tds_HND hanti hder ind c hc (fun n => (Tn n : ℝ))
  obtain ⟨-, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hderF : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n => by
    have h := hderF0 n (hfin n)
    beta_reduce at h
    rw [hQe n, hTc n] at h
    exact h
  have hQp : ∀ n : ℕ,
      0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    inv_pos.mpr (pow_pos ((q.rescale_P6N (c n) (hc n)).neckRadius_pos _ (Tn n).2.1) 2)
  have hn1 : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) + 1 := fun n => by positivity
  have hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recK n i hi).static b).neck.scale := fun n i hi b =>
    (mul_le_mul_of_nonneg_right (le_max_left _ _)
      ((hn1 n).trans (le_max_left _ _))).trans (hbirthK n i hi b)
  have hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ / c n * ((recK n i hi).static b).neck.scale :=
    Filter.Eventually.of_forall fun n i hi b => hbirthAK n i hi b
  have hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) := fun n =>
    (haccK n).trans (hspec.2.2.1 n)
  have hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius := fun n =>
    (hspec.2.2.2.1 n).trans (hradK n)
  have hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder := fun n =>
    (hspec.2.2.2.2.2.2.2 n).trans (hordK n)
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)
  have hT₀K1 : ∀ n, 1 ≤ a₀ / c n + T₀K n := fun n => by
    have := le_max_left 1 (c n * (aSeed n : ℝ) / c n)
    have := ha₀K n
    change (1 : ℝ) ≤ a₀ / c n + max 1 (c n * (aSeed n : ℝ) / c n)
    linarith
  have hpinchK := (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₀K
    ha₀K hT₀K1 hHIK).1
  have hGinit : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n =>
    (K n).toHistory.final_initial (hfin n)
  have hpinchF : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) Phi :=
    fun n => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => T₀K n) (fun _ => ha₀K n) (fun _ => hT₀K1 n)
      (fun _ => hHIK n)).2
      (fun _ => (K n).horizon) (fun _ => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl
        (hfin n) le_rfl) (fun _ => hGinit n) 0
  have hhalf := ObservedHistory.hhalf_of_room_one_A6K σ Tn R L hRpos hroom
  have hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n))
      ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
        ((K n).toHistory.activeStage_mono (has n)) ((K n).toHistory.activeStage_mono (hsT n)))
      (y n) ≠ ⊤ := fun n => ne_top_of_lt (hball n)
  have hsepK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          ((recK n i hi).static b).neck.scale := by
    intro T _ C hC
    filter_upwards [two_max_lt_birth_MJ hRr hC] with n hn i hi b _
    refine hn.trans_le (le_trans ?_ (hbirthK n i hi b))
    exact mul_le_mul (le_max_left _ _) ((hRρ n).trans (le_max_right _ _)) (hRpos n).le
      ((hn1 n).trans (le_max_left _ _))
  obtain ⟨Cst, hsurv, hext⟩ := ObservedHistory.finalSurvExt_of_engine_FS (Cg := 4) (ε := ε)
    (C1 := C1) (C2 := C2) (Ctime := Ctime) (phi := Phi) (Q := fun n =>
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (a₀K := fun n => a₀ / c n)
    (qK := qK) (T₀K := T₀K) (recordsK := recK) (pF := fun n => q.rescale_P6N (c n) (hc n))
    hevF hC2 hcanK hacc hrad hord htail hT0X hsepK (fun n i => hrecF n i)
    (fun n i hi => (hδK n i hi).trans (hspec.2.2.2.2.2.2.1 n)) hPhi ha₀K hHIK hscale
    (Filter.Eventually.of_forall fun n i hi b => hbirthAK n i hi b) hpinchK hpinchF Tn aSeed
    haT hsT has pT seedTrace (fun n i => hslabK n i) hderF hclock h1 hsm hhalf hL hgood hRdef
    hRpos hRr hfinK
    (fun n => by
      have h11 := (hspec.2.2.2.2.1 n).trans (hradK n)
      change StandardCap.transitionEnd + 10 < (p n).modelRadius
      linarith)
    (fun n yG' hyG => hprod hC1 hC2' hCt σ y hevF
      (fun k => Subtype.coe_le_coe.mpr (hsT k)) (Q := fun n =>
        ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (T₀ := T₀K) (p := qK)
      (pF := fun n => q.rescale_P6N (c n) (hc n)) (recordsK := recK) hrecF
      (a₀ := fun n => a₀ / c n) hHIK hcanK (fun n i hi => hδK n i hi) haccK hradK hordK hQp
      (fun n j => hslabK n j) (fun n _ => hderF n)
      (fun n i hi b => (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQp n).le
        ((hn1 n).trans (le_max_left _ _))).trans (hbirthK n i hi b))
      (fun n i hi b => hbirthAK n i hi b) hsel n yG' hyG)
  refine ⟨qK, T₀K, recK, hsepK, htail, hcanK, hacc, hrad, hord, Cst, hsurv, hext, hscale,
    hbirthA, 1, one_pos, ?_⟩
  intro B hB
  refine Filter.Eventually.of_forall ?_
  intro n i hi b _ _
  have hcn := hc n
  have hR' : R n ≤ c n * (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := hRρ' n
  have habs : ((n : ℝ) + 1) / c n ≤ (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := by
    rw [div_le_iff₀ hcn, mul_comm]
    exact (hRr n).trans hR'
  have hhi : max 1 (c n * (aSeed n : ℝ) / c n) ≤
      ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ := by
    rw [t0K_eq_aSeed_T0K hcn (h1 n)]
    have := hclock n
    linarith
  have key := (F.tower.history (ind n)).hscaleK_rescale_P6X3 (hc n)
    (fun i' _ => records (ind n) i') (T₀ := c n * (aSeed n : ℝ))
    (A := (n : ℝ) + 1) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹)
    (fun i' hi' b' => by
      rw [max_eq_right habs]
      have hb := birthN_aSeed_T0K records hrcs hanti hδq ind (fun m : ℕ => (m : ℝ) + 1)
        (T₀ := T₀) (c := c) (aS := fun k => (aSeed k : ℝ)) (Tn := fun k => (Tn k : ℝ))
        (Tno := fun k => (Tno k : ℝ)) hTr hΛ hlate hc hTno hTno0 h2c hclock n i' hi' b'
      simpa only [max_self] using hb) i hhi b
  rw [hρK n]
  exact key

theorem drvResF_DT_Cg_ThS_of_engine_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {εb C1b C2b : ℝ} {Ctimeb : ℝ≥0}
    {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hεb : 0 < εb) (hεb' : εb < 1 / 11)
    (hC1 : GC.LongTime.Ch11.csHN_CH2.{u} εb ≤ C1b) (hC2' : GC.LongTime.Ch11.csHN_CH2.{u} εb ≤ C2b)
    (hCt : GC.LongTime.Ch11.ctHN_CH2.{u} εb ≤ Ctimeb) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hδq : Tendsto q.delta atTop (𝓝 0))
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
    (hT : ∀ n, thetaF_FS.{u} records hrcs hanti hδq hfine ha₀ hHI0 hεb hεb' Ctime n ≤ T₀ n)
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    DrvResF_DT_Cg_ThS_FS F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hevF hlt
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hevF n).1.trans (hevF n).2
  -- Icc → 数值
  have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
    have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
    rw [this]; field_simp [(hc k).ne']
  have hTno0 : ∀ k, 0 ≤ (Tno k : ℝ) := fun k => (Tno k).2.1
  have h2c : ∀ k, 2 * c k < (Tno k : ℝ) := fun k => h2r k
  have hρK : ∀ k, ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ =
      c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [hTno k]; exact RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q (Tn k : ℝ)
  have hRρ' : ∀ k, R k ≤ c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [← hρK k]; exact hRρ k
  -- 单一元组与供给
  have hspec := hnotPackF_spec_FS.{u} hεb hεb' Ctime
  have hspec5 := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackExF_FS.{u} hεb hεb' Ctime)))))
  obtain ⟨-, -, -, -, -, -, -, -, hprod⟩ := hspec5
  have hsup := Classical.choose_spec (drvResE_records_of_engine_T0K records hrcs hanti hδq hfine
    ha₀ hHI0 (hnotNfF_FS.{u} hεb hεb' Ctime) (hnotζF_FS.{u} hεb hεb' Ctime)
    (hnotRnF_FS.{u} hεb hεb' Ctime) (hnotδF_FS.{u} hεb hεb' Ctime)
    (hnotmF_FS.{u} hεb hεb' Ctime)
    hspec.2.1 hspec.2.2.2.2.2.1) T₀ hT ind c (fun k => (σ k : ℝ)) L R (fun k => (Tn k : ℝ))
    (fun k => (Tno k : ℝ)) (fun k => (aSeed k : ℝ)) hc hTno hTno0 h2c hclock h1 hlate hroom hRr
    hRρ' hwin
  obtain ⟨p, recKHo, haccK, hradK, hordK, hcanH, hδK, hbirthK, hbirthAK, hHIK, hT0X, htail⟩ := hsup
  let qK : ℕ → CutoffParameters := fun n => (p n).rescale_P6N (c n) (hc n)
  let T₀K : ℕ → ℝ := fun n => max 1 (c n * (aSeed n : ℝ) / c n)
  let recK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n) :=
    fun n i hi => (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi
  have hcanK : ∀ n i hi b, ((recK n i hi).static b).hasCanonicalWindow :=
    fun n i hi b => (F.tower.history (ind n)).hcanK_rescale_P6X3 (hc n) (recKHo n) (hcanH n)
      i hi b
  have ha₀K : ∀ n, 0 < a₀ / c n := fun n => div_pos ha₀ (hc n)
  have hslabK := hslabK_of_tds_HND hanti hder ind c hc (fun n => (Tn n : ℝ))
  obtain ⟨-, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hderF : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n => by
    have h := hderF0 n (hfin n)
    beta_reduce at h
    rw [hQe n, hTc n] at h
    exact h
  have hQp : ∀ n : ℕ,
      0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    inv_pos.mpr (pow_pos ((q.rescale_P6N (c n) (hc n)).neckRadius_pos _ (Tn n).2.1) 2)
  have hn1 : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) + 1 := fun n => by positivity
  have hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1)
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recK n i hi).static b).neck.scale := fun n i hi b =>
    (mul_le_mul_of_nonneg_right (le_max_left _ _)
      ((hn1 n).trans (le_max_left _ _))).trans (hbirthK n i hi b)
  have hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ / c n * ((recK n i hi).static b).neck.scale :=
    Filter.Eventually.of_forall fun n i hi b => hbirthAK n i hi b
  have hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) := fun n =>
    (haccK n).trans (hspec.2.2.1 n)
  have hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius := fun n =>
    (hspec.2.2.2.1 n).trans (hradK n)
  have hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder := fun n =>
    (hspec.2.2.2.2.2.2.2 n).trans (hordK n)
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)
  have hT₀K1 : ∀ n, 1 ≤ a₀ / c n + T₀K n := fun n => by
    have := le_max_left 1 (c n * (aSeed n : ℝ) / c n)
    have := ha₀K n
    change (1 : ℝ) ≤ a₀ / c n + max 1 (c n * (aSeed n : ℝ) / c n)
    linarith
  have hpinchK := (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₀K
    ha₀K hT₀K1 hHIK).1
  have hGinit : ∀ n, (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n =>
    (K n).toHistory.final_initial (hfin n)
  have hpinchF : ∀ n, Perelman.PhiAlmostNonnegative
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) Phi :=
    fun n => (hP (fun _ => K n) (fun _ => q.rescale_P6N (c n) (hc n)) (fun _ => hrecF n)
      (fun _ => a₀ / c n) (fun _ => T₀K n) (fun _ => ha₀K n) (fun _ => hT₀K1 n)
      (fun _ => hHIK n)).2
      (fun _ => (K n).horizon) (fun _ => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl
        (hfin n) le_rfl) (fun _ => hGinit n) 0
  have hhalf := ObservedHistory.hhalf_of_room_one_A6K σ Tn R L hRpos hroom
  have hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n))
      ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
        ((K n).toHistory.activeStage_mono (has n)) ((K n).toHistory.activeStage_mono (hsT n)))
      (y n) ≠ ⊤ := fun n => ne_top_of_lt (hball n)
  have hsepK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          ((recK n i hi).static b).neck.scale := by
    intro T _ C hC
    filter_upwards [two_max_lt_birth_MJ hRr hC] with n hn i hi b _
    refine hn.trans_le (le_trans ?_ (hbirthK n i hi b))
    exact mul_le_mul (le_max_left _ _) ((hRρ n).trans (le_max_right _ _)) (hRpos n).le
      ((hn1 n).trans (le_max_left _ _))
  obtain ⟨Cst, hsurv, hext⟩ := ObservedHistory.finalSurvExt_of_engine_FS (Cg := Cg) (ε := ε)
    (C1 := C1) (C2 := C2) (Ctime := Ctime) (phi := Phi) (Q := fun n =>
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (a₀K := fun n => a₀ / c n)
    (qK := qK) (T₀K := T₀K) (recordsK := recK) (pF := fun n => q.rescale_P6N (c n) (hc n))
    hevF hC2 hcanK hacc hrad hord htail hT0X hsepK (fun n i => hrecF n i)
    (fun n i hi => (hδK n i hi).trans (hspec.2.2.2.2.2.2.1 n)) hPhi ha₀K hHIK hscale
    (Filter.Eventually.of_forall fun n i hi b => hbirthAK n i hi b) hpinchK hpinchF Tn aSeed
    haT hsT has pT seedTrace (fun n i => hslabK n i) hderF hclock h1 hsm hhalf hL hgood hRdef
    hRpos hRr hfinK
    (fun n => by
      have h11 := (hspec.2.2.2.2.1 n).trans (hradK n)
      change StandardCap.transitionEnd + 10 < (p n).modelRadius
      linarith)
    (fun n yG' hyG => hprod hC1 hC2' hCt σ y hevF
      (fun k => Subtype.coe_le_coe.mpr (hsT k)) (Q := fun n =>
        ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (T₀ := T₀K) (p := qK)
      (pF := fun n => q.rescale_P6N (c n) (hc n)) (recordsK := recK) hrecF
      (a₀ := fun n => a₀ / c n) hHIK hcanK (fun n i hi => hδK n i hi) haccK hradK hordK hQp
      (fun n j => hslabK n j) (fun n _ => hderF n)
      (fun n i hi b => (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQp n).le
        ((hn1 n).trans (le_max_left _ _))).trans (hbirthK n i hi b))
      (fun n i hi b => hbirthAK n i hi b) hsel n yG' hyG)
  refine ⟨qK, T₀K, recK, hsepK, htail, hcanK, hacc, hrad, hord, Cst, hsurv, hext, hscale,
    hbirthA, 1, one_pos, ?_⟩
  intro B hB
  refine Filter.Eventually.of_forall ?_
  intro n i hi b _ _
  have hcn := hc n
  have hR' : R n ≤ c n * (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := hRρ' n
  have habs : ((n : ℝ) + 1) / c n ≤ (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹ := by
    rw [div_le_iff₀ hcn, mul_comm]
    exact (hRr n).trans hR'
  have hhi : max 1 (c n * (aSeed n : ℝ) / c n) ≤
      ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ := by
    rw [t0K_eq_aSeed_T0K hcn (h1 n)]
    have := hclock n
    linarith
  have key := (F.tower.history (ind n)).hscaleK_rescale_P6X3 (hc n)
    (fun i' _ => records (ind n) i') (T₀ := c n * (aSeed n : ℝ))
    (A := (n : ℝ) + 1) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n : ℝ) ^ 2)⁻¹)
    (fun i' hi' b' => by
      rw [max_eq_right habs]
      have hb := birthN_aSeed_T0K records hrcs hanti hδq ind (fun m : ℕ => (m : ℝ) + 1)
        (T₀ := T₀) (c := c) (aS := fun k => (aSeed k : ℝ)) (Tn := fun k => (Tn k : ℝ))
        (Tno := fun k => (Tno k : ℝ)) hTr hΛ hlate hc hTno hTno0 h2c hclock n i' hi' b'
      simpa only [max_self] using hb) i hhi b
  rw [hρK n]
  exact key

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
