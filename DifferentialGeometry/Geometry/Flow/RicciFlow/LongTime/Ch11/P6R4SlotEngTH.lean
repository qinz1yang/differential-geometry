import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4FrameSupplyTJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4HnotCTH

/-!
# TRSHNOT G2：R4 帧 J10 槽 producer `r4Slot_of_engine_TH`（`r4Slot_of_engine_TJ` 的 hnot 内付孪生，后缀 `_TH`）

`r4Slot_of_engine_TJ`（P6R4FrameSupplyTJ，TRSJ10 G2）以 `R4HnotC_TJ` 为唯一残余前提。本孪生**去掉该前提**：
元组 `(Nf, ζ, Rn, δ₀, m₀)` 由 G1 核 `r4HnotC_core_TH Ctime` 给出，hnot 于 R4 中心 `(t, y′)` 由同一核在调用点
供给——环境数据 `Q := ρ̃(Tn)⁻²`、`scalar(t, y′) < 2R ≤ 2Q`（`hcmp` + `hceil`）、事件 slab 导数界 `hslabT`
（`hslabK_of_tds_HND`）、`recordsF := (recQ (ind n) i).rescale_P6M (c n) (hc n)`（引擎已有的 full records，
与 `drvSlots_Rc_of_J10_R4J` 的 pF 记录同款）。证明体 = `r4Slot_of_engine_TJ` 逐字，只改两处：
`obtain` 元组换成 `r4HnotC_core_TH`，`h3 := hnot …` 换成 `hcore …`（多传 `Q / Tn / hQ2 / recordsF` 四项）。
结论 `∃ Θ', R4Slot_TJ …` 与 TJ 版逐字相同（`R4Slot_TJ` 来自 P6R4FrameSupplyTJ）。
生成器 build-logs/scratch/O-CH11-TRSHNOT/gen/g2.py。
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

/-- **R4 J10 槽 producer（`_TH`，PROVISIONAL[引擎级 `hfine` / `hrecent` / `hTD` / `hpinK`]；hnot 内付）**：
T0K 供给 + G1 核 + 小引理 ⇒ `∃ Θ', R4Slot_TJ`。无 `R4HnotC_TJ` 前提。 -/
theorem r4Slot_of_engine_TH {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} (hC2 : 0 ≤ C2)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (recQ : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrecent : GC.LongTime.Ch11.RecentCutoffSupply_C11S recQ)
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale)
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinK : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ)
      (i' : Fin ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.eventCount),
      Perelman.PhiAlmostNonnegative
        (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.event i').incoming.flow
        (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.castSucc)
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.succ) ∩
          Ici (1 / 2)) phi)
    :
    ∃ Θ' : ℕ → ℝ, R4Slot_TJ F q ε C1 C2 Ctime Θ' := by
  obtain ⟨Nf, ζ, Rn, δ₀, m₀, hNf, hζ, hδ₀, hcore⟩ := RetainedCoreHistory.r4HnotC_core_TH.{u} Ctime
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨Θ, hΘ⟩ := drvResE_records_of_engine_T0K recQ hrecent hanti hδq hfine ha₀ hHI
    Nf (fun n => min (ζ n) (1 / ((n : ℝ) + 1))) (fun n => max (Rn n) ((n : ℝ) + 1))
    (fun n => min (δ₀ n) (1 / ((n : ℝ) + 1))) (fun n => max (m₀ n) (n + 2))
    (fun n => lt_min (hζ n) (by positivity)) (fun n => lt_min (hδ₀ n) (by positivity))
  refine ⟨fun k => 2 * Θ k, ?_⟩
  intro Aseed ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hTn2 seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat hts hy' hcross
    hslab hclose hcompR hcmp hcmpL hgood' hΘ'
  -- 数值前提（供给的合同）
  have hTnc : ∀ n, 0 ≤ c n * (Tn n : ℝ) := fun n => mul_nonneg (hc n).le (Tn n).2.1
  have h2c : ∀ n, 2 * c n < c n * (Tn n : ℝ) := fun n => by
    have := hTn2 n
    nlinarith [hc n]
  have hΘc : ∀ n, Θ n ≤ c n * (aSeed n : ℝ) := fun n => by
    have h1 := hΘ' n
    have h2 := hTn2 n
    have h3 := hclock n
    nlinarith [hc n, mul_pos (hc n) (sub_pos.2 h2)]
  have hRρ : ∀ n, R n ≤ c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ := fun n => by
    have := hceil n
    rwa [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n)] at this
  have hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      (aSeed n : ℝ) ≤ ((Tn n : ℝ) - 1 ^ 2 / 2 + L n ^ 2 / R n) - T / R n := by
    intro T hT
    filter_upwards [hL.eventually_ge_atTop (max T 1)] with n hn
    have hLT : T ≤ L n := (le_max_left _ _).trans hn
    have hL1 : 1 ≤ L n := (le_max_right _ _).trans hn
    have hLL : T ≤ L n ^ 2 := by nlinarith
    have hnn : 0 ≤ (L n ^ 2 - T) / R n := div_nonneg (by linarith) (hRpos n).le
    have : L n ^ 2 / R n - T / R n = (L n ^ 2 - T) / R n := by ring
    have h3 := hclock n
    linarith
  obtain ⟨p, recKHo, hacc, hrad, hord, hcan, hδ, hbirth, hbirthA, hHIk, -, -⟩ :=
    hΘ (fun n => c n * (aSeed n : ℝ)) hΘc ind c (fun n => (Tn n : ℝ) - 1 ^ 2 / 2 + L n ^ 2 / R n)
      L R (fun n => (Tn n : ℝ)) (fun n => c n * (Tn n : ℝ)) (fun n => (aSeed n : ℝ)) hc
      (fun n => rfl) hTnc h2c hclock hone (fun n => le_rfl) (fun n => le_of_eq (by ring)) hRr hRρ
      hwin
  -- K 帧数据包
  have hT0eq : ∀ n, max 1 (c n * (aSeed n : ℝ) / c n) = (aSeed n : ℝ) := fun n =>
    t0K_eq_aSeed_T0K (hc n) (hone n)
  have hcanK : ∀ n i hi b, (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n)
      i hi).static b).hasCanonicalWindow := fun n =>
    (F.tower.history (ind n)).hcanK_rescale_P6X3 (hc n) (recKHo n) (hcan n)
  have hQpos : ∀ n, 0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    lt_of_lt_of_le (hRpos n) (hceil n)
  have hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) *
      max ((n : ℝ) + 1) (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) ≤
      (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
        ).neck.scale := fun n i hi b =>
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_trans (by positivity) (le_max_left _ _))) (hbirth n i hi b)
  have hNfQ : ∀ (n : ℕ) i hi b, Nf n *
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
        ).neck.scale := fun n i hi b =>
    le_trans (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQpos n).le
      (le_trans (by positivity) (le_max_left _ _))) (hbirth n i hi b)
  have hslabT : ∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
      ((((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event i).incoming
        ).DerivativeBoundBefore Ctime
        (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
        (min (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) (Tn n : ℝ)) :=
    fun n i => hslabK_of_tds_HND hanti hTD ind c hc (fun n => (Tn n : ℝ)) n i
  have haccN : ∀ n : ℕ, ((p n).rescale_P6N (c n) (hc n)).modelAccuracy ≤ 1 / ((n : ℝ) + 1) :=
    fun n => (hacc n).trans (min_le_right _ _)
  have hradN : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).rescale_P6N (c n) (hc n)).modelRadius :=
    fun n => (le_max_right _ _).trans (hrad n)
  have hordN : ∀ n : ℕ, n + 2 ≤ ((p n).rescale_P6N (c n) (hc n)).modelOrder :=
    fun n => (le_max_right _ _).trans (hord n)
  have hQ2 : ∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n) <
      2 * ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    lt_of_lt_of_le (hcmp n) (mul_le_mul_of_nonneg_left (hceil n) zero_le_two)
  have h3 := hcore (K := fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n)) t y'
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (Tn := fun n => (Tn n : ℝ)) hQpos (fun n => Subtype.coe_le_coe.mpr ((hts n).trans (hsT n)))
    hQ2 hslabT
    (qK := fun n => (p n).rescale_P6N (c n) (hc n))
    (T₀K := fun n => max 1 (c n * (aSeed n : ℝ) / c n))
    (recordsK := fun n i hi =>
      (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi)
    (pF := fun n => q.rescale_P6N (c n) (hc n)) (a₀K := fun n => a₀ / c n)
    (fun n i => (recQ (ind n) i).rescale_P6M (c n) (hc n)) hcanK
    (fun n => (hacc n).trans (min_le_left _ _)) (fun n => (le_max_left _ _).trans (hrad n))
    (fun n => (le_max_left _ _).trans (hord n))
    hHIk (fun n i hi => (hδ n i hi).trans (min_le_left _ _)) hNfQ hbirthA
  -- 其余派生项
  have hfinK : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n))
      ((seedTrace n).point ((Kh n).activeStage (t n)) ((Kh n).activeStage_mono (hat n))
        ((Kh n).activeStage_mono ((hts n).trans (hsT n)))) (y' n) ≠ ⊤ := fun n =>
    ne_top_of_compR_TJ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (hcompR n) (hgateP n)
  have hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (j : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)
        (hj : max 1 (c n * (aSeed n : ℝ) / c n) ≤
          ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time j.succ) b,
        (σ n : ℝ) - T / R n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time j.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          (((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) j hj).static b
            ).neck.scale := by
    intro T _ C hC
    obtain ⟨N, hN⟩ := sepBound_TJ hRr C hC
    filter_upwards [eventually_ge_atTop N] with n hn j hj b _
    refine hN n hn _ ?_
    have h1 := hscaleK n j hj b
    have h2 : R n ≤ max ((n : ℝ) + 1) (((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) :=
      (hceil n).trans (le_max_right _ _)
    exact le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      max 1 (c n * (aSeed n : ℝ) / c n) ≤ (σ n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [haS T hT] with n hn
    rw [hT0eq n]
    exact hn
  have hT₀X : ∀ᶠ n in atTop,
      max 1 (c n * (aSeed n : ℝ) / c n) ≤ (t n : ℝ) - (1 / 100 : ℝ) ^ 2 := by
    filter_upwards [hTnS 1 one_pos] with n hn
    rw [hT0eq n]
    have h1 := hclose n
    have h2 := hclock n
    have h3 : (1 : ℝ) / R n = 1 / R n := rfl
    nlinarith [h1, h2, hn]
  exact drvSlots_Rc_of_J10_R4J (K := fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    (Ctime := Ctime) (ε := ε) (C1 := C1) (C2 := C2) hC2
    (qK := fun n => (p n).rescale_P6N (c n) (hc n))
    (T₀K := fun n => max 1 (c n * (aSeed n : ℝ) / c n))
    (recordsK := fun n i hi =>
      (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi)
    hcanK haccN hradN hordN (pF := fun n => q.rescale_P6N (c n) (hc n))
    (fun n i => (recQ (ind n) i).rescale_P6M (c n) (hc n))
    (fun n i hi => (hδ n i hi).trans (min_le_right _ _)) hphi
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (a₀K := fun n => a₀ / c n) hHIk hscaleK (Filter.Eventually.of_forall hbirthA)
    (fun n i t ht x => hpinK ind c hc n i t ⟨ht.1, (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
      ((le_max_left _ _).trans ht.2)⟩ x)
    Tn aSeed haT pT seedTrace hslabT hclock hone hsm σ t y' hsT hat hts hRpos hRr hL i hslab hclose
    hcmp hcmpL hTnS hgood' hfinK hsep hT₀K (fun n => div_pos ha₀ (hc n)) hT₀X h3

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
