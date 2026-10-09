import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResE4ThDefMJ

/-!
# MJ G2：DT 行 θ₀ 尾核 ⇒ `DrvResE4_DT_V11`（引擎供给桥，后缀 `_MJ`）

见 `P6DrvResE4ThDefMJ`。本文件：`thetaJ_MJ`（T0K 供给的 Θ，元组由 `(ε, Ctime)` 定出）、
Icc → 数值转换、桥 `drvResE4_DT_of_Th_MJ`（PROVED）、旧核 ⇒ 新核 `drvResE4_Th_of_E4_MJ`（PROVED）。
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

/-- **供给阈值 Θ（`_MJ`）**：T0K 供给 `drvResE_records_of_engine_T0K` 在 `(ε, Ctd)` 定出的单一元组处的 `Θ`。 -/
def thetaJ_MJ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (drvResE_records_of_engine_T0K records hrcs hanti hδq hfine ha₀ hHI
    (hnotNf_MJ.{u} hε hε' Ctd) (hnotζ_MJ.{u} hε hε' Ctd) (hnotRn_MJ.{u} hε hε' Ctd)
    (hnotδ_MJ.{u} hε hε' Ctd) (hnotm_MJ.{u} hε hε' Ctd)
    (hnotPack_spec_MJ.{u} hε hε' Ctd).2.1 (hnotPack_spec_MJ.{u} hε hε' Ctd).2.2.2.2.2.1)

/-- 实数引理：`n` 大时 `2·max (3/(1/100)²) (C·R) < (n+1)·R`（`R ≥ n+1`）。 -/
theorem two_max_lt_birth_MJ {R : ℕ → ℝ} (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) {C : ℝ}
    (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((n : ℝ) + 1) * R n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C + 246)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 2 * C + 246 ≤ (n : ℝ) := hN.trans hnN
  have hR := hRr n
  have hRpos : 0 < R n := lt_of_lt_of_le (Nat.cast_add_one_pos n) hR
  have h30 : 3 / ((1 : ℝ) / 100) ^ 2 = 30000 := by norm_num
  rw [h30, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  refine max_lt ?_ ?_
  · nlinarith
  · nlinarith

/-- **旧核 ⇒ 新核（`_MJ`，PROVED）**：`DrvResE4_DT_V11` 的最后一个合取投影。 -/
theorem drvResE4_Th_of_E4_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ} (h : DrvResE4_DT_V11 F q records ε C1 C2 Ctime T₀ Qt a₀) :
    DrvResE4_DT_Th_MJ F q records ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, θ₀, hθ₀, hθ⟩ :=
    h A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  exact ⟨θ₀, hθ₀, hθ⟩

/-- **θ₀ 尾核 ⇒ `DrvResE4_DT_V11`（引擎供给桥，`_MJ`，PROVED 相对 `hrcs`、`hfine`、`hanti`、`hδq`、
`ha₀`/`hHI`、TDS `hder`、`T₀ ≥ thetaJ_MJ`）**。 -/
theorem drvResE4_DT_of_Th_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hC1 : GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C1) (hC2' : GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C2)
    (hCt : GC.LongTime.Ch11.ctSeq_CH2.{u} ε ≤ Ctime) (hC2 : 0 ≤ C2)
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
    (hT : ∀ n, thetaJ_MJ.{u} records hrcs hanti hδq hfine ha₀ hHI0 hε hε' Ctime n ≤ T₀ n)
    (h : DrvResE4_DT_Th_MJ F q records ε C1 C2 Ctime T₀ Qt) :
    DrvResE4_DT_V11 F q records ε C1 C2 Ctime T₀ Qt a₀ := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨θ₀, hθ₀, hθ⟩ := h A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
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
  have hspec := hnotPack_spec_MJ.{u} hε hε' Ctime
  have hspec5 := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackEx_MJ.{u} hε hε' Ctime)))))
  obtain ⟨-, -, -, -, -, -, -, -, hprod⟩ := hspec5
  have hsup := Classical.choose_spec (drvResE_records_of_engine_T0K records hrcs hanti hδq hfine
    ha₀ hHI0 (hnotNf_MJ.{u} hε hε' Ctime) (hnotζ_MJ.{u} hε hε' Ctime)
    (hnotRn_MJ.{u} hε hε' Ctime) (hnotδ_MJ.{u} hε hε' Ctime) (hnotm_MJ.{u} hε hε' Ctime)
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
  -- J10ResE2_DJ 四项
  have hJ2 : J10ResE2_DJ K σ y qK T₀K recK (fun n => a₀ / c n) := by
    refine ⟨ha₀K, fun n => ?_, hT0X, ?_⟩
    · have h11 := (hspec.2.2.2.2.1 n).trans (hradK n)
      change StandardCap.transitionEnd + 10 < (p n).modelRadius
      linarith
    · intro j hjt htj yG hyG
      have hD1 : ∀ n, (K n).EventSlabsDerivative Ctime
          ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ (j n).castSucc :=
        fun n i hi => by
        have hle : i.succ ≤ (j n).castSucc := Fin.castSucc_lt_iff_succ_le.mp hi
        have ht : (K n).time i.succ ≤ (Tn n : ℝ) :=
          (((K n).toHistory.time_strictMono.monotone hle).trans (hjt n).le).trans
            (Subtype.coe_le_coe.mpr (hsT n))
        exact ((K n).toHistory.event i).incoming.derivativeBoundBefore_mono (le_min le_rfl ht)
          (hslabK n i)
      have hD2 : ∀ n, (((K n).toHistory.event (j n)).incoming).DerivativeBoundBefore Ctime
          ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ (σ n) := fun n =>
        ((K n).toHistory.event (j n)).incoming.derivativeBoundBefore_mono
          (le_min (htj n).le (Subtype.coe_le_coe.mpr (hsT n))) (hslabK n (j n))
      refine RetainedCoreHistory.hnot_prefix_of_hnotK_HNF (t := fun n => (σ n : ℝ))
        (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) (D := fun n => (n : ℝ) + 1) j recK yG
        (fun _ => le_rfl) (fun _ => le_rfl) ?_
      exact hprod hC1 hC2' hCt σ hjt htj
        (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (T₀ := T₀K)
        (p := qK) (pF := fun n => q.rescale_P6N (c n) (hc n)) (recordsK := recK)
        (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := fun n => a₀ / c n)
        hHIK hcanK hδK haccK hradK hordK hQp hD1 hD2
        (fun n i hi b _ _ =>
          (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQp n).le
            ((hn1 n).trans (le_max_left _ _))).trans (hbirthK n i hi b))
        (fun n i hi b _ _ => hbirthAK n i hi b) y hyG hsel
  -- J10 帧
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} (A := (1 : ℝ)) one_pos
  have hrecF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (q.rescale_P6N (c n) (hc n)) :=
    fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)
  have hpinchK := (hP K (fun n => q.rescale_P6N (c n) (hc n)) hrecF (fun n => a₀ / c n) T₀K ha₀K
    (fun n => by
      have := le_max_left 1 (c n * (aSeed n : ℝ) / c n)
      have := ha₀K n
      change (1 : ℝ) ≤ a₀ / c n + max 1 (c n * (aSeed n : ℝ) / c n)
      linarith) hHIK).1
  have hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n))
      ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
        ((K n).toHistory.activeStage_mono (has n)) ((K n).toHistory.activeStage_mono (hsT n)))
      (y n) ≠ ⊤ := fun n => ne_top_of_lt (hball n)
  have hhalf := ObservedHistory.hhalf_of_room_one_A6K σ Tn R L hRpos hroom
  have hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) := fun n =>
    (haccK n).trans (hspec.2.2.1 n)
  have hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius := fun n =>
    (hspec.2.2.2.1 n).trans (hradK n)
  have hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder := fun n =>
    (hspec.2.2.2.2.2.2.2 n).trans (hordK n)
  have hJ : J10ResE_RX_HSX K σ y R qK T₀K :=
    j10ResE_of_2_JP (Cg := 4) (ε := ε) (C1 := C1) (C2 := C2) hC2 hcanK hacc hrad hord htail
      (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n))
      (fun n i hi => (hδK n i hi).trans (hspec.2.2.2.2.2.2.1 n)) hPhi hHIK hscale hbirthA
      hpinchK Tn aSeed haT hsT has pT seedTrace (fun n i => hslabK n i) hclock h1 hsm hhalf hL
      hgood hRdef hRpos hRr hfinK hJ2
  have hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recK n i hi).static b).neck.scale := by
    intro T _ C hC
    filter_upwards [two_max_lt_birth_MJ hRr hC] with n hn i hi b _
    refine hn.trans_le (le_trans ?_ (hbirthK n i hi b))
    exact mul_le_mul (le_max_left _ _) ((hRρ n).trans (le_max_right _ _)) (hRpos n).le
      ((hn1 n).trans (le_max_left _ _))
  exact ⟨qK, T₀K, recK, hsep, htail, hcanK, hacc, hrad, hord, hJ, hscale, hbirthA, θ₀, hθ₀, hθ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
