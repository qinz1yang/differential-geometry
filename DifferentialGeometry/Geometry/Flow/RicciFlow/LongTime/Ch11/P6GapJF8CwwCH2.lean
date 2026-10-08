import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersFinalNoJ10P6JB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J9LocSupplyP6KT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelSlabKTSupplyP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotFinalCwwP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BirthOnTailP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapJF8CwwP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnSpecCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6GapJF8CwwCHN.lean` 机械克隆]
# CHN G1d：JF8 (CWW) producer 在显式 csHN / ctHN 处

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6GapJF8CwwP6HN.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6CoarseC_eq_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6
  p6FineEta_le_C11GT6)
namespace ObservedHistory
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- **JF8 producer 的 (CWW) 孪生（`_P6HN`，PROVISIONAL[OPEN `hJ11F8`、`hJ15F8`、`hOpenF8J′`、先验 TDS]）**：
KT2c `hgapJF8_loc_of_producers_P6KT2c_CH2` 逐字（坏点常数泛化为
`η₁ C1₁ C2₁ Ctime₁`），改动：(i) `hOpenFJ` 的 cap-window 合取（final CWS diag + hsepF）删去，
由 G9 `hnotK_final_cww_P6HN` 在本定理选的 records 上付；(ii) `hOpenFJ` 的 J6 因子 `n+1` 加强为
`max (n+1) (Cb n)⁻¹`（G10 `birth_on_tail_of_recent_P6HN` 同机制供给）；(iii) diagonal 档换 G9 的
`(Cb Rn ζ δ₀ m₀)`（Ctime₀ 之后取），T₀ 阈值随之为 ∃ `Tmin`；
(iv) 常数约束 `Cs(η₁) ≤ C1₁, C2₁`、`CtHN ≤ Ctime₁`（坏点常数）。 -/
theorem hgapJF8_loc_of_producers_cww_P6HN_CH2 {η₁ : ℝ} (hη : 0 < η₁) (hη' : η₁ < 1 / 11) :
    0 < GC.LongTime.Ch11.ctHN_CH2.{u} η₁ ∧ 1 ≤ GC.LongTime.Ch11.csHN_CH2.{u} η₁ ∧ ∀ Ctime₀ : ℝ≥0,
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
      {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0},
      GC.LongTime.Ch11.csHN_CH2.{u} η₁ ≤ C1₁ → GC.LongTime.Ch11.csHN_CH2.{u} η₁ ≤ C2₁ →
        GC.LongTime.Ch11.ctHN_CH2.{u} η₁ ≤ Ctime₁ →
    (AntitoneOn q.neckRadius (Ici 0)) →
    (Tendsto q.delta atTop (𝓝 0)) →
    ∀ (records : GC.LongTime.Ch11.CutoffRecords_C11S F q),
    (∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z)) →
    (GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime₀) →
    ∀ {a₀ : ℝ}, 0 < a₀ →
    (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
    ∃ Tmin : ℕ → ℝ, ∀ {T₀ Qt : ℕ → ℝ}, (∀ n, Tmin n ≤ T₀ n) →
    HnJ11F8_P6HN F q ε C1 C2 Ctime a₀ T₀ Qt η₁ C1₁ C2₁ Ctime₁ →
    HnJ15F8_P6HN F q ε C1 C2 Ctime a₀ T₀ Qt η₁ C1₁ C2₁ Ctime₁ →
    HnOpenF8J_P6HN F q ε C1 C2 Ctime a₀ T₀ Qt Cb η₁ C1₁ C2₁ Ctime₁ →
    hgapJF8_loc_P6KT2 F q η₁ C1₁ C2₁ Ctime₁ ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨hCtHN, hCs, hG9⟩ := RetainedCoreHistory.hnotK_final_cww_at_CH2.{u} hη hη'
  generalize GC.LongTime.Ch11.ctHN_CH2.{u} η₁ = CtHN at hCtHN hG9 ⊢
  generalize GC.LongTime.Ch11.csHN_CH2.{u} η₁ = Cs at hCs hG9 ⊢
  refine ⟨hCtHN, hCs, fun Ctime₀ => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCbb, hζb, hδb, hRnb, hm₀b, hmain⟩ := hG9 Ctime₀
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCbb, hζb, hδb, hRnb, hm₀b, ?_⟩
  intro P g F q ε C1 C2 Ctime C1₁ C2₁ Ctime₁ hC1 hC2 hCt hanti hδq records hP5L hTD a₀ ha₀ hHI
  refine ⟨Classical.choose (diagonalPack_nom_CXKN (H := F.tower.history) records Cb Rn ζ δ₀ m₀
    hCbb (fun n => (hζb n).1) (fun n => (hδb n).1) ha₀ (fun _ => 0) hP5L hδq hanti),
    fun {T₀ Qt} hT₀' hJ11F8 hJ15F8 hOpenF8J => ?_⟩
  obtain ⟨Phi, hPhi, hphi⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      (a₀ := 1) one_pos
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hfin hlt
  obtain ⟨hK, hJ16, hdistQ, hclosGF⟩ :=
    hOpenF8J A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
  -- D-7：records / J4 / J5 / J8 取 KNOM 的一次 `choose_spec`（固定档 ζ = δ₀ = 1/(n+1)、Rn = n+1、m₀ = n+2）
  obtain ⟨p, recordsK, hcan, hδo, hacco, hrado, hordo, -, hJ8, -, -, -⟩ :=
    Classical.choose_spec (diagonalPack_nom_CXKN (H := F.tower.history) records
      Cb Rn ζ δ₀ m₀ hCbb
      (fun n => (hζb n).1) (fun n => (hδb n).1) ha₀ (fun _ => 0) hP5L hδq hanti) T₀ hT₀' ind
  have hδ : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1) :=
    fun n i hi => (hδo n i hi).trans (hδb n).2
  have hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) :=
    fun n => (hacco n).trans (hζb n).2
  have hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius := fun n => (hRnb n).trans (hrado n)
  have hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder := fun n => (hm₀b n).trans (hordo n)
  have hJ6' := hK p recordsK hcan hδ hacc hrad hord hJ8
  have hJ6 : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) *
      max (((n : ℝ) + 1) / c n) (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) ≤
      ((recordsK n i hi).static b).neck.scale := fun n i hi b =>
    (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_trans (by have := hc n; positivity) (le_max_left _ _))).trans (hJ6' n i hi b)
  have hQs : ∀ n : ℕ, 0 < c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹ :=
    fun n => mul_pos (hc n) (lt_of_lt_of_le (by have := hc n; positivity) (le_max_left _ _))
  have hbirthK : ∀ n i hi b, c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹ ≤
      Cb n * (((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale := by
    intro n i hi b
    have h := (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hJ6' n) i hi b
    refine qs_le_birth_of_tail_P6HN (hCbb n).1 (le_max_right ((n : ℝ) + 1) _) (hQs n).le ?_
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _)
      (le_trans zero_le_one (le_trans (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        (le_max_left _ _)))).trans h
  have hCWS := hmain hC1 hC2 hCt (K := K) (Tn := fun n => (Tn n : ℝ)) σ y hfin
    (fun n => hsT n) (Q := fun n => c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹)
    (T₀ := fun n => max 1 (T₀ n / c n)) (p := fun n => (p n).rescale_P6N (c n) (hc n))
    (pF := fun n => q.rescale_P6N (c n) (hc n))
    (recordsK := fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := fun n => a₀ / c n)
    (fun n => (Ho n).hHI_rescale_P6X3 (hc n) (hHI (ind n)))
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n))
    (fun n => (Ho n).hδF_rescale_P6X3 (hc n) (hδo n)) hacco hrado hordo hQs
    (fun n => (Ho n).eventSlabsDerivT_rescale_P6KT (hc n)
      (GC.LongTime.Ch11.hslabKT_of_supply_P6KT2 hTD le_rfl hanti (fun t ht => q.neckRadius_pos t ht)
        ind (fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹)
        (fun n => (Tno n : ℝ)) (fun _ => le_max_right _ _) n))
    (fun n hK => (Ho n).derivativeBoundBefore_finalSlab_min_rescale_P6KT (hc n)
      (tK := (Tno n : ℝ))
      (fun hK' => GC.LongTime.Ch11.finalSlabDerivT_of_supply_P6KT hTD le_rfl (ind n)
        (fun _ ht0 htK => GC.LongTime.Ch11.ceil_of_antitone_P6KT2 hanti
          (fun t ht => q.neckRadius_pos t ht) (le_max_right _ _) ht0 htK.le) hK') hK)
    hbirthK (fun n => (Ho n).hbirthA_rescale_P6X3 (hc n) (recordsK n) (hJ8 n)) hsel
  obtain ⟨κd, hκd, hvolO⟩ :=
    hJ11F8 A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
    p recordsK hcan hδ hacc hrad hord hJ8 hJ6
  obtain ⟨κ, ρV, hκ, hρV, hκR, hκRF⟩ :=
    hJ15F8 A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
    p recordsK hcan hδ hacc hrad hord hJ8 hJ6
  -- 重标度窗口 HI（年龄 `0 + τ`）⇐ 原尺度 records + 初始 HI（同 jointD 映射）
  have hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (0 + τ') x :=
    fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (records (ind n)) ha₀ (hHI (ind n))
  have hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
      ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, 1 ≤ a ∧
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x := by
    intro T hT
    filter_upwards [hwin T hT] with n hn
    intro v _ hv x
    exact ⟨0 + (v : ℝ), by linarith [h1 n], hpin n v x⟩
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have := hRr n
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simp only [one_pow, mul_one]
    exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlateR : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hwin T hT] with n hn
    have ha1 : (1 : ℝ) ≤ (σ n : ℝ) - T / R n := (h1 n).trans hn
    calc (1 : ℝ) ≤ R n * 1 := by linarith [hR1 n]
      _ ≤ R n * ((σ n : ℝ) - T / R n) := mul_le_mul_of_nonneg_left ha1 (by linarith [hR1 n])
  -- event `hclosG` ⇐ J16 `hscalU` + first exit（同 jointD）
  have hclosG := hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
    (fun _ => 1) hL hsm hclock hRr1 hwin hlateR le_rfl hpin hJ16
  refine ⟨Ctime₀, Phi, fun n => c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹,
    fun n => max 1 (T₀ n / c n), fun n => (p n).rescale_P6N (c n) (hc n),
    fun n => q.rescale_P6N (c n) (hc n), fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n),
    fun n => a₀ / c n, ⟨fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)⟩, hPhi,
    fun n => (Ho n).hHI_rescale_P6X3 (hc n) (hHI (ind n)),
    fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n),
    fun n => (Ho n).hδF_rescale_P6X3 (hc n) (hδ n), hacc, hrad, hord,
    fun n => (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hJ6 n),
    Eventually.of_forall fun n => (Ho n).hbirthA_rescale_P6X3 (hc n) (recordsK n) (hJ8 n),
    fun n i => (Ho n).toHistory.phiAlmostNonnegative_rescale_P6X2 hphi (hc n) (records (ind n)) ha₀
      (hHI (ind n)) (le_max_left _ _) i,
    fun n hK => (Ho n).phiAlmostNonnegative_finalSlab_rescale_P6WR2 hphi (hc n) (records (ind n))
      ha₀ (hHI (ind n)) (le_max_left _ _) hK,
    fun n => (Ho n).eventSlabsDerivT_rescale_P6KT (hc n)
      (GC.LongTime.Ch11.hslabKT_of_supply_P6KT2 hTD le_rfl hanti (fun t ht => q.neckRadius_pos t ht)
        ind (fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹)
        (fun n => (Tno n : ℝ)) (fun _ => le_max_right _ _) n),
    fun n hK => (Ho n).derivativeBoundBefore_finalSlab_min_rescale_P6KT (hc n)
      (tK := (Tno n : ℝ))
      (fun hK' => GC.LongTime.Ch11.finalSlabDerivT_of_supply_P6KT hTD le_rfl (ind n)
        (fun _ ht0 htK => GC.LongTime.Ch11.ceil_of_antitone_P6KT2 hanti
          (fun t ht => q.neckRadius_pos t ht) (le_max_right _ _) ht0 htK.le) hK') hK,
    fun n => max_le (h1 n) (by rw [div_le_iff₀ (hc n)]; linarith [hT₀l n]),
    hCWS, ⟨κd, hκd, hvolK_of_orig_P6CK (Ho := Ho) (c := c) hc σ y R hRpos hvolO⟩,
    ⟨1, one_pos, hpinL⟩, hdistQ, ⟨κ, ρV, hκ, hρV, hκR, hκRF⟩, hclosG, hclosGF⟩
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
