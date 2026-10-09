import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProdFinalFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResJFConj2FS

/-!
# FSUP G4：JF / JF8 的 conj2（缩档形）由引擎数据证出（路线 A，`_FS`）

`hOpenFJ_of_engine_FS` / `hOpenF8J_of_engine_FS`（PROVED 相对 env 前提）：
`HgwResJFOpen_FS` / `HgwResJF8Open_FS`（GP final producer 的 `hOpenFJ{8}` 型，`∀ p recordsK` 块前提档为
元组档 `(ζ, Rn, m₀, δ₀)`、J7b 因子 `max (n+1) (Nf n)`）：
* conj2' 的结论（final 帧 hnot）⇐ `hnotK_final_cww_at_CH2` 的单一元组 `hnotPackExF_FS` 在元组档处的结论
  （records 取 `recordsKRescale_P6X3`，Dt ⇐ SCRS⁺ TDS，birth `Nf·Q ≤ scale` ⇐ J7b' 经
  `hscaleK_rescale_P6X3`，`1 ≤ a₀·scale` ⇐ `hbirthA_rescale_P6X3`，δ 经 `hδF_rescale_P6X3`）——
  档匹配：前提档就是 G9 所需的元组档；
* `DepthExtendable` 合取 ⇐ G1 的 `hDextJF{,8}_of_engine_FS`（同一元组实例）。
无新 binder / Prop。生成器 `build-logs/scratch/O-CH11-FSUP/gen/g9_open.py`。
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

open ObservedHistory (DepthExtendable HgwResJFOpen_FS HgwResJF8Open_FS)
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 p6FineEta_C11GT6)

theorem hOpenFJ_of_engine_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 11) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) (hεle : ε ≤ coneAccuracy)
    (hC1 : GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C1) (hC2' : GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C2)
    (hCt : GC.LongTime.Ch11.ctHN_CH2.{u} ε ≤ Ctime) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
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
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (hT : ∀ n, thetaF_FS.{u} records hrcs hanti hδq hfine ha₀ hHI0 hε hε' Ctime n ≤ T₀ n)
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    HgwResJFOpen_FS F q records ε C1 C2 Ctime a₀ T₀ Qt (hnotNfF_FS.{u} hε hε' Ctime)
      (hnotζF_FS.{u} hε hε' Ctime) (hnotRnF_FS.{u} hε hε' Ctime)
      (hnotδF_FS.{u} hε hε' Ctime) (hnotmF_FS.{u} hε hε' Ctime) := by
  have hb := hDextJF_of_engine_FS (Qt := Qt) hε hε' hεX hεN hεle hC1 hC2' hCt hC2 hanti hder
    hfresh hrcs hδq hfine ha₀ hHI0 hT₀δ hT hTr hΛ
  have hspec := hnotPackF_spec_FS.{u} hε hε' Ctime
  have hspec5 := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackExF_FS.{u} hε hε' Ctime)))))
  obtain ⟨-, -, -, -, -, -, -, -, hprod⟩ := hspec5
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hfin hlt Qs
  refine ⟨?_, hb A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm hT₀l
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt⟩
  let NfT : ℕ → ℝ := hnotNfF_FS.{u} hε hε' Ctime
  intro p recordsK hcan hδp hacc hrad hord hJ8 hwit hJ7b n yG' hyG
  have hfinK : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hfin n).1.trans (hfin n).2
  have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
    have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
    rw [this]; field_simp [(hc k).ne']
  have hρK : ∀ k, ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ =
      c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [hTno k]; exact RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q (Tn k : ℝ)
  have hslabK := hslabK_of_tds_HND hanti hder ind c hc (fun n => (Tn n : ℝ))
  obtain ⟨-, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hderF : ∀ n (hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
      (((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n hK => by
    have h := hderF0 n hK
    beta_reduce at h
    rw [hQe n, hTc n] at h
    exact h
  have hQp : ∀ n : ℕ,
      0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    inv_pos.mpr (pow_pos ((q.rescale_P6N (c n) (hc n)).neckRadius_pos _ (Tn n).2.1) 2)
  have hn1 : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) + 1 := fun n => by positivity
  have hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ / c n) x ∧
      -3 / (a₀ / c n) ≤ metricScalarAt ((K n).initialMetric 0) x :=
    fun n => (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (hHI0 (ind n))
  have hscaleK : ∀ (n : ℕ) i hi b, max ((n : ℝ) + 1) (NfT n) *
      max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      (((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale := by
    intro n i hi b
    have h7 : ∀ i hi b, max ((n : ℝ) + 1) (NfT n) * max (((n : ℝ) + 1) / c n)
        (q.neckRadius (Tno n) ^ 2)⁻¹ ≤ ((recordsK n i hi).static b).neck.scale := fun i hi b => by
      have h := hJ7b n i hi b
      change max ((n : ℝ) + 1) (NfT n) * max (((n : ℝ) + 1) / c n)
        (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) ≤ _ at h
      rwa [← max_assoc, max_self] at h
    have h := (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n)
      (A := max ((n : ℝ) + 1) (NfT n)) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n) ^ 2)⁻¹)
      h7 i hi b
    rwa [← hρK n] at h
  exact hprod hC1 hC2' hCt σ y hfin (fun k => Subtype.coe_le_coe.mpr (hsT k))
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (T₀ := fun n => max 1 (c n * (aSeed n : ℝ) / c n))
    (p := fun n => (p n).rescale_P6N (c n) (hc n))
    (pF := fun n => q.rescale_P6N (c n) (hc n))
    (recordsK := fun n i hi => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi)
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := fun n => a₀ / c n) hHIK
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n))
    (fun n i hi => (Ho n).hδF_rescale_P6X3 (hc n) (fun i' hi' => hδp n i' ((hT₀l n).trans hi'))
      i hi)
    hacc hrad hord hQp (fun n j => hslabK n j) hderF
    (fun n i hi b => (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQp n).le
      ((hn1 n).trans (le_max_left _ _))).trans (hscaleK n i hi b))
    (fun n i hi b => (Ho n).hbirthA_rescale_P6X3 (hc n) (recordsK n) (hJ8 n) i hi b) hsel n yG' hyG

theorem hOpenF8J_of_engine_FS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) (hεle : ε ≤ coneAccuracy)
    (hη : 0 < p6FineEta_C11GT6 ε) (hη' : p6FineEta_C11GT6 ε < 1 / 11)
    (hC1 : GC.LongTime.Ch11.csHN_CH2.{u} (p6FineEta_C11GT6 ε) ≤
      p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
    (hCt : GC.LongTime.Ch11.ctHN_CH2.{u} (p6FineEta_C11GT6 ε) ≤
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)).toNNReal) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
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
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (hT : ∀ n, thetaF_FS.{u} records hrcs hanti hδq hfine ha₀ hHI0 hη hη' Ctime n ≤ T₀ n)
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    HgwResJF8Open_FS F q records ε C1 C2 Ctime a₀ T₀ Qt (hnotNfF_FS.{u} hη hη' Ctime)
      (hnotζF_FS.{u} hη hη' Ctime) (hnotRnF_FS.{u} hη hη' Ctime)
      (hnotδF_FS.{u} hη hη' Ctime) (hnotmF_FS.{u} hη hη' Ctime) := by
  have hb := hDextJF8_of_engine_FS (Cg := 8) (by norm_num) (Qt := Qt) (C1 := C1) (C2 := C2)
    (εb := p6FineEta_C11GT6 ε) (C1b := p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
    (C2b := p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
    (Ctimeb := (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)).toNNReal) hε hεX hεN hεle hη hη' hC1
    hC1 hCt hC2 hanti hder hfresh hrcs hδq hfine ha₀ hHI0 hT₀δ hT hTr hΛ
  have hspec := hnotPackF_spec_FS.{u} hη hη' Ctime
  have hspec5 := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackExF_FS.{u} hη hη' Ctime)))))
  obtain ⟨-, -, -, -, -, -, -, -, hprod⟩ := hspec5
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hfin hlt Qs
  refine ⟨?_, hb A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm hT₀l
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt⟩
  let NfT : ℕ → ℝ := hnotNfF_FS.{u} hη hη' Ctime
  intro p recordsK hcan hδp hacc hrad hord hJ8 hwit hJ7b n yG' hyG
  have hfinK : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon := fun n =>
    (hfin n).1.trans (hfin n).2
  have hTno : ∀ k, (Tno k : ℝ) = c k * (Tn k : ℝ) := fun k => by
    have : (Tn k : ℝ) = (Tno k : ℝ) / c k := rfl
    rw [this]; field_simp [(hc k).ne']
  have hρK : ∀ k, ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ =
      c k * (q.neckRadius (Tno k : ℝ) ^ 2)⁻¹ := fun k => by
    rw [hTno k]; exact RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q (Tn k : ℝ)
  have hslabK := hslabK_of_tds_HND hanti hder ind c hc (fun n => (Tn n : ℝ))
  obtain ⟨-, hderF0⟩ := GC.LongTime.Ch11.hkernelDtT_of_supply_P6KT hder le_rfl hanti
    q.neckRadius_pos ind c hc (fun n => (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹)
    (fun n => c n * (Tn n : ℝ)) (fun _ => le_rfl)
  have hTc : ∀ n, c n * (Tn n : ℝ) / c n = (Tn n : ℝ) := fun n =>
    mul_div_cancel_left₀ _ (hc n).ne'
  have hQe : ∀ n, c n * (q.neckRadius (c n * (Tn n : ℝ)) ^ 2)⁻¹ =
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    (RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q (Tn n : ℝ)).symm
  have hderF : ∀ n (hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
      (((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore Ctime
      ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹
      (min (K n).horizon (Tn n : ℝ)) := fun n hK => by
    have h := hderF0 n hK
    beta_reduce at h
    rw [hQe n, hTc n] at h
    exact h
  have hQp : ∀ n : ℕ,
      0 < ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n =>
    inv_pos.mpr (pow_pos ((q.rescale_P6N (c n) (hc n)).neckRadius_pos _ (Tn n).2.1) 2)
  have hn1 : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) + 1 := fun n => by positivity
  have hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ / c n) x ∧
      -3 / (a₀ / c n) ≤ metricScalarAt ((K n).initialMetric 0) x :=
    fun n => (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (hHI0 (ind n))
  have hscaleK : ∀ (n : ℕ) i hi b, max ((n : ℝ) + 1) (NfT n) *
      max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
      (((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale := by
    intro n i hi b
    have h7 : ∀ i hi b, max ((n : ℝ) + 1) (NfT n) * max (((n : ℝ) + 1) / c n)
        (q.neckRadius (Tno n) ^ 2)⁻¹ ≤ ((recordsK n i hi).static b).neck.scale := fun i hi b => by
      have h := hJ7b n i hi b
      change max ((n : ℝ) + 1) (NfT n) * max (((n : ℝ) + 1) / c n)
        (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) ≤ _ at h
      rwa [← max_assoc, max_self] at h
    have h := (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n)
      (A := max ((n : ℝ) + 1) (NfT n)) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n) ^ 2)⁻¹)
      h7 i hi b
    rwa [← hρK n] at h
  exact hprod hC1 hC1 hCt σ y hfin (fun k => Subtype.coe_le_coe.mpr (hsT k))
    (Q := fun n => ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (T₀ := fun n => max 1 (c n * (aSeed n : ℝ) / c n))
    (p := fun n => (p n).rescale_P6N (c n) (hc n))
    (pF := fun n => q.rescale_P6N (c n) (hc n))
    (recordsK := fun n i hi => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi)
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := fun n => a₀ / c n) hHIK
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n))
    (fun n i hi => (Ho n).hδF_rescale_P6X3 (hc n) (fun i' hi' => hδp n i' ((hT₀l n).trans hi'))
      i hi)
    hacc hrad hord hQp (fun n j => hslabK n j) hderF
    (fun n i hi b => (mul_le_mul (le_max_right _ _) (le_max_right _ _) (hQp n).le
      ((hn1 n).trans (le_max_left _ _))).trans (hscaleK n i hi b))
    (fun n i hi b => (Ho n).hbirthA_rescale_P6X3 (hc n) (recordsK n) (hJ8 n) i hi b) hsel n yG' hyG

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
