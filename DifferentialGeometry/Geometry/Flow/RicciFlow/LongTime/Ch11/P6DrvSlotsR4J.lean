import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TailR4J

/-!
# R4J10 G2：R4 中心 `(t, y′)` 的 J10 槽桥（`_R4J`）

HTRSPAY 的 R4 帧 driver（`P6R4DriverGateHTP`）残余 `hsurvive` / `hextend` 的中心是 `(t, y′)`，`t ↑ σ`，
`y′ ≍ p′`，归一化 `R` 是崩点 `(σ, y)` 的标量，`R/2 < R_c < 2R`，`R_c := scalar(t, y′)`。

* G0 结论：`J10Blk_JT`（= `drvSlots_K_of_J10_sepT_HSX` 结论）与 `j10Blk_of_tail_*` 对 K 帧 event 内部中心
  泛型。故不新写 `J10ResE_RX_R4J`：残余沿用 hres 侧同形（`J10ResE3_JT` + `0 < a₀K` + `∀ᶠ hT₀X` + DrvResE
  同元组 K 帧数据包），中心取 `K := rescale tower`、`σ := t`、`yK := y′`、`R := R_c`。
* `drvSlots_Rc_of_J10_R4J`：R4 帧数据（`hgood′`、`hclose`、`hcmp` / `hcmpL`、seed、`hslab`）对齐到
  K 帧 `R_c` 形（假设方向 ratio-2 可吸收：`Cg := 8`、`L_J := max (L - 2) 0 / √2`、`T ↦ 2T + 1`、`C ↦ 2C`）
  ⇒ `J10Blk_JT K t y′ R_c`，即 `R_c` 归一化的 R4 槽孪生 `∃ Cst, hsurvive ∧ hextend`。
* `drvSlots_R4_of_J10_R4J`：同上加 `R = R_c`（`hReq`），结论为 R4 槽归一化 `R` 的逐字形。
  不带 `hReq` 的逐字形不可推：槽假设球 `ball(y′, A/√R)` 与结论球方向相反（见 DELIVERIES 块）。
无新顶层 binder；不假设 `hqR`。
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

/-- **R4 中心标量（`_R4J`，缩写 def）**：`R_c n := scalar(t n, y′ n)`（K 帧）。 -/
def centerScalar_R4J (K : ℕ → RetainedCoreHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y' : ∀ n, ((K n).toHistory.stageAt (t n)).Carrier) (n : ℕ) : ℝ :=
  metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (t n)) (t n)) (y' n)

/-- **R4 中心槽桥（`_R4J`，PROVISIONAL[K 帧数据包 + `J10ResE3_JT` + `0 < a₀K` + `∀ᶠ hT₀X`]）**：
R4 帧数据（`hgood′`、`hclose`、`hcmp` / `hcmpL`、seed、`hslab`）+ hres 侧同形残余 ⇒
`J10Blk_JT K t y′ R_c`。见文件头。 -/
theorem drvSlots_Rc_of_J10_R4J {K : ℕ → RetainedCoreHistory.{u}}
    {Ctime : ℝ≥0} {ε C1 C2 : ℝ} (hC2 : 0 ≤ C2)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder)
    {pF : ℕ → CutoffParameters}
    (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Q a₀K : ℕ → ℝ}
    (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
      -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthAK : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (hslabT : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time i.succ) (Tn n : ℝ)))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) (h1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (hsm : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) 1)
    (σ t : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y' : ∀ n, ((K n).toHistory.stageAt (t n)).Carrier) {R : ℕ → ℝ} {L : ℕ → ℝ}
    (hsT : ∀ n, σ n ≤ Tn n) (hat : ∀ n, aSeed n ≤ t n) (hts : ∀ n, t n ≤ σ n)
    (hRpos : ∀ n, 0 < R n) (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (hL : Tendsto L atTop atTop)
    (i : ∀ n, Fin (K n).eventCount)
    (hslab : ∀ n, (K n).time (i n).castSucc < (t n : ℝ) ∧ (t n : ℝ) < (K n).time (i n).succ)
    (hclose : ∀ n, (σ n : ℝ) - t n ≤ 1 / R n)
    (hcmp : ∀ n, centerScalar_R4J K t y' n < 2 * R n)
    (hcmpL : ∀ n, R n / 2 < centerScalar_R4J K t y' n)
    (hTnS : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgood' : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v)
      (hvt : v ≤ t n), (t n : ℝ) - (L n - 2) ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvt.trans ((hts n).trans (hsT n))))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (t n)) (t n))
              ((seedTrace n).point ((K n).toHistory.activeStage (t n))
                ((K n).toHistory.activeStage_mono (hat n))
                ((K n).toHistory.activeStage_mono ((hts n).trans (hsT n)))) (y' n) +
            ENNReal.ofReal ((L n - 2) / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z →
        (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (t n)) (t n))
        ((seedTrace n).point ((K n).toHistory.activeStage (t n))
          ((K n).toHistory.activeStage_mono (hat n))
          ((K n).toHistory.activeStage_mono ((hts n).trans (hsT n)))) (y' n) ≠ ⊤)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (j : Fin (K n).eventCount) (hj : T₀K n ≤ (K n).time j.succ) b,
        (σ n : ℝ) - T / R n < (K n).time j.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recordsK n j hj).static b).neck.scale)
    (hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n)
    (ha₀ : ∀ n, 0 < a₀K n) (hT₀X : ∀ᶠ n in atTop, T₀K n ≤ (t n : ℝ) - (1 / 100 : ℝ) ^ 2)
    (h3 : J10ResE3_JT K t y' qK T₀K recordsK) :
    J10Blk_JT K t y' (centerScalar_R4J K t y') := by
  have hRcpos : ∀ n, 0 < centerScalar_R4J K t y' n := fun n =>
    lt_trans (half_pos (hRpos n)) (hcmpL n)
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hRr n]) tendsto_natCast_atTop_atTop
  have hRclim : Tendsto (centerScalar_R4J K t y') atTop atTop :=
    tendsto_atTop_mono (fun n => (hcmpL n).le) (hRlim.atTop_div_const (by norm_num))
  -- T / R_c ≤ 2 T / R
  have hdiv : ∀ n (T : ℝ), 0 < T → T / centerScalar_R4J K t y' n ≤ 2 * T / R n := by
    intro n T hT
    rw [div_le_div_iff₀ (hRcpos n) (hRpos n)]
    have := hcmpL n
    nlinarith [mul_pos hT (hRpos n)]
  have hsepc : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (j : Fin (K n).eventCount) (hj : T₀K n ≤ (K n).time j.succ) b,
        (t n : ℝ) - T / centerScalar_R4J K t y' n < (K n).time j.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * centerScalar_R4J K t y' n) <
          ((recordsK n j hj).static b).neck.scale := by
    intro T hT C hC
    filter_upwards [hsep (2 * T + 1) (by linarith) (2 * C) (by linarith)] with n hn j hj b hlt
    refine lt_of_le_of_lt ?_ (hn j hj b ?_)
    · refine mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) (by norm_num)
      calc C * centerScalar_R4J K t y' n ≤ C * (2 * R n) :=
            mul_le_mul_of_nonneg_left (hcmp n).le hC
        _ = 2 * C * R n := by ring
    · have h2 := hdiv n T hT
      have h3' := hclose n
      have h4 : (2 * T + 1) / R n = 2 * T / R n + 1 / R n := add_div _ _ _
      linarith
  have hT₀Kc : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      T₀K n ≤ (t n : ℝ) - T / centerScalar_R4J K t y' n := by
    intro T hT
    filter_upwards [hT₀K (2 * T + 1) (by linarith)] with n hn
    have h2 := hdiv n T hT
    have h3' := hclose n
    have h4 : (2 * T + 1) / R n = 2 * T / R n + 1 / R n := add_div _ _ _
    linarith
  have hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ t n := by
    filter_upwards [hTnS 1 one_pos] with n hn
    have h3' := hclose n
    linarith
  obtain ⟨LJ, hLJ⟩ : ∃ LJ : ℕ → ℝ, ∀ m, LJ m = max (L m - 2) 0 / Real.sqrt 2 :=
    ⟨_, fun _ => rfl⟩
  have hLJlim : Tendsto LJ atTop atTop := by
    have h1' : Tendsto (fun m => L m - 2) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-2 : ℝ) hL
    have h2' : Tendsto (fun m => max (L m - 2) 0) atTop atTop :=
      tendsto_atTop_mono (fun m => le_max_left _ _) h1'
    have h3' := h2'.atTop_div_const (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
    exact h3'.congr (fun m => (hLJ m).symm)
  have hgoodK : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v)
      (hvs : v ≤ t n), (t n : ℝ) - LJ n ^ 2 / centerScalar_R4J K t y' n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans ((hts n).trans (hsT n))))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (t n)) (t n))
              ((seedTrace n).point ((K n).toHistory.activeStage (t n))
                ((K n).toHistory.activeStage_mono (hat n))
                ((K n).toHistory.activeStage_mono ((hts n).trans (hsT n)))) (y' n) +
            ENNReal.ofReal (LJ n / Real.sqrt (centerScalar_R4J K t y' n)) →
        (8 : ℝ) * centerScalar_R4J K t y' n ≤
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z →
        (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z := by
    intro n v hav hvs hwin z hd hsc
    have hRn := hRpos n
    have hcn := hcmp n
    have hcl := hcmpL n
    have hRcn := hRcpos n
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hwin' : (t n : ℝ) - (L n - 2) ^ 2 / R n ≤ (v : ℝ) := by
      refine le_trans ?_ hwin
      have hm : (max (L n - 2) 0) ^ 2 ≤ (L n - 2) ^ 2 := by
        rcases le_total (L n - 2) 0 with h | h
        · rw [max_eq_right h]; nlinarith [sq_nonneg (L n - 2)]
        · rw [max_eq_left h]
      have hq : LJ n ^ 2 = (max (L n - 2) 0) ^ 2 / 2 := by
        rw [hLJ n, div_pow, hs2]
      have key : LJ n ^ 2 / centerScalar_R4J K t y' n ≤ (L n - 2) ^ 2 / R n := by
        rw [hq, div_div, div_le_div_iff₀ (by positivity) hRn]
        nlinarith [mul_le_mul_of_nonneg_right hm hRn.le,
          mul_nonneg (sq_nonneg (L n - 2)) (sub_nonneg.2 hcl.le)]
      linarith
    have hdist : ENNReal.ofReal (LJ n / Real.sqrt (centerScalar_R4J K t y' n)) ≤
        ENNReal.ofReal ((L n - 2) / Real.sqrt (R n)) := by
      rw [hLJ n]
      rcases le_total (L n - 2) 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_div, div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 hRn)]
        have hsq : Real.sqrt (R n) ≤ Real.sqrt 2 * Real.sqrt (centerScalar_R4J K t y' n) := by
          rw [← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt (by linarith)
        exact mul_le_mul_of_nonneg_left hsq h
    refine hgood' n v hav hvs hwin' z (le_trans hd (add_le_add le_rfl hdist)) (by linarith)
  exact j10Blk_of_tail_R4J (σ := t) (yK := y') (R := centerScalar_R4J K t y') (Ctime := Ctime)
    (ε := ε) (C1 := C1) (C2 := C2) (Cg := 8) hC2 hcanK hacc hrad hord hT₀Kc recordsFK hδFK hphi
    hHIK hscaleK hbirthAK hpinchK Tn aSeed haT (fun n => (hts n).trans (hsT n)) hat pT seedTrace
    hslabT hclock h1 hsm hhalf (L := LJ) hLJlim hgoodK (fun _ => rfl) hRcpos hRclim
    (hRclim.eventually_ge_atTop 1) hfinK hsepc (fun n => ⟨i n, hslab n⟩) ha₀ hT₀X h3

/-- **R4 逐字槽桥（`_R4J`，PROVISIONAL[同 `drvSlots_Rc_of_J10_R4J` + `hReq`]）**：
`drvSlots_Rc_of_J10_R4J` 再加 `R = R_c`（`hReq`）⇒ `J10Blk_JT K t y′ R`，即 R4 槽（归一化 `R`）
`∃ Cst, hsurvive ∧ hextend` 逐字。`hReq` 在 R4 `hcmp` / `hcmpL` 的 ratio-2 下一般不成立
（GAP-WITNESS：槽假设球与结论球方向相反）。 -/
theorem drvSlots_R4_of_J10_R4J {K : ℕ → RetainedCoreHistory.{u}}
    (t : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y' : ∀ n, ((K n).toHistory.stageAt (t n)).Carrier) {R : ℕ → ℝ}
    (hReq : ∀ n, R n = centerScalar_R4J K t y' n)
    (h : J10Blk_JT K t y' (centerScalar_R4J K t y')) :
    J10Blk_JT K t y' R := by
  have hfun : R = centerScalar_R4J K t y' := funext hReq
  rw [hfun]
  exact h

/-- consumer。 -/
example : True := by
  have := @drvSlots_Rc_of_J10_R4J.{0}
  have := @drvSlots_R4_of_J10_R4J.{0}
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
