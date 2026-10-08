import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDProtCP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStayCXP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalSlabCeilingCXJF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVFinalP6HF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGood_P6L3

/-!
# SLTPROD c⋆ stay 与 SB2 cap ceiling 的 final slab 版（A1 续 HARNACK，供 G9SHIFT G9″，后缀 `_P6HK`）

* `ObservedHistory.stay_cstar_final_P6HK`（PROVED）：SLTPROD `stay_cstar_of_firstExit_P6SP` 逐字，`H :
  ObservedHistory`
  → `KH : RetainedCoreHistory`（`KH.toHistory`），`hσlast : activeStage σ < last` → `hσH : σ <
  horizon`，
  核 `hstop_of_firstExit_CXJD` → CX-J10FIN `hstop_final_CXJF`。σ 可在 final slab；final 中心的 "prefix 版"
  就是本条（final 中心的 trace 已是全 history trace，不需要 `prefixAt`）。
* `ObservedHistory.capCeiling_of_firstExit_sep_final_P6HK`（PROVED）：SB2
  `capCeiling_of_firstExit_sep_P6SB2` 逐字，
  中心 `(j n, t n)` event → final slab（`hfin`、`time last < t n < horizon`、`yG` 在 last stage、`hRn` 用
  restrict final
  slab 标量），`hprotC_of_ceiling_guarded_P6SB2` → `hprotC_gen_of_ceiling_CXJF`，CXJD ceiling → CXJF
  final ceiling；
  `hsepT` / `hsep4` / 结论里的 `i⁺ ≤ (j n)⁺` → `i⁺ ≤ last`。
* `RetainedCoreHistory.activeStage_eq_succ_final_P6HK`：辅助。
无新 binder。生成器 `build-logs/scratch/O-CH11-HARNACK/gen2/g5.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- final 版 `activeStage_eq_succ_P6SB`（`_P6HK`）：`a = time i⁺` ⇒ `activeStage a = i⁺`（`i⁺` 可为
  last）。 -/
theorem RetainedCoreHistory.activeStage_eq_succ_final_P6HK (K : RetainedCoreHistory.{u})
    (i : Fin K.eventCount) (a : Icc (0 : ℝ) K.toHistory.horizon) (ha : (a : ℝ) = K.time i.succ) :
    K.toHistory.activeStage a = i.succ := by
  rcases Fin.eq_castSucc_or_eq_last i.succ with ⟨e2, he2⟩ | hl
  · have hlt : K.toHistory.time e2.castSucc < K.toHistory.time e2.succ :=
      K.toHistory.time_strictMono e2.castSucc_lt_succ
    rw [he2]
    refine K.toHistory.activeStage_eq_of_slab_P6L3 e2 a ?_ ?_
    · rw [ha, ← he2]
    · rw [ha]
      change K.toHistory.time i.succ < _
      rw [he2]
      exact hlt
  · rw [hl]
    exact K.toHistory.activeStage_eq_last_of_time_last_le a (by rw [ha, ← hl])

/-- **SLTPROD c⋆ stay，final 版（`_P6HK`）**：`stay_cstar_of_firstExit_P6SP` 逐字，换帧见文件头。 -/
theorem ObservedHistory.stay_cstar_final_P6HK {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (KH : RetainedCoreHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn) {pT :
        (KH.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
        (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t) (a₀ +
          t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR :
        0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσH : (σ : ℝ) < KH.toHistory.horizon)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hRa : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (hQbdef : Qb = max (max (metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage
        σ) σ) z / R) Cg) 1)
    (hTdef : T = 1 / (2 * max (Ctime' : ℝ) 1) / Qb)
    (hguard : ((σ : ℝ) - a) *
        max (Cg * R) (metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z) ≤
      1 / (2 * max (Ctime' : ℝ) 1))
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage
        σ) (KH.toHistory.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
        GeometricCutoffRecord KH.toHistory e q)
    (hOld : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin KH.toHistory.eventCount) (h1 : KH.toHistory.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ KH.toHistory.activeStage Tn) (h3 : KH.toHistory.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ KH.toHistory.activeStage σ) (he : T₀ ≤ KH.toHistory.time e.succ),
        (∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), KH.toHistory.time
            e.succ ≤ (v : ℝ) →
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
              (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono
                  (haS.trans hav))
                (KH.toHistory.activeStage_mono (hvσ.trans hσT)))
              (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
                  (KH.toHistory.activeStage_mono hvσ)) <
            riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
                (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                  (KH.toHistory.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hzy : z ∈ riemannianBallOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y (D /
        Real.sqrt R))
    (hdσ : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
          (KH.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
          (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono (haS.trans
              hav))
            (KH.toHistory.activeStage_mono ((hvt.trans le_rfl).trans hσT)))
          (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono hvt)) ≤
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
            (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
              (KH.toHistory.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / Real.sqrt R) := by
  generalize hRz : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z =
      Rz at hQbdef hguard
  have hCgR : R ≤ Cg * R := by nlinarith
  have hQbM : Qb * R ≤ max (Cg * R) Rz := by
    have hle : Qb ≤ max (Cg * R) Rz / R := by
      rw [hQbdef]
      refine max_le (max_le ?_ ?_) ?_
      · exact div_le_div_of_nonneg_right (le_max_right _ _) hR.le
      · rw [le_div_iff₀ hR]
        exact le_max_left _ _
      · rw [le_div_iff₀ hR, one_mul]
        exact hCgR.trans (le_max_left _ _)
    calc Qb * R ≤ max (Cg * R) Rz / R * R := mul_le_mul_of_nonneg_right hle hR.le
      _ = max (Cg * R) Rz := div_mul_cancel₀ _ hR.ne'
  have hQb1 : (1 : ℝ) ≤ Qb := by
    rw [hQbdef]
    exact le_max_right _ _
  have hQbpos : 0 < Qb := by linarith
  have hm1 : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hdepth : (σ : ℝ) - a ≤ T / R := by
    rw [hTdef, div_div, le_div_iff₀ (mul_pos hQbpos hR)]
    have hsa : 0 ≤ (σ : ℝ) - a := sub_nonneg.mpr (show (a : ℝ) ≤ σ from haσ)
    exact (mul_le_mul_of_nonneg_left hQbM hsa).trans hguard
  have hstep : 2 * (Ctime' : ℝ) * Qb * T ≤ 1 := by
    have hT : 2 * (Ctime' : ℝ) * Qb * T = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [hT, div_le_one hm1]
    exact le_max_left _ _
  have hQb : max (max (Rz / R) Cg) 1 ≤ Qb := le_of_eq hQbdef.symm
  have hz : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Rz / R *
      R := by
    rw [div_mul_cancel₀ _ hR.ne', hRz]
  exact hstop_final_CXJF hC2 KH haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb
    hstep haS haσ hσH haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hacc
    hDm hprotC hzy hdσ hnum

/-- **cap 出生时刻 ceiling，final 中心（`_P6HK`）**：`capCeiling_of_firstExit_sep_P6SB2` 逐字，换帧见文件头。 -/
theorem ObservedHistory.capCeiling_of_firstExit_sep_final_P6HK
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon) {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htj : ∀ n, t n < (K n).horizon) (σ
        : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀ : ℕ → ℝ) (hT₀ : ∀ n, T₀ n ≤ aSeed n)
    (hOld : ∀ n (e : Fin (K n).eventCount), T₀ n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {θ₀ : ℝ} {T₀K : ℕ → ℝ} {pK : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (pK n))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hθ₀ : 0 < θ₀) (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (haccK : ∀ n : ℕ, (pK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hradK : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (pK n).modelRadius)
    (hordK : ∀ n : ℕ, n + 2 ≤ (pK n).modelOrder)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (Fin.last (K n).eventCount))
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      metricScalarAt ((K n).toHistory.event i).outputMetric (A.point i.succ le_rfl hl) ≤
        2 * (max (max 1 Cg) 1 * R n) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm0 : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [le_max_right (Ctime' : ℝ) 1]
  set Qb : ℝ := max (max 1 Cg) 1 with hQbdef
  have hQb1 : 1 ≤ Qb := le_max_right _ _
  have hQb0 : 0 < Qb := by linarith
  set T : ℝ := 1 / (2 * max (Ctime' : ℝ) 1) / Qb with hTdef
  have hT0 : 0 < T := div_pos (by positivity) hQb0
  have hT1 : T ≤ 1 := (div_le_one hQb0).2 (hc1.trans hQb1)
  have hstep : 2 * (Ctime' : ℝ) * Qb * T ≤ 1 := by
    have h1 : 2 * (Ctime' : ℝ) * Qb * T = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [h1]
    exact (div_le_one hm0).2 (le_max_left _ _)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hTE := hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)
  have hr6 := hnat.eventually_ge_atTop (6 / r ^ 2)
  have hacE : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ min ε₀ (1 / 2) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds (lt_min hε₀ (by norm_num)))
  filter_upwards [hwin T hT0, hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (1 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1), hTE, hr6, hacE]
    with n hwn hLn hTEn hr6n hacn
  intro i hi hl A b hage
  have hsc : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL5 : 2 * (1 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  -- 深度：年龄 ≤ θ₀/scale 且 θ₀·R ≤ T·scale ⇒ σ − time i⁺ ≤ T/R
  have hsep := hsepT n i hi b hl hage
  have hdep : t n - (K n).time i.succ ≤ T / R n := by
    rw [le_div_iff₀ (hR n)]
    have h1 := mul_le_mul_of_nonneg_right hage (hR n).le
    have h2 : θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ * R n =
        θ₀ * R n / ((recordsK n i hi).static b).neck.scale := by
      field_simp
    have h3 : θ₀ * R n / ((recordsK n i hi).static b).neck.scale ≤ T := by
      rw [div_le_iff₀ hsc]
      exact hsep
    linarith
  have htle : (K n).time i.succ ≤ (K n).time (Fin.last (K n).eventCount) :=
    (K n).time_strictMono.monotone hl
  have hσt : (σ n : ℝ) = t n := hσ n
  have hjσ : (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) := by rw [hσt]; exact hjt n
  have hTR : T / R n ≤ 1 / R n := div_le_div_of_nonneg_right hT1 (hR n).le
  have haSr : (aSeed n : ℝ) ≤ (K n).time i.succ := by linarith
  let a : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨(K n).time i.succ, (aSeed n).2.1.trans haSr,
      (by linarith : (K n).time i.succ ≤ (σ n : ℝ)).trans (σ n).2.2⟩
  have haval : (a : ℝ) = (K n).time i.succ := rfl
  have haS : aSeed n ≤ a := haSr
  have haσ : a ≤ σ n := show ((K n).time i.succ : ℝ) ≤ σ n by linarith
  have hdepth : (σ n : ℝ) - a ≤ T / R n := by rw [haval, hσt]; exact hdep
  have hLR : 1 / R n ≤ L n ^ 2 / R n :=
    div_le_div_of_nonneg_right (by nlinarith) (hR n).le
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ a := by linarith
  have hRa' : 1 ≤ R n * a := by
    have := mul_le_mul_of_nonneg_left haSr (hR n).le
    rw [haval]
    linarith [hRa n]
  have hact_a : (K n).toHistory.activeStage a = i.succ :=
    (K n).activeStage_eq_succ_final_P6HK i a haval
  have hact_σ : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) hjσ.le
  have hσH : (σ n : ℝ) < (K n).toHistory.horizon := hσt.trans_lt (htj n)
  obtain ⟨A', hA'⟩ := trace_transport_both_P6SB ((K n).toHistory.activeStage_mono haσ) (y n)
    hact_a.symm hact_σ.symm (hyG n).symm A
  have hz : metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
      (y n) ≤ 1 * R n := by
    rw [(K n).scalar_stage_eq_last_P6HF (hfin n) hact_σ (σ n) (y n) (yG n) (hyG n), hσt, ← hRn n,
      one_mul]
  have hzy : y n ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (1 / Real.sqrt (R n)) := by
    change riemannianEDistOf _ (y n) (y n) < ENNReal.ofReal (1 / Real.sqrt (R n))
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos one_pos (Real.sqrt_pos.mpr (hR n)))
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP
    (Qb := Qb) (R := R n) (Rad := 1) (L := L n) hr hρ hc0 hQb1 (hR1 n) hκdef (by linarith)
    (by linarith)
  have hQb : max (max 1 Cg) 1 ≤ Qb := le_rfl
  -- kernel records 限制到 `time i⁺` 之后
  let rec' : ∀ e : Fin (K n).eventCount, (a : ℝ) ≤ (K n).toHistory.time e.succ →
      GeometricCutoffRecord (K n).toHistory e (pK n) := fun e he => recordsK n e (hi.trans he)
  have hOld' : ∀ e : Fin (K n).eventCount, (a : ℝ) ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore :=
    fun e he => hOld n e ((hT₀ n).trans (haSr.trans he))
  have hcan' : ∀ (e : Fin (K n).eventCount) (he : (a : ℝ) ≤ (K n).toHistory.time e.succ) b,
      ((rec' e he).static b).hasCanonicalWindow := fun e he b => hcanK n e (hi.trans he) b
  have hacc1 : (pK n).modelAccuracy ≤ min ε₀ (1 / 2) := (haccK n).trans hacn
  have hDm' : StandardCap.transitionEnd + 10 < (pK n).modelRadius := by linarith [hradK n]
  have hnc' := hnc0 (H := (K n).toHistory) (q := pK n) (T₀ := (a : ℝ)) rec'
    (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hordK n)) hcan'
  have hscale' : ∀ (e : Fin (K n).eventCount) (he : (a : ℝ) ≤ (K n).toHistory.time e.succ) b,
      (a : ℝ) < (K n).toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((rec' e he).static b).neck.scale := by
    intro e he b' hae
    have hej : e.succ ≤ Fin.last (K n).eventCount := Fin.le_last _
    have hse : 0 < ((rec' e he).static b').neck.scale := ((rec' e he).static b').neck.scale_pos
    have hM : 2 * (2 * (Qb * R n)) < ((rec' e he).static b').neck.scale :=
      lt_scale_of_age_dichotomy_P6SB2 hθ₀ hsc hse (by linarith) hage
        (hsep4 n i hi b hl hage) (hsep4 n e (hi.trans he) b' hej)
    have hRQ : R n ≤ Qb * R n := le_mul_of_one_le_left (hR n).le hQb1
    have h6 : 2 * (3 / r ^ 2) < ((rec' e he).static b').neck.scale := by
      have := hRlt n
      have h63 : 2 * (3 / r ^ 2) = 6 / r ^ 2 := by ring
      linarith
    have hmx : max (3 / r ^ 2) (2 * (Qb * R n)) < ((rec' e he).static b').neck.scale / 2 :=
      max_lt (by linarith) (by linarith)
    linarith
  have hL0 : 0 ≤ L n := by linarith
  have hprotC' := ObservedHistory.hprotC_gen_of_ceiling_CXJF (K n) (haT n)
    (hsmall n) (hclock n) (seedTrace n) (hsT n) (has n) (y n) (L n) (hR n) hL0 (hgood n) hQb hstep
    haS haσ haL hdepth hz A' rec' hDm' hnc' hscale'
  have hceil := ObservedHistory.scalar_le_two_mul_finalSlab_ceiling_CXJF (Cball := 1) (Qb := Qb)
    (T := T) (K := Qb * R n / κ ^ 2) (ℓ := κ / Real.sqrt (Qb * R n)) (D := 1) hC2
    (K n) (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n)
    (y n) (L n) (hR n) (hgood n) hQb hstep haS haσ hσH haL hdepth hRa' hz A' hℓ hKℓ hℓr hKr
    hKC hℓρ hρL le_rfl rec' hOld' hcan' (hacc1.trans (min_le_right _ _)) hDm' hprotC' hzy
    (hdσ n) hnum a le_rfl haσ
  have hpt := hA' i.succ ((K n).toHistory.activeStage a) hact_a.symm le_rfl hl
    ((K n).toHistory.activeStage_mono (le_refl a)) ((K n).toHistory.activeStage_mono haσ)
  rw [scalar_output_of_stage_P6SB (K n).toHistory i hact_a _ _ hpt] at hceil
  exact hceil

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
