import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAlignedP6SB3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStaySeqP6SP

/-!
# guarded 槽的 producer：同 slab c⋆ stay 付 hder / hgrad / hnc（O-CH11-BCBD-A2 G5，后缀 `_A2B`）

G4 的 guarded 核只在逐点短窗 `(t − v)·max(Cg·R, R(t, x)) ≤ c⋆` 上要 hder / hgrad / hnc。本文件给 G9″ 帧的 producer，
**不用 `hdistW`**：
* `hdistWStar_of_firstExit_A2B`（PROVED ⇐ hgood + CXJD 结构输入族）：
  SLTPROD G3 `stay_cstar_of_firstExit_P6SP` 的同 slab 实例（`hprotC` 空真），结论 = G9″ `hdistW` 体加同一 guard；
* `hderSelG_… / hgradG_… / hkappaSG_… / tested_kappaG_…`、
  `hnc_window_sameStageG_… / hnc_window_of_freshG_…`
  （PROVED ⇐ 槽前提）：原 producer 逐字（生成器断言替换），`hdistW` 换 guarded 形，结论加 guard。
生成器 `build-logs/scratch/O-CH11-BCBD-A2/gen/gen5.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **同 slab c⋆ stay ⇒ guarded `hdistW⋆`（`_A2B`，PROVED ⇐ CXJD 结构输入族）**：SLTPROD G3
`stay_cstar_of_firstExit_P6SP`（任意 trace）在 `activeStage v = activeStage σ` 时取用，`hprotC` 空真
（不存在 `activeStage v ≤ e⁻ < e⁺ ≤ activeStage σ`）；records 取 `T₀′ := max T₀ T₀X`；数值同 G3c
`cstar_numerics_P6SP`。结论 = G9″ `hdistW` 体加 c⋆ guard `(σ − v)·max(Cg·R, R(σ, x)) ≤ c⋆`。 -/
theorem ObservedHistory.hdistWStar_of_firstExit_A2B {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
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
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (K n).eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  intro Rad B _ _
  filter_upwards [hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1), hT₀ B,
    hnat.eventually_ge_atTop 2, hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)]
    with n hLn hT₀n hn2 hnD
  intro x hx v hav hvs hBv hst hg tr
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hL5 : 2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6SB (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  have hσlast : (K n).toHistory.activeStage (σ n) < Fin.last (K n).toHistory.eventCount := by
    rw [hσact]
    exact Fin.castSucc_lt_last _
  have hsv0 : 0 ≤ (σ n : ℝ) - v := sub_nonneg.mpr (show (v : ℝ) ≤ σ n from hvs)
  have hRle : ((σ n : ℝ) - v) * R n ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_left ((show R n ≤ Cg * R n by nlinarith [hR n]).trans
      (le_max_left (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n)) x))) hsv0
    linarith
  have hTv : (σ n : ℝ) - v ≤ 1 / R n := by
    rw [le_div_iff₀ (hR n)]
    exact hRle
  have hLR : 1 / R n ≤ L n ^ 2 / R n :=
    div_le_div_of_nonneg_right (by nlinarith) (hR n).le
  have haL : (σ n : ℝ) - L n ^ 2 / R n ≤ v := by linarith
  have hav' : (aSeed n : ℝ) ≤ v := hav
  have hRa' : 1 ≤ R n * v := by
    have := mul_le_mul_of_nonneg_left hav' (hR n).le
    linarith [hRa n]
  have hT₀' : max (T₀ n) (T₀X n) ≤ (v : ℝ) :=
    max_le (hT₀n.trans hBv) ((hT₀X n).trans hav')
  have hacc' : (p n).modelAccuracy ≤ 1 / 2 := by
    refine (hacc n).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hDm : StandardCap.transitionEnd + 10 < (p n).modelRadius := hnD.trans_le (hrad n)
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP
    (Qb := max (max (metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) x / R n) Cg) 1)
    (R := R n) (Rad := Rad) (L := L n) hr hρ hc0 (le_max_right _ _) (hR1 n) hκdef (by linarith)
    (by linarith)
  exact ObservedHistory.stay_cstar_of_firstExit_P6SP hC2 hCg (K n).toHistory (haT n) (hsmall n)
    (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n) (L n) (hR n) (hgood n) hav hvs
    hσlast haL hRa' rfl rfl hg tr hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀'
    (fun e he => recordsK n e ((le_max_left _ _).trans he))
    (fun e he => hOldX n e ((le_max_right _ _).trans he))
    (fun e he b => hcanK n e _ b) hacc' hDm
    (fun e _ _ h3 h4 _ _ b => absurd (h4.trans (hst ▸ h3)) (not_le.mpr e.castSucc_lt_succ))
    hx (hdσ n) hnum v le_rfl hvs


/-- **guarded `hder` 槽（`_A2B`，PROVED ⇐ hgood + `hdistWG`）**：
`hderSel_of_selection_sameSlab_Cg_P6JG3` 逐字，`hdistW` 与结论都加 c⋆ guard。 -/
theorem ObservedHistory.hderSelG_of_selection_sameSlab_Cg_A2B
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
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
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistWG : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x) (Iic v) v| ≤
        (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdistWG (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq hg
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon :=
    (hv.2.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) v' hv.1.le (hv.2.trans (htj n))
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_of_incoming_P6JG3H (j n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6JG3H (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hav : aSeed n ≤ v' := hw.trans hBv'
  have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - max B 1 / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_of_incoming_P6JG3H (j n) hvact.symm v x _ hptx
  have hg' : ((σ n : ℝ) - v') * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) x') ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    rw [(K n).scalar_of_incoming_P6JG3H (j n) hσact.symm (σ n) x x' hxx, hσ n]
    exact hg
  have hgoodv := hgood n v' hav hvt (hLθ.trans hBv') _
    (hd x' hx' v' hav hvt hBv' (hvact.trans hσact.symm) hg' tr) (by rw [hsc']; exact hq.le)
  have hvh : v < (K n).toHistory.horizon :=
    (hv.2.trans (htj n)).trans_le ((K n).toHistory.time_le_horizon_at (j n).succ)
  have htv : (K n).toHistory.time ((K n).toHistory.activeStage v') < (v' : ℝ) := by
    rw [hvact]
    exact hv.1
  exact (K n).deriv_of_stage_P6JG3H (j n) hvact.symm v x _ hptx (hgoodv.2 htv hvh)

/-- **guarded `hgrad` 槽（`_A2B`，PROVED ⇐ hgood + `hdistWG`）**：
`hgrad_of_selection_sameSlab_Cg_P6CD` 逐字，`hdistW` 与结论都加 c⋆ guard。 -/
theorem ObservedHistory.hgradG_of_selection_sameSlab_Cg_A2B
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
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
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistWG : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential ((K n).toHistory.event (j n)).incoming.flow v x w| ≤
          (C2'.toNNReal : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x *
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar v x) *
            Real.sqrt
              ((((K n).toHistory.event (j n)).incoming.flow.base.metric v).inner x w w) := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdistWG (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq hg w
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon :=
    (hv.2.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) v' hv.1.le (hv.2.trans (htj n))
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_of_incoming_P6JG3H (j n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6JG3H (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hav : aSeed n ≤ v' := hw.trans hBv'
  have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - max B 1 / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_of_incoming_P6JG3H (j n) hvact.symm v x _ hptx
  have hg' : ((σ n : ℝ) - v') * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) x') ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    rw [(K n).scalar_of_incoming_P6JG3H (j n) hσact.symm (σ n) x x' hxx, hσ n]
    exact hg
  have hgoodv := hgood n v' hav hvt (hLθ.trans hBv') _
    (hd x' hx' v' hav hvt hBv' (hvact.trans hσact.symm) hg' tr) (by rw [hsc']; exact hq.le)
  have hW := (K n).witness_of_stage_P6JG3H (j n) hvact.symm v x _ hptx hgoodv.1
  obtain ⟨W, -⟩ := hW
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient w

/-- **guarded 同 stage trace-κ（`_A2B`，PROVED ⇐ FRESH + `hdistWG`）**：
`hkappaS_of_fresh_P6SB` 逐字加 guard。 -/
theorem ObservedHistory.hkappaSG_of_fresh_A2B {H : ℕ → ObservedHistory.{u}} {Cg : ℝ}
    {Ctime' : ℝ≥0}
    {nr : ℝ → ℝ} {Aκ κ Tκ r : ℝ}
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (H n))
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (H n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((H n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (H n) ((H n).activeStage (aSeed n))
      ((H n).activeStage (Tn n)) ((H n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((H n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (H n) (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((H n).stageMetric
      ((H n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
            ((H n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (H n).activeStage v = (H n).activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((H n).stageMetric
          ((H n).activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (σ n))
          ((H n).activeStage_mono hvs) x,
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage v) v)
            ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
              ((H n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
                ((H n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (H n).activeStage v = (H n).activeStage (σ n) →
      ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((H n).stageMetric
        ((H n).activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
        ((H n).activeStage (σ n)) ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r / 200 →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  intro D T hD hT
  filter_upwards [hdistW D T hD hT, hwinF T hT, hgate, hL.eventually_ge_atTop 0] with
    n hdW hwin hg hL0
  intro x hx v hvt hvT hst hgd tr r'' hr'' hr''le hball
  have hTv : (Tn n : ℝ) - r ^ 2 / 2 ≤ v := hwin.trans hvT
  have hav : aSeed n ≤ v := by
    change (aSeed n : ℝ) ≤ v
    rw [hclock n]
    have : 0 ≤ r ^ 2 := sq_nonneg r
    linarith
  have hvTn : v ≤ Tn n := hvt.trans (hsT n)
  have hd := hdW x hx v hav hvt hvT hst hgd tr
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hRpos n)
  have hlt : ENNReal.ofReal (L n / Real.sqrt (R n)) <
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hsR)]
    exact div_lt_div_of_pos_right (by linarith) hsR
  have hne : riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
        ((H n).activeStage_mono (hsT n))) (y n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hg)
  have hmem : tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt) ∈
      riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v)
        ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
          ((H n).activeStage_mono hvTn)) (Aκ * r) :=
    lt_of_le_of_lt hd ((ENNReal.add_lt_add_left hne hlt).trans_le hg)
  exact hWK n (Tn n) (pT n) r (hTκ n) (htimeS n) (hsmallS n) (hvolS n) (hnrS n) (aSeed n)
    (haT n) (hclock n) (seedTrace n) v hav hvTn hTv _ hmem r'' hr''.le (by linarith) hball

/-- **单 history 同 stage tested κ，guarded（`_A2B`，PROVED）**：
`tested_kappa_window_sameStage_P6SB` 逐字加 guard。 -/
theorem RetainedCoreHistory.tested_kappaG_window_sameStage_A2B (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {t : ℝ} (hjt : K.time j.castSucc < t) (htj : t < K.time j.succ)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ : (σ : ℝ) = t)
    (y : (K.toHistory.stageAt σ).Carrier) (yG : (K.stage j.castSucc).Carrier) (hyG : HEq y yG)
    {κ ρ Rad θ qg cg : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - θ ≤ v →
      K.toHistory.activeStage v = K.toHistory.activeStage σ →
      ((σ : ℝ) - v) * max qg (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
        x) ≤ cg →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρ →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'') :
    ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), t - θ ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) yG Rad,
      (t - τ) * max qg ((K.toHistory.event j).incoming.flow.scalar t z) ≤ cg →
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b) := by
  intro τ haτ hτt hjτ _ z hz hg zz hzz b hb hbρ hball
  have hσact : K.toHistory.activeStage σ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6SB j σ (by rw [hσ]; exact hjt.le) (by rw [hσ]; exact htj)
  have hτact : K.toHistory.activeStage τ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6SB j τ hjτ.le (hτt.trans_lt htj)
  have hvt : τ ≤ σ := show (τ : ℝ) ≤ σ by rw [hσ]; exact hτt
  let x : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hσact.symm) z
  have hxz : HEq x z := cast_heq _ _
  have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad :=
    K.mem_ball_incoming_P6SB j hσact.symm σ Rad z yG x y hxz hyG (by rw [hσ]; exact hz)
  obtain ⟨tr, htr⟩ := exists_trace_of_stage_eq_P6SB K.toHistory (hτact.trans hσact.symm)
    (K.toHistory.activeStage_mono hvt) x
  have hθ' : (σ : ℝ) - θ ≤ τ := by rw [hσ]; exact haτ
  have hpt : tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt) = zz :=
    eq_of_heq (htr.trans (hxz.trans hzz.symm))
  have hball' : K.toHistory.isParabolicallyRmControlledBall τ
      (tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt)) b := by
    rw [hpt]
    exact hball
  have hg' : ((σ : ℝ) - τ) * max qg (metricScalarAt (K.toHistory.stageMetric
      (K.toHistory.activeStage σ) σ) x) ≤ cg := by
    rw [K.scalar_of_incoming_P6JG3H j hσact.symm σ z x hxz, hσ]
    exact hg
  have h := hK x hx τ hvt hθ' (hτact.trans hσact.symm) hg' tr b hb hbρ hball'
  rw [hpt, ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **guarded kernel `hnc`（同 stage，`_A2B`，PROVED）**：`hnc_window_sameStage_P6SB` 加 guard；
证明对每个测试时刻 `T` 取 `U_T := {z ∈ 球 | guard(T, z)}`、窗口起点 `a := T` 调
`tested_noncollapse_eventPrefix_P6M`（guard 对 `τ ≥ T` 单调）。 -/
theorem ObservedHistory.hnc_window_sameStageG_A2B {K : ℕ → RetainedCoreHistory.{u}} {Cg : ℝ}
    {Ctime' : ℝ≥0} (hCg0 : 0 ≤ Cg)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
      ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (j n).castSucc).time
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) < T)
      (hTs : T < (K n).time (j n).succ), T ≤ t n →
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (j n).castSucc).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          (((K n).toHistory.event (j n)).incoming.closedPrefix T hT hTs) ((K n).event_initial (j n))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (j n).castSucc).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
              (yG n))),
        (t n - T) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) →
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρnc n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  intro Rad B
  filter_upwards [hkappa (max Rad 1) (max B 1) (by positivity) (by positivity)] with n hn
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hsingle := (K n).tested_kappaG_window_sameStage_A2B (j n) (hjt n) (htj n) (σ n) (hσ n)
    (y n) (yG n) (hyG n) (Rad := max Rad 1 / Real.sqrt (R n)) (θ := max B 1 / R n)
    (qg := Cg * R n) (cg := 1 / (2 * max (Ctime' : ℝ) 1)) hκ.le hn
  have hU : ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
      (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
        (max Rad 1 / Real.sqrt (R n)) := by
    intro z hz
    rw [← hRn n] at hz
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hz
  intro T hT hTs hTt hBT
  have hBT' : t n - max B 1 / R n ≤ T := by
    rw [← hRn n] at hBT
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hbridge := (K n).tested_noncollapse_eventPrefix_P6M (j n) (a := T) (t := t n)
    (ρ := ρnc n)
    {z | z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
        (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)))
      ∧ (t n - T) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1)}
    (fun τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hball => by
      have hM : 0 ≤ max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) :=
        (mul_nonneg hCg0 (hR n).le).trans (le_max_left _ _)
      have hgτ : (t n - τ) * max (Cg * R n)
          (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_right (by linarith) hM).trans hz.2
      exact hsingle τ (hBT'.trans haτ) hτt hjτ hτj z (hU z hz.1) hgτ zz hzz b hb hbρ hball)
    ((K n).prefixAt_time_last _)
  intro Bh tm z hz hg
  exact hbridge T hT hTs hTt le_rfl z ⟨hz, hg⟩


/-- **guarded kernel `hnc` ⇐ FRESH + `hdistWG`（`_A2B`，PROVED）**：
`hnc_window_of_fresh_P6SB` 加 guard。 -/
theorem ObservedHistory.hnc_window_of_freshG_A2B {K : ℕ → RetainedCoreHistory.{u}} {Cg : ℝ}
    {Ctime' : ℝ≥0} (hCg0 : 0 ≤ Cg)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    {nr : ℝ → ℝ} {Aκ κ Tκ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hdistWG : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    Tendsto (fun n => r / 200 *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop ∧
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (j n).castSucc).time
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) < T)
      (hTs : T < (K n).time (j n).succ), T ≤ t n →
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (j n).castSucc).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          (((K n).toHistory.event (j n)).incoming.closedPrefix T hT hTs) ((K n).event_initial (j n))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (j n).castSucc).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
              (yG n))),
        (t n - T) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) →
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ r / 200 →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  refine ⟨?_, ?_⟩
  · have hs : Tendsto (fun n => Real.sqrt (R n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hRlim
    refine (hs.const_mul_atTop (by positivity : (0 : ℝ) < r / 200)).congr fun n => ?_
    rw [hRn n]
  · exact hnc_window_sameStageG_A2B hCg0 hjt htj σ hσ y yG hyG R hRpos hRn hκ (fun _ => r / 200)
      (hkappaSG_of_fresh_A2B hWK Tn aSeed σ haT hsT has pT seedTrace y R L hRpos hL hTκ
        htimeS hsmallS hvolS hnrS hclock hwinF hgate hdistWG)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
