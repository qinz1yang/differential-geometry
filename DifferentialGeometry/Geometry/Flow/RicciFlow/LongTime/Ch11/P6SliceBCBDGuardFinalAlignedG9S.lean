import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardFinalNcG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSlabsFinalG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardSeqG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFinalSlabP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceTerminalRt_P6LS

/-!
# G5″ / G9″ guarded 孪生（逐 `n` FRESH）的 final-slab 外壳（O-CH11-G9SHIFT G9，后缀 `_G9S`）

σ 落 final slab（`time (Fin.last _) < t n < horizon`）：
* `hdistWStarF_of_firstExit_G9S`：同 slab c⋆ stay 付 guarded `hdistW⋆`（核 `stay_cstar_final_P6HK`）；
* `hW_final_Cg_G9S`：`hW_final_P6M` 的 `Cg` 推广；
  `hnc_window_of_freshGF_seq_G9S`：逐 `n` FRESH 的 final guarded `hnc`；
* **`ObservedHistory.sliceBCBD_final_fresh_theta_ev_noProtC_alignedG_seq_G9S`**（G5″-final）：kernel G4
  取 `H n := (K n).prefixAt (Fin.last _)`、`G n := finalSlab.restrictIncoming`、`s n := horizon`，
  槽由 G5 / G6 / G7 的 final 件付；`hpinch` 增 final slab 一项 `hpinchF`；
* **`ObservedHistory.sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_G9S`**（G9″-final，验收终点形）：
  `hnotK` 由 HARNACK `capCeiling_of_firstExit_sep_final_P6HK` 付，其余同 G9″。
结论 = KFINAL 的 final anchor 陈述（`G n` 中心）。生成器 `gen/genG.py`。无新分析、无新 binder。
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

/-- **同 slab c⋆ stay ⇒ guarded `hdistW⋆`，final（`_G9S`）**：A2B 同名引理换帧，核换 `stay_cstar_final_P6HK`。 -/
theorem ObservedHistory.hdistWStarF_of_firstExit_G9S {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    {t : ℕ → ℝ} (htK : ∀ n, t n < (K n).horizon) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
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
  have hσH : (σ n : ℝ) < (K n).toHistory.horizon := by
    rw [hσ n]
    exact htK n
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
  exact ObservedHistory.stay_cstar_final_P6HK hC2 hCg (K n) (haT n) (hsmall n)
    (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n) (L n) (hR n) (hgood n) hav hvs
    hσH haL hRa' rfl rfl hg tr hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀'
    (fun e he => recordsK n e ((le_max_left _ _).trans he))
    (fun e he => hOldX n e ((le_max_right _ _).trans he))
    (fun e he b => hcanK n e _ b) hacc' hDm
    (fun e _ _ h3 h4 _ _ b => absurd (h4.trans (hst ▸ h3)) (not_le.mpr e.castSucc_lt_succ))
    hx (hdσ n) hnum v le_rfl hvs

/-- **selection ⇒ SLT 终端 `hW`，final slab，阈值 `Cg·R`（`_G9S`）**：`hW_final_P6M` 的 `Cg` 推广。 -/
theorem ObservedHistory.hW_final_Cg_G9S {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
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
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      Cg * R n < (G n).flow.scalar (t n) x →
        ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) eps C1' C2' x,
          W.capTubeHasNeckChart eps := by
  intro Rad
  filter_upwards [hL.eventually_ge_atTop (max Rad 1)] with n hLn
  intro x hx hq
  have hσact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) (by rw [hσ n]; exact (htl n).le)
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_final_G9S (hfin n) (G n) (hG n) hσact.symm (σ n) _ x (yG n) x'
      (y n) hxx (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  have hL11 := (K n).toHistory.hasSpatialCanonicalTimeControl_at_terminal_of_selection_Cg_P6L3
    (haT n) (hsT n) (has n) (seedTrace n) (y n) (hR n) (hgood n) hLn
  have hsc := (K n).scalar_final_G9S (hfin n) (G n) (hG n) hσact.symm (σ n) x x' hxx
  have hgoodx := hL11 x' hx' (by rw [hsc, hσ n]; exact hq.le)
  have hw := (K n).witness_final_G9S (hfin n) (G n) (hG n) hσact.symm (σ n) x x' hxx hgoodx.1
  rw [hσ n] at hw
  exact hw

/-- **guarded kernel `hnc` ⇐ 逐 `n` FRESH + `hdistWG`，final（`_G9S`）**：`hnc_window_of_freshG_seq_G9S`
    换帧。 -/
theorem ObservedHistory.hnc_window_of_freshGF_seq_G9S {K : ℕ → RetainedCoreHistory.{u}} {Cg : ℝ}
    {Ctime' : ℝ≥0} (hCg0 : 0 ≤ Cg)
    {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (K n).toHistory)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
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
    Tendsto (fun n => r / 200 * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop ∧
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (Fin.last (K n).eventCount)).time
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) < T)
      (hTs : T < (K n).horizon), T ≤ t n →
        t n - B / (G n).flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (Fin.last (K n).eventCount)).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          ((G n).closedPrefix T hT hTs)
          (by rw [hG n]; exact (K n).final_initial ((htl n).trans (htK n)))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (Fin.last (K n).eventCount)).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (t n - T) * max (Cg * R n) ((G n).flow.scalar (t n) z) ≤
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
  · exact hnc_window_sameStageGF_G9S hCg0 htl htK G hG σ hσ y yG hyG R hRpos hRn hκ
      (fun _ => r / 200)
      (hkappaSG_of_fresh_seq_G9S hWK Tn aSeed σ haT hsT has pT seedTrace y R L hRpos hL hTκ
        htimeS hsmallS hvolS hnrS hclock hwinF hgate hdistWG)

/-- **G5″ guarded 孪生（逐 `n` FRESH），σ 在 final slab（`_G9S`）**：`…theta_ev…alignedG_seq_G9S` 换帧。 -/
theorem ObservedHistory.sliceBCBD_final_fresh_theta_ev_noProtC_alignedG_seq_G9S
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount)
        < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi)
    (hnotK : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (Fin.last (K n).eventCount))
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤
          θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (ρs : ℕ → ℝ → ℝ)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount))
    (hpre2 : ∀ n, (G n).DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hRlt n).le) hnat
  have hRlimG : Tendsto (fun n => (G n).flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨-, -, Dp, -, -, hD, -, -, -, hDn⟩ := exists_params_P6D (fun _ => (0 : ℝ))
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ Dp n ∧
      Dp n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot' : ∀ᶠ n in atTop, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static
              b).window x ∧
        ‖x.val‖ < Dp n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤ θ₀ *
          ((((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static
              b).neck.scale
            )⁻¹ :=
    hnotK.mono fun n hn => by
      rw [hD n]
      exact (K n).not_capWindowPoint_prefix_of_late_P6N (Fin.last (K n).eventCount) (recordsK n) (yG
          n) hn
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / (G n).flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt)
        i),
      hpinchF n⟩
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (Fin.last (K n).eventCount) (recordsK n)
      (hcanK n)
  have hslabs := ObservedHistory.hslabs_of_sepRho_prefixDtF_G9S hC20 (by linarith) htl htK G hG σ hσ
      y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X
    hOldX hdσ hwin recordsK hcanK hacc hrad hord hT₀ ρs hsepρ hpre1 hpre2
  have hCg1 : (1 : ℝ) ≤ Cg := by linarith
  have hCg0' : (0 : ℝ) ≤ Cg := by linarith
  have hdistWG := ObservedHistory.hdistWStarF_of_firstExit_G9S (Ctime' := Ctime') hC20 hCg1 htK σ hσ
      y R hRpos hR1 Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀
    hpin hRa recordsK hcanK hacc hrad hT₀ T₀X hT₀X hOldX hdσ
  obtain ⟨hρ, hnc⟩ := hnc_window_of_freshGF_seq_G9S hCg0'
    htl htK G hG σ hσ y yG hyG R hRpos hRlim hRn hκ hr hWK
    Tn aSeed haT hsT has pT seedTrace L hL hTκ htimeS hsmall hvolS hnrS hclock hwinF hgate hdistWG
  have hW := ObservedHistory.hW_final_Cg_G9S (fun n => (htl n).trans (htK n)) hG htl σ hσ y yG hyG R
      hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgradGF_of_selection_sameSlab_Cg_G9S hC20 htl htK G hG σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistWG
  have hder := hderSelGF_of_selection_sameSlab_Cg_G9S htl htK G hG σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistWG
  have hR0 : ∀ n, 0 < (G n).flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * (G n).flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_local_starG_theta_ev_A2B (θcap := fun _ => θ₀)
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := G)
    (s := fun n => (K n).horizon) (y := yG) (ρ := fun _ => r / 200) hεcone hκ hphi hθ₀
    (fun n => (K n).prefixAt_time_last _) (fun n => by rw [hG n]; exact (K n).final_initial ((htl
        n).trans (htK n))) hcan hpar
    (fun _ => le_rfl) hpinch htl htK hnot' hT₀' hRt hRlimG hR0 (Cq := Cg)
    (fun n => Cg * R n) hCg0 hqC
    hslabs hder hW hgrad hnc hρ

/-- **G9″ guarded 孪生（逐 `n` FRESH），σ 在 final slab（`_G9S`）**：`…sep…alignedG_seq_G9S` 换帧。 -/
theorem ObservedHistory.sliceBCBD_final_fresh_sep_noProtC_alignedG_seq_G9S
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount)
        < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad2 : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) ((K n).horizon) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (Fin.last (K n).eventCount) →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale)
    (ρs : ℕ → ℝ → ℝ)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (Fin.last (K n).eventCount) →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount))
    (hpre2 : ∀ n, (G n).DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  have hceil := ObservedHistory.capCeiling_of_firstExit_sep_final_P6HK hC20 (fun n => (htl n).trans
      (htK n)) htl htK
    σ hσ y yG hyG R hRpos hR1 (fun n => by rw [hRn n, hG n]) Tn aSeed haT hsT has pT seedTrace L hL
        hgood hr hsmall hclock a₀ ha₀ hpin hRa T₀X hT₀X
    hOldX hdσ hwin recordsK hsepT hθ₀ hRlt hcanK hacc hrad2 hord hsep4
  have haccE : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ε₀ := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hε₀)] with n hn
    exact (hacc n).trans hn
  have hnotKev : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (Fin.last (K n).eventCount))
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
    filter_upwards [hceil, haccE] with n hc ha
    rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
    have hx : ‖x.val‖ < (p n).modelRadius := lt_of_lt_of_le h2 (hrad2 n)
    have hS := hlow ((K n).toHistory.event i) ha (le_trans (by omega) (hord n))
      ((recordsK n i hi).static b) (hcanK n i hi b) x hx
    rw [← h1] at hS
    have hC := hc i hi hl A b h3
    have hP := hsep4 n i hi b hl h3
    linarith
  exact sliceBCBD_final_fresh_theta_ev_noProtC_alignedG_seq_G9S (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := hθ₀) (htl := htl) (htK := htK) (G := G) (hG := hG) (hcanK := hcanK) (hacc
        := hacc)
    (hrad := fun n => le_trans (by linarith) (hrad2 n)) (hord := hord) (hpinchK0 := hpinchK0)
        (hpinchF := hpinchF)
    (hnotK := hnotKev) (Kh := fun n => (K n).toHistory) (hKh := rfl) (σ := σ) (hσ := hσ) (y := y)
    (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn) (hRlt := hRlt) (hT₀ := hT₀) (Tn := Tn)
    (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT) (seedTrace := seedTrace)
    (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin) (hr := hr)
    (hsmall := hsmall) (hclock := hclock) (a₀ := a₀) (ha₀ := ha₀) (hpin := hpin) (hRa := hRa)
    (T₀X := T₀X) (hT₀X := hT₀X) (hOldX := hOldX) (hdσ := hdσ) (hκ := hκ) (hWK := hWK)
    (hTκ := hTκ) (htimeS := htimeS) (hvolS := hvolS) (hnrS := hnrS) (hwinF := hwinF)
    (hgate := hgate) (ρs := ρs) (hsepρ := hsepρ) (hpre1 := hpre1)
    (hpre2 := hpre2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
