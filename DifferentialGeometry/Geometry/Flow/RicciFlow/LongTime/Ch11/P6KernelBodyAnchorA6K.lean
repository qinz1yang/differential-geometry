import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDBodyShiftA6K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBRowsA6K

/-!
# kernel body 帧 anchor producer（O-CH11-KERNB-A6 / W7 G3c，`_A6K`）

rings 层 `hanchor0` 槽（逐字形）⇐ kernel body 字段 + (B) 行 + selection 常数约束 `Ctime ≤ Ctime′`
（lead R 裁定 (a)，进 SELECTORS.md，不是 binder）。经 G3b `sliceBCBD_kernel_body_sep_alignedG_ev_A6K`
（A2B guarded G9″，无 `hdistW`；FRESH 换 body `hvolK`；∀n 平移）：
* `ρs n _ := (√(Q n))⁻¹` ⇒ 天花板 `hceil` = 行 `hRQ`，(SEP-ρ⁺) `hsepρ` = body `hscaleK`；
* 前缀 Dt `hpre1 / hpre2` ⇐ body 截断 `hslabK`（使用点 `≤ t n = σ n ≤ Tn n ≤ tK n`）+ 阈值单调
  （`Q ≤ max (n+1) Q`）+ 常数单调（`Ctime ≤ Ctime′`）；
* CXJD 族 ⇐ G1：`T₀X := 0`、`hOldX := rfl`、`hpin` ⇐ `recordsF / hHI / 0 < a₀`、`hRa` ⇐ `1 ≤ aSeed`；
  `hdσ` ⇐ body `hdistσ`（eventually）；`r := 1`、`θ₀ := 1`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- 常数单调（`_A6K`，PROVED）。 -/
theorem derivativeBoundBefore_const_mono_A6K {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} {C C' : ℝ≥0} {q t₀ : ℝ} (hC : C ≤ C')
    (h : G.DerivativeBoundBefore C q t₀) : G.DerivativeBoundBefore C' q t₀ := fun y t ht hR =>
  (h y t ht hR).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (sq_nonneg _))

/-- **body 帧 `hanchor0`（`_A6K`，PROVISIONAL[selection 常数约束 `Ctime ≤ Ctime′`；行 `hclock hsmall
ha₀ hRa1 hRQ`]）**：结论 = rings 层 `hanchor0` 槽逐字。 -/
theorem hanchor0_body_A6K {ε C1' C2' : ℝ} {Ctime' Ctime : ℝ≥0} (hεcone : ε ≤ coneAccuracy)
    (hC20 : 0 ≤ C2') (hCt : Ctime ≤ Ctime')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n (j' : Fin (K n).eventCount),
      ((K n).toHistory.event j').incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j'.succ) (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n)
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
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
    {Aκ : ℝ} (r : ℕ → ℝ)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) 1)
    (ha₀ : ∀ n, 0 < a₀ n) (hRa1 : ∀ n, 1 ≤ (aSeed n : ℝ)) (hRQ : ∀ n, R n ≤ Q n) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hQpos : ∀ n, 0 < Q n := fun n => (hRpos n).trans_le (hRQ n)
  have hρQ : ∀ n, (((Real.sqrt (Q n))⁻¹) ^ 2)⁻¹ = Q n := fun n => by
    rw [inv_pow, Real.sq_sqrt (hQpos n).le, inv_inv]
  have htK : ∀ n, t n ≤ tK n := fun n => by
    have h1 : (σ n : ℝ) ≤ Tn n := hsT n
    linarith [hσ n, hTnK n]
  refine sliceBCBD_kernel_body_sep_alignedG_ev_A6K (θ₀ := 1) hεcone hC20 hphi one_pos hjt htj
    hcanK (Eventually.of_forall hacc) (Eventually.of_forall hrad) (Eventually.of_forall hord)
    hpinchK0 (fun n => (K n).toHistory) rfl σ hσ y hyG R hRpos hRn (fun n => (hRlt n).le) hT₀
    Tn aSeed haT hsT has pT seedTrace L hL hCg hgood hwin one_pos hsmall hclock a₀
    (fun n => (ha₀ n).le) (hpin_kernel_A6K K recordsF ha₀ hHI)
    (hRa_kernel_A6K aSeed R hRlt hRa1) (fun _ => 0) (hT₀X_zero_A6K aSeed) (hOldX_kernel_A6K K _)
    (hdistσ.mono fun n hn => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hn))
    hκd hvolK (fun n _ => (Real.sqrt (Q n))⁻¹) (fun n => by rw [hρQ n]; exact hRQ n)
    (fun B _ => Eventually.of_forall fun n i hi b _ _ => by rw [hρQ n]; exact hscaleK n i hi b)
    (fun n e he => by
      rw [hρQ n]
      have hle : (K n).time e.succ ≤ (K n).time (j n).castSucc :=
        (K n).time_strictMono.monotone (Fin.le_iff_val_le_val.2 (by
          have := Fin.lt_def.1 he
          simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
          omega))
      have hmin : min ((K n).time e.succ) (tK n) = (K n).time e.succ :=
        min_eq_left (hle.trans ((hjt n).le.trans (htK n)))
      have h := hslabK n e
      rw [hmin] at h
      exact derivativeBoundBefore_const_mono_A6K hCt
        (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_threshold_le _
          (le_max_right _ _) h))
    (fun n => by
      rw [hρQ n]
      exact derivativeBoundBefore_const_mono_A6K hCt
        (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_threshold_le _ (le_max_right _ _)
          (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_mono _ (le_min (htj n).le (htK n))
            (hslabK n (j n)))))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
