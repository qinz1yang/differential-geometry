import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDBodyFinalKFP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBodyAnchorA6K

/-!
# final kernel body 帧 anchor producer（O-CH11-KFPROD G4b，`_KFP`）

final rings 层 `hanchor0` 槽（逐字形）⇐ final kernel body 字段 + (B) 行 + selection 常数约束
`Ctime ≤ Ctime′`（R33：`fine_Ctime_le_p6Ctime_A6K` 付）。KERNB `hanchor0_body_A6K` 的 final 帧对应，经 G4a
`sliceBCBD_final_body_sep_alignedG_ev_KFP`（G9SHIFT final G9″ guarded，无 `hdistW`；
FRESH 换 body `hvolK`；∀n 平移）：
* `ρs n _ := (√(Q n))⁻¹` ⇒ 天花板 `hceil` = 行 `hRQ`，(SEP-ρ⁺) `hsepρ` = body `hscaleK`；
* 前缀 Dt `hpre1` ⇐ body 截断 `hslabK`（event 段终点 `time e.succ ≤ time last < t ≤ tK`），
  `hpre2` ⇐ body 截断 `hderF`（`t ≤ min horizon tK`）+ 阈值单调 + 常数单调；
* CXJD 族 ⇐ KERNB G1：`T₀X := 0`、`hOldX := rfl`、`hpin` ⇐ `recordsF / hHI / 0 < a₀`、
  `hRa` ⇐ `1 ≤ aSeed`；
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

/-- **final body 帧 `hanchor0`（`_KFP`，PROVISIONAL[selection 常数约束 `Ctime ≤ Ctime′`；行 `hclock
hsmall ha₀ hRa1 hRQ`]）**：结论 = final rings 层 `hanchor0` 槽逐字。 -/
theorem hanchor0_body_final_KFP {ε C1' C2' : ℝ} {Ctime' Ctime : ℝ≥0} (hεcone : ε ≤ coneAccuracy)
    (hC20 : 0 ≤ C2') (hCt : Ctime ≤ Ctime')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} {a₀ : ℕ → ℝ}
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
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n (j' : Fin (K n).eventCount),
      ((K n).toHistory.event j').incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j'.succ) (tK n)))
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (min (K n).horizon (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
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
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n) := by
  subst hKh
  have hQpos : ∀ n, 0 < Q n := fun n => (hRpos n).trans_le (hRQ n)
  have hρQ : ∀ n, (((Real.sqrt (Q n))⁻¹) ^ 2)⁻¹ = Q n := fun n => by
    rw [inv_pow, Real.sq_sqrt (hQpos n).le, inv_inv]
  have htKK : ∀ n, t n ≤ tK n := fun n => by
    have h1 : (σ n : ℝ) ≤ Tn n := hsT n
    linarith [hσ n, hTnK n]
  exact sliceBCBD_final_body_sep_alignedG_ev_KFP (θ₀ := 1) (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := one_pos) (htl := htl) (htK := htK) (G := G) (hG := hG)
    (hcanK := hcanK) (hacc := Eventually.of_forall hacc) (hrad := Eventually.of_forall hrad)
    (hord := Eventually.of_forall hord) (hpinchK0 := hpinchK0) (hpinchF := hpinchF)
    (Kh := fun n => (K n).toHistory) (hKh := rfl) (σ := σ) (hσ := hσ) (y := y) (hyG := hyG)
    (R := R) (hRpos := hRpos) (hRn := hRn) (hRle := fun n => (hRlt n).le) (hT₀ := hT₀)
    (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT)
    (seedTrace := seedTrace) (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin)
    (hr := one_pos) (hsmall := hsmall) (hclock := hclock) (a₀ := a₀)
    (ha₀ := fun n => (ha₀ n).le) (hpin := hpin_kernel_A6K K recordsF ha₀ hHI)
    (hRa := hRa_kernel_A6K aSeed R hRlt hRa1) (T₀X := fun _ => 0)
    (hT₀X := hT₀X_zero_A6K aSeed) (hOldX := hOldX_kernel_A6K K _)
    (hdσ := hdistσ.mono fun n hn =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hn))
    (hκd := hκd) (hvolK := hvolK) (ρs := fun n _ => (Real.sqrt (Q n))⁻¹)
    (hceil := fun n => by rw [hρQ n]; exact hRQ n)
    (hsepρ := fun B _ => Eventually.of_forall fun n i hi b _ _ => by
      rw [hρQ n]; exact hscaleK n i hi b)
    (hpre1 := fun n e _ => by
      rw [hρQ n]
      have hle : (K n).time e.succ ≤ (K n).time (Fin.last (K n).eventCount) :=
        (K n).time_strictMono.monotone (Fin.le_last e.succ)
      have hmin : min ((K n).time e.succ) (tK n) = (K n).time e.succ :=
        min_eq_left (hle.trans ((htl n).le.trans (htKK n)))
      have h := hslabK n e
      rw [hmin] at h
      exact derivativeBoundBefore_const_mono_A6K hCt
        (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_threshold_le _
          (le_max_right _ _) h))
    (hpre2 := fun n => by
      rw [hρQ n]
      exact derivativeBoundBefore_const_mono_A6K hCt
        (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_of_threshold_le _ (le_max_right _ _)
          (OrientedThreeStage.IncomingSlab.derivativeBoundBefore_mono _ (le_min (htK n).le (htKK n))
            (hderF n))))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
