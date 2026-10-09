import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteHIFinalP6HF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FinalCondKRouteFullP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HctrlNoJ10P6JA

/-!
# J10KERNEL G2a：final 帧 hctrl 环无 J10 孪生（O-CH11-J10KERNEL，`_P6JK2`）

`exists_hctrl_lateHI_final_P6HF`（P6KRouteHIFinalP6HF）的无 J10 孪生：删 `hqR : qcan < R`；survival 换
J10CORE 核 `hsurvive_noJ10_P6JC`（ceiling ⇐ `hceilQ_of_firstExit_sep_P6JG`，(B) 族 + `hsepX`）——
即 event 版 J10GEN2A `exists_hctrl_lateHI_noJ10_P6JA` 的 final 帧照抄（E 帧 = extendAt final 截断，
桥 `hgood_seq_final_P6JA`；搬回 K = `isParabolicallyRmControlledBall_final_P6M`）。E / (B) 族 binder 文本
逐字切自 J10GEN2A final `false_of_selection_finalSlab_lateHI_prefix_full_P6JA`（去 `hdistC`）。结论逐字。
生成器 `build-logs/scratch/O-CH11-J10KERNEL/gen/gen2a.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **G2a（`_P6JK2`，PROVISIONAL：E seed 兼容 / (B) 族 / `hsepX` / `hfinX`，同 J10GEN2A event 版）**：
final 帧 hctrl 环无 J10（无 `hqR`）；结论逐字。 -/
theorem exists_hctrl_lateHI_final_noJ10_P6JK2
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {D θcap qcan T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
      T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory
      i (pF n))
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x,
      InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
        n) x ∧
      -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
      T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
      (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount))
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / (G n).flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        (G n).flow.scalar (t n) z ≤
          Q * (G n).flow.scalar (t n) (yG n))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
      (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
      (Hs : ℕ → ObservedHistory.{u})
      (hHs : Hs = fun n => (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
        ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
          le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
        (htl n) (htK n)).toHistory)
      (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
      (hts' : HEq ts (fun n => ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime
        ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
          le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
        (htl n) (htK n)))
      (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (hys : ∀ n, HEq (ys n) (yG n))
      {epsG C1G C2G Cg : ℝ} {CtG : ℝ≥0}
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
      (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
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
          (Kh n).HasSpatialCanonicalTimeControl epsG C1G C2G CtG v z)
      (TnE aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haTE : ∀ n, aE n ≤ TnE n)
      (hsTE : ∀ n, ts n ≤ TnE n) (hasE : ∀ n, aE n ≤ ts n)
      (pTE : ∀ n, ((Hs n).stageAt (TnE n)).Carrier)
      (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
        ((Hs n).activeStage (TnE n)) ((Hs n).activeStage_mono (haTE n)) (pTE n))
      (haa : ∀ n, (aSeed n : ℝ) ≤ aE n)
      (hseedC : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (Kh n).horizon),
        (v : ℝ) = v' →
        ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
          (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
          (h1' : (Kh n).activeStage (aSeed n) ≤ (Kh n).activeStage v')
          (h2' : (Kh n).activeStage v' ≤ (Kh n).activeStage (Tn n)),
          HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
            ((seedTrace n).point ((Kh n).activeStage v') h1' h2'))
      {rX : ℝ}
      (hC2G : 0 ≤ C2G)
      (hrX : 0 < rX)
      (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (TnE n) (pTE n) rX)
      (hclock : ∀ n, (aE n : ℝ) = (TnE n : ℝ) - rX ^ 2)
      (a₀X : ℕ → ℝ)
      (ha₀X : ∀ n, 0 ≤ a₀X n)
      (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
        InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
      (hRa : ∀ n, 1 ≤ R n * aE n)
      (qX : ℕ → CutoffParameters)
      (T₀X : ℕ → ℝ)
      (hT₀X : ∀ n, T₀X n ≤ aE n)
      (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
        GeometricCutoffRecord (Hs n) e (qX n))
      (hOldX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
        ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
      (hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
        ((recordsX n e he).static b).hasCanonicalWindow)
      (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
      (haccX : ∀ n : ℕ, (qX n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
      (hmX : ∀ n, 2 ≤ (qX n).modelOrder)
      (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
        (he : T₀X n ≤ (Hs n).time e.succ) b, (aE n : ℝ) < (Hs n).time e.succ →
          M * R n < ((recordsX n e he).static b).neck.scale)
      (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
            ((Hs n).activeStage_mono (hsTE n))) (ys n) ≠ ⊤) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ᶠ n in atTop,
      (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r / Real.sqrt (R n)) := by
  subst hKh
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  subst hHs
  obtain rfl := eq_of_heq hts'
  -- E 层（`Hs n` = final 截断 history；final prefix_full_P6JA 原式）
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt ((K n).prefixAt_time_last _)
      (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl ((htl n).trans (htK n))
        le_rfl) ((K n).final_initial ((htl n).trans (htK n))) (htl n) (htK n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (Fin.last (K n).eventCount)).extendAtTime ((K n).prefixAt_time_last _)
      (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl ((htl n).trans (htK n))
        le_rfl) ((K n).final_initial ((htl n).trans (htK n))) (htl n) (htK n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun n => (hσ n).symm
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => (hys n).trans (hyG n).symm
  have hHs' : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory := fun _ => rfl
  -- 0. E 层 hgood（final 桥）/ hwin（⇐ hclock）与 hceilQ（G1b-3，(B) 族 + hsepX）
  have hgoodE := hgood_seq_final_P6JA (haTK := haT) (hsTK := hsT) (hasK := has)
    (haTE := haTE) (hsTE := hsTE) (hasE := hasE) hHs' hσ' hysK haa hseedC hgood
  have hwinE := hwinE_of_clock_P6JA hsTE (fun _ => rfl) hrX hclock hRlim
  have hceilQ := hceilQ_of_firstExit_sep_P6JG
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) hC2G hrX
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    htl htK Hs rfl
    TnE aE ts haTE hsTE hasE pTE hsmall hclock seedE a₀X ha₀X hpinX ys R L hR hRlim hL hgoodE
    hwinE hRa qX T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepX hfinX
  -- 1. anchor 搬到 E 层（`A = 1`）
  obtain ⟨Q, hQ, hball⟩ := hanchor0_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    htl htK hanchor0 Hs ts ys R rfl HEq.rfl hys hRn 1 one_pos
  -- 2. survival：J10CORE 核（无 J10），`Cball := Q`、`Q_b := max (max Q Cg) 1`
  have hQb1 : (1 : ℝ) ≤ max (max Q Cg) 1 := le_max_right _ _
  have hC0 : (0 : ℝ) ≤ 2 * (CtG : ℝ) * max (max Q Cg) 1 := by
    have := CtG.coe_nonneg
    positivity
  have hT : 0 < 1 / (2 * (CtG : ℝ) * max (max Q Cg) 1 + 1) := by positivity
  have hstep : 2 * (CtG : ℝ) * max (max Q Cg) 1 *
      (1 / (2 * (CtG : ℝ) * max (max Q Cg) 1 + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  obtain ⟨K₀, hK₀, hev⟩ := RetainedCoreHistory.hsurvive_noJ10_P6JC (Cball := Q)
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) hphi recordsF hHI
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab htl htK hderG hnot hT₀ hRt Hs ts ys R
    rfl HEq.rfl hys hRn hRlim hQb1 (hceilQ Q hQ) 1 _ one_pos hT hstep
  -- 3. 受控球半径（final 搬回 K：`isParabolicallyRmControlledBall_final_P6M`）
  have hm : 0 < min 1 (min (1 / (2 * (CtG : ℝ) * max (max Q Cg) 1 + 1)) (1 / (K₀ + 1))) := by
    have : 0 < 1 / (K₀ + 1) := by positivity
    exact lt_min one_pos (lt_min hT this)
  refine ⟨Real.sqrt (min 1 (min (1 / (2 * (CtG : ℝ) * max (max Q Cg) 1 + 1)) (1 / (K₀ + 1)))),
    Real.sqrt_pos.2 hm, fun r hr hrm => ?_⟩
  filter_upwards [hev, hball] with n hn hb
  have hRn0 : 0 < R n := hR n
  obtain ⟨h1, h2, h3⟩ := controlledBall_radius_arith_P6M2 hK₀ hRn0 hr hrm
  have htr := hn hb
  have hE : (Hs n).isParabolicallyRmControlledBall (ts n) (ys n) (r / Real.sqrt (R n)) :=
    ((Hs n).isParabolicallyRmControlledBall_iff_isTracedRegion (ts n) (ys n) _).2
      (htr.mono (by positivity) h1 (by positivity) h2 (by positivity) h3)
  exact (K n).isParabolicallyRmControlledBall_final_P6M ((htl n).trans (htK n)) (htl n) (htK n)
    (ts n) (σ n) (hσ' n) (ys n) (y n) (hysK n) hE

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
