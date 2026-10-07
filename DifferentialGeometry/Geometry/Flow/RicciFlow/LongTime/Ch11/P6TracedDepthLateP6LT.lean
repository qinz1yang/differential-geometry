import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorSelectionP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.LateKernelsG1_P6LL

/-!
# late-records 主形的 extendAt 层零件（O-CH11-P6LATE G2，后缀 `_P6LT`）

P6D2 G3（`P6TracedDepthP6D2`）与 G1y（`P6AnchorSelectionP6M`）里**吃 full family** 的四个定理的 late 版：
* `hsurvive_of_extendAt_late_P6LT` / `hextend_of_extendAt_late_P6LT`：核心换成 G1 的 (1) / (2)；
* `exists_subseq_htraced_extendAt_late_P6LT`：驱动 `exists_subseq_forall_depthExtendable_P6L` 不变，
  两条单步换成上面的 late 版（其余零件 `hanchor0 / hpinch / hderiv _of_extendAt_P6D2` 不吃 records）；
* `RetainedCoreHistory.hanchor0_late_P6LT`：SLT 窗口版本来就是 late 形，直接把 `T₀ hT₀ records hcan hnot`
  从 binder 传入。
数据前提块（late）：`records : ∀ n i, T₀ n ≤ time i.succ → …`、`hcan` / `hscale` late、`hnot` =
`CapWindowPoint` late 展开形、`hT₀ : ∀ B, ∀ᶠ n, T₀ n ≤ t n − B / R n`；full family `recordsF` + `hδF`
（hybrid，见 G1 块）；`hinit` → 时刻 0 HI `a₀`（`ha₀ hHI`）；`p₀` 去掉。证明其余逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **`_P6LT`（基点 anchor，late records）**：`hanchor0_of_closure_data_window_q_P6M` 的副本：SLT 窗口版
本来就吃 late 形（`T₀ hT₀ records hcan`），这里直接把 `T₀ / hT₀ / records / hcan / hnot` 从 binder 传入
（原版取 `T₀ = 0` 并由 `hRt` 造 `hT₀`）；`p₀` 去掉。 -/
theorem RetainedCoreHistory.hanchor0_late_P6LT
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t ρ T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((G n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    {Cq : ℝ} (q : ℕ → ℝ) (hq2 : ∀ n, 2 * qcan n ≤ q n)
    (hqC : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) := by
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop :=
    tendsto_atTop_mono (fun n => (hqcan n).trans (hqR n).le) hnat
  have hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop :=
    tendsto_atTop_mono (fun n => (hpar n).2.1.trans (hpar n).2.2.1) hnat
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    exact (hpar n).1.trans hn
  have hθ (n : ℕ) : (1 : ℝ) / 2 ≤ θcap n := by
    refine le_trans ?_ (hθcap n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hord (n : ℕ) : 2 ≤ (p n).modelOrder := le_trans (by omega) (hpar n).2.2.2.1
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M
    (Ctime := 2 * Ctime) (Cq := Cq) hεle hκ hphi (by norm_num : (0 : ℝ) < 1 / 2) H hend s G hGi t
    hat hts y q ρ (fun n => by have := hq0 n; have := hq2 n; linarith) hqC hR hRt T₀ hT₀
    records hcan hradius hord hacc hW
    (fun Rad B => Eventually.of_forall fun n j first hf z _ Btr v hv _ hRv => by
      have hlt : qcan n < ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) := by
        have := hq0 n
        have := hq2 n
        linarith
      have h := hslab n j (Fin.castSucc_lt_last j) _ v hv hlt
      rw [hctime]
      have h0 : 0 ≤ (Ctime : ℝ) * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
        mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
      linarith)
    (fun Rad B => Eventually.of_forall fun n x _ v hv _ hRv =>
      hderG n x v hv (lt_of_le_of_lt (hq2 n) hRv)) hgrad
    (fun B => Eventually.of_forall fun n j v hv w => (hpinch n).1 j v hv.1 w)
    (fun B => Eventually.of_forall fun n v hv w => (hpinch n).2 v hv.1 w) hnc hρ D θcap hDt hθ
    hnot A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact ((hq0 n).trans (hqR n)).le

namespace ObservedHistory

/-- **`_P6LT`（单步 survival，late records + hybrid）**：`hsurvive_of_extendAt_P6D2` 的副本，核心换成
(1) `exists_eventually_isTracedRegion_extendAt_late_P6LL`。 -/
theorem hsurvive_of_extendAt_late_P6LT
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n)) :
    ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Ctime : ℝ) * Q * T ≤ 1 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
      (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n) := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  intro A T Q hA hT hQ2 hstep
  obtain ⟨K₀, hK₀, hev⟩ :=
    RetainedCoreHistory.exists_eventually_isTracedRegion_extendAt_late_P6LL hphi recordsF ha₀ hHI
      hend hGi hcan hδF hqcan hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hT₀
      (A := A) (T := T) (Q := Q) hA hT (by linarith)
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev, hRt.eventually_ge_atTop T] with n hn hRtn hball
  rw [hRn n] at hball ⊢
  have hq0 : 0 < qcan n := lt_of_lt_of_le (by positivity) (hqcan n)
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := hq0.trans (hqR n)
  have hTR : T / (G n).flow.scalar (t n) (y n) ≤ t n := by
    rw [div_le_iff₀ hR0]
    linarith
  let uu : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon :=
    ⟨t n - T / (G n).flow.scalar (t n) (y n), by linarith,
      (sub_le_self _ (div_pos hT hR0).le).trans
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)).2.2⟩
  have hut : uu ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n) := by
    change t n - T / (G n).flow.scalar (t n) (y n) ≤ t n
    linarith [div_pos hT hR0]
  have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    hq0.le (hslab n) (hderG n)
  refine hn (ys n) (hys n) uu rfl ?_
  refine RetainedCoreHistory.scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball
    ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)) (Ctime := 2 * Ctime)
    (qcan := 2 * qcan n)
    (T := T) hR0 (by linarith) ?_ rfl hut hdin.1 hdin.2.1 hdin.2.2 ?_ (ys n) hball
  · push_cast
    linarith
  · nlinarith [hqR n]

/-- **`_P6LT`（`hextend`，late records + hybrid）**：`hextend_of_extendAt_P6D2` 的副本，核心换成 (2)
`depthExtendable_add_of_windowAnchorBound_late_P6LL`。 -/
theorem hextend_of_extendAt_late_P6LT
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n)) :
    ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
    (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
    (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
    ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
        ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
        (A / Real.sqrt (R (σ i))),
    ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
      (w : ℝ) = ts (σ i) - T' / R (σ i) →
    ∀ (hwt : w ≤ ts (σ i))
      (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
        ((Hs (σ i)).activeStage (ts (σ i)))
        ((Hs (σ i)).activeStage_mono hwt) x),
      metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
        (Bt.point ((Hs (σ i)).activeStage w) le_rfl
          ((Hs (σ i)).activeStage_mono hwt)) ≤
        M * R (σ i)) →
    DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1))) := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  have hRfun : R = fun n => (G n).flow.scalar (t n) (y n) := funext hRn
  subst hRfun
  intro σ hσ Tstar M hT hM hext hanc
  exact depthExtendable_add_of_windowAnchorBound_late_P6LL hphi recordsF ha₀ hHI hend hGi hcan hδF
    hqcan hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hT₀ hRt hσ hT hM ys hys hext hanc

/-- **`_P6LT`（`htraced`，late records + hybrid）**：`exists_subseq_htraced_extendAt_P6D2` 的副本：驱动
`exists_subseq_forall_depthExtendable_P6L` 不变，两条单步换成上面的 late 版。 -/
theorem exists_subseq_htraced_extendAt_late_P6LT
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwit : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T := by
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  have hRlim : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    rw [hRn n]
    linarith [hqcan n, hqR n]
  have hqcan2 : ∀ n, 2 * qcan n ≤ 2 * R n := fun n => by
    rw [hRn n]
    linarith [hqR n]
  exact exists_subseq_forall_depthExtendable_P6L Hs ts ys R hR hRlim
    (hsurvive_of_extendAt_late_P6LT hphi recordsF ha₀ hHI hend hGi hcan hδF hqcan hpar hscale hθcap
      hpinch hslab hat hts hderG hqR hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn)
    (hanchor0_of_extendAt_P6D2 hend hGi hat hts hanchor0 Hs ts ys R hHs hts' hys hRn)
    (hextend_of_extendAt_late_P6LT hphi recordsF ha₀ hHI hend hGi hcan hδF hqcan hpar hscale hθcap
      hpinch hslab hat hts hderG hqR hnot hT₀ hRt Hs ts ys R hHs hts' hys hRn)
    hr₀ hw hseed hκ ρnc hradii hkappa hphi
    (hpinch_of_extendAt_P6D2 hend hGi hat hts hpinch Hs ts ys R hHs hts')
    hε hεX hεN hqs hwit (Ctime := 2 * Ctime) (Cq := 2) (qcan := fun n => 2 * qcan n) hqcan2
    (hderiv_of_extendAt_P6D2 hend hGi hat hts hqcan hslab hderG Hs ts ys R hHs hts') hbcad

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
