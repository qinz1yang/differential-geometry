import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingDepthExtension_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessP6D
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf

/-!
# P6 / L7 任意深度的 `htraced`（`RetainedCoreHistory` + `extendAt` 实例化）+ 喂 P6D G2（O-CH11-P6D2 G3）

后缀 `_P6D2`。G2 的抽象驱动 `exists_subseq_forall_depthExtendable_P6L`（`ObservedHistory` 序列形）在坏点
序列 `K n = (H n).extendAt …`、`τ n = extendAtTime …`、`ŷ n ≍ y n`、`R n = R_G(t n, y n)` 上实例化：

* 两条单步由树内定理直接给出（**数据前提**与 `depthExtendable_add_of_windowAnchorBound` 逐字相同：
  records / `hpar` / `hscale` / `hθcap` / pinching / slab 导数 / `¬ CapWindowPoint` / `hRt`）：
  `hsurvive_of_extendAt_P6D2`（`CrossingTracedRegion:70` + `TracedRegionDepthInduction:17`；P6B L7
  的 eventually-深度版，去掉 `∀ n, T ≤ R t`）、`hextend_of_extendAt_P6D2`（`CrossingDepthExtension:16`）；
* trace-local pinching / 时间导数（P6D G2 前提形）由数据前提逐点给出（`hpinch_of_extendAt_P6D2`、
  `hderiv_of_extendAt_P6D2`，常数 `2·Ctime`、阈值 `2·qcan`）；`hanchor0_of_extendAt_P6D2` 把 `G` 形
  基点 anchor（L6 / `SLT:249` 输出形）搬到延长 history；
* 序列对象用等式绑定（`hHs : Hs = …`、`hts' : HEq ts …`、`hys`、`hRn`），证明里 `subst`——陈述保持
  `Hs ts ys R` 的通用形（与 P6D G2 / G2 驱动逐字同形）。

主定理 `exists_subseq_htraced_extendAt_P6D2`：⇒ `∃ σ ↑, ∀ T > 0, DepthExtendable Hs ts ys R σ T`
（= P6D G2 的 `htraced`，沿 `σ`；**无 `4·Ctime·Q·T ≤ 1` 限制**）。consumer
`exists_eventually_hasSpatialCanonicalTimeControl_extendAt_P6D2`：喂 P6D G2 ⇒ 坏点子列 eventually 完整
`HasSpatialCanonicalTimeControl`（常数先取）。

**剩余的 P6 trace-local 前提**（全部显式）：`hseed`（基点种子体积）、`hkappa`（局部 κ，可由 G0 从
`Pre841` / (K-seq) 给出）、`hwit`（更早时刻 witness，point selection 的"更早好"）、`hbcad`（BCAD 双 trace 形）、
`hanchor0`（基点 L6）。D-4：无 `nr`。D-6：(D2) 不出现（深度由本文件自身的 traced regions 给出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

open private RetainedCoreHistory.metricScalarAt_extendAt_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf

namespace ObservedHistory

/-- **单步 survival（`hsurvive`）的 `extendAt` 实例**：基点 ball anchor（延长 history 形）+ `4·Ctime·Q·T ≤ 1` ⇒
traced region（`CrossingTracedRegion:70` + `TracedRegionDepthInduction:17`，P6B L7 的
eventually-深度版：`T ≤ R t` 由 `hRt` eventually 给出）。 -/
theorem hsurvive_of_extendAt_P6D2
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
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
    RetainedCoreHistory.exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces hphi
      hinit hend hGi hrec hqcan hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot
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

/-- **深度延伸（`hextend`）的 `extendAt` 实例** = `depthExtendable_add_of_windowAnchorBound`。 -/
theorem hextend_of_extendAt_P6D2
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
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
  exact depthExtendable_add_of_windowAnchorBound hphi hinit hend hGi hrec hqcan hpar hscale hθcap
    hpinch hslab hat hts hderG hqR hnot hRt hσ hT hM ys hys hext hanc

/-- 基点 ball anchor：`G` 形（L6 / `SLT:249` 输出形）⇒ 延长 history 形（`scalar_ball_bound_extendAt_iff`）。 -/
theorem hanchor0_of_extendAt_P6D2
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
    ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (A / Real.sqrt (R n)),
      metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := hanchor0 A hA
  refine ⟨Q, hQ, hev.mono fun n hn => ?_⟩
  rw [hRn n]
  exact (RetainedCoreHistory.scalar_ball_bound_extendAt_iff (H n) (hend n) (G n) (hGi n) (hat n)
    (hts n) (y n) (ys n) (hys n) _ _).mpr hn

/-- trace-local pinching ⇐ 数据前提 `hpinch`
（`curvatureOperatorLowerBoundAt_extendAt_of_pinched`，逐点）。 -/
theorem hpinch_of_extendAt_P6D2
    {phi : ℝ → ℝ}
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
        ((Hs n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
          (phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))) := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  intro D T _ _
  exact Eventually.of_forall fun n x _ v _ _ tr =>
    (H n).curvatureOperatorLowerBoundAt_extendAt_of_pinched (hend n) (G n) (hGi n) (hat n)
      (hts n) (hpinch n).1 (hpinch n).2 v _

/-- trace-local 时间导数界（常数 `2·Ctime`、阈值 `2·qcan`）⇐ 数据前提 `hslab` / `hderG`
（`abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt`）。 -/
theorem hderiv_of_extendAt_P6D2
    {Ctime : ℝ≥0} {qcan : ℕ → ℝ}
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
      (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
        ((Hs n).activeStage_mono hvt) x,
        2 * qcan n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          ((2 * Ctime : ℝ≥0) : ℝ) * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2 := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  intro D T _ _
  refine Eventually.of_forall fun n x _ v hvt _ hvlt hreg tr hq => ?_
  have hq0 : 0 ≤ qcan n := (lt_of_lt_of_le (by positivity) (hqcan n)).le
  have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    hq0 (hslab n) (hderG n)
  exact ((H n).extendAt (hend n) (G n) (hGi n) (hat n)
    (hts n)).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt
    (t := (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))
    (t₀ := ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n) : ℝ)) le_rfl
    hdin.1 hdin.2.1 hdin.2.2 v hvlt hreg _ hq

/-- 基点 `R(ŷ) = R n`（private `metricScalarAt_extendAt_eq`）。 -/
theorem scal_of_extendAt_P6D2
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ)
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory)
    (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
    (hys : ∀ n, HEq (ys n) (y n)) (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n)) :
    ∀ n, metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n) = R n := by
  subst hHs
  obtain rfl := eq_of_heq hts'
  intro n
  rw [hRn n]
  exact RetainedCoreHistory.metricScalarAt_extendAt_eq (H n) (hend n) (G n) (hGi n) (hat n) (hts n)
    (y n) (ys n) (hys n)

/-- **G3：`htraced`（∀ A T）在 `RetainedCoreHistory` + `extendAt` 坏点序列上**：数据前提（同
`depthExtendable_add_of_windowAnchorBound`）+ 基点 anchor（L6 形）+ trace-local κ / witness / BCAD ⇒
存在子列 `σ`，所有深度 depth-extendable。pinching / 时间导数由数据前提给出（不另设前提）。 -/
theorem exists_subseq_htraced_extendAt_P6D2
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
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
    (hsurvive_of_extendAt_P6D2 hphi hinit hend hGi hrec hqcan hpar hscale hθcap hpinch hslab hat
      hts hderG hqR hnot hRt Hs ts ys R hHs hts' hys hRn)
    (hanchor0_of_extendAt_P6D2 hend hGi hat hts hanchor0 Hs ts ys R hHs hts' hys hRn)
    (hextend_of_extendAt_P6D2 hphi hinit hend hGi hrec hqcan hpar hscale hθcap hpinch hslab hat
      hts hderG hqR hnot hRt Hs ts ys R hHs hts' hys hRn)
    hr₀ hw hseed hκ ρnc hradii hkappa hphi
    (hpinch_of_extendAt_P6D2 hend hGi hat hts hpinch Hs ts ys R hHs hts')
    hε hεX hεN hqs hwit (Ctime := 2 * Ctime) (Cq := 2) (qcan := fun n => 2 * qcan n) hqcan2
    (hderiv_of_extendAt_P6D2 hend hGi hat hts hqcan hslab hderG Hs ts ys R hHs hts') hbcad

/-- **consumer（G3 ⇒ P6D G2）**：`htraced` 子列喂 P6D G2
`exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D`（常数 `epsW`、`C` 在序列前取）：
坏点子列
eventually 满足完整 `HasSpatialCanonicalTimeControl`（D-9.2）。pinching / 时间导数由数据前提给出；
`κ`
、witness、BCAD、基点 anchor 是 P6 剩余的 trace-local 前提。 -/
theorem exists_eventually_hasSpatialCanonicalTimeControl_extendAt_P6D2 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {D θcap qcan s t : ℕ → ℝ} → {p₀ p : ℕ → CutoffParameters} → {δb ρb : ℕ → ℝ} →
      {H : ℕ → RetainedCoreHistory.{u}} →
      {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)} →
      {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n)} →
      {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier} →
      (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory)) →
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) →
      (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount)) →
      (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n)) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount)) →
      (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) → (hts : ∀ n, t n < s n) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n)) →
      (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
        (D n) (θcap n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop) →
      (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n)) →
      (Hs : ℕ → ObservedHistory.{u}) → (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) →
      (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) → (R : ℕ → ℝ) →
      (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory) →
      (hts' : HEq ts (fun n => (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) →
      (hys : ∀ n, HEq (ys n) (y n)) → (hRn : ∀ n, R n = (G n).flow.scalar (t n) (y n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
          ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
              ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
                (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
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
                (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} →
      {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
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
              Wt.capTubeHasNeckChart ε) →
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
                (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
        (Hs (σ (ψ i))).HasSpatialCanonicalTimeControl ε C C C.toNNReal (ts (σ (ψ i)))
          (ys (σ (ψ i))) := by
  obtain ⟨epsW, hepsW, hB⟩ :=
    exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW
  refine ⟨C, hC, ?_⟩
  intro P₀ g₀ Ctime phi hphi D θcap qcan s t p₀ p δb ρb H records G y hinit hend hGi hrec hqcan
    hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hRt hanchor0 Hs ts ys R hHs hts' hys hRn
    r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwit hbcad
  obtain ⟨σ, hσ, hall⟩ := exists_subseq_htraced_extendAt_P6D2 hphi hinit hend hGi hrec hqcan
    hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hRt hanchor0 Hs ts ys R hHs hts' hys hRn
    hr₀ hw hseed hκ ρnc hradii hkappa hε hεX hεN hqs hwit hbcad
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
  have hscal := scal_of_extendAt_P6D2 hend hGi hat hts Hs ts ys R hHs hts' hys hRn
  have hpinchL := hpinch_of_extendAt_P6D2 hend hGi hat hts hpinch Hs ts ys R hHs hts'
  have hderivL := hderiv_of_extendAt_P6D2 hend hGi hat hts hqcan hslab hderG Hs ts ys R hHs hts'
  obtain ⟨-, ψ, hψ, hev⟩ := hB' (fun m => Hs (σ m)) (fun m => ts (σ m)) (fun m => ys (σ m))
    (fun m => R (σ m)) (fun m => hR (σ m)) (fun m => hscal (σ m)) (hRlim.comp hσ.tendsto_atTop)
    (fun A T hA hT => hall T hT A hA) hr₀ hw (hσ.tendsto_atTop.eventually hseed) hκ
    (fun m => ρnc (σ m)) (hradii.comp hσ.tendsto_atTop)
    (fun D T hD hT => hσ.tendsto_atTop.eventually (hkappa D T hD hT)) hphi
    (fun D T hD hT => hσ.tendsto_atTop.eventually (hpinchL D T hD hT)) (fun m => hqs (σ m))
    (fun m => hqcan2 (σ m)) (fun D T hD hT => hσ.tendsto_atTop.eventually (hwit D T hD hT))
    (fun D T hD hT => hσ.tendsto_atTop.eventually (hderivL D T hD hT))
  exact ⟨σ, hσ, ψ, hψ, hev⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
