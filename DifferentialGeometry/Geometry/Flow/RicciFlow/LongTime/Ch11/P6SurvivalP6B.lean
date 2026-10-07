import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionDepthInduction

/-!
# P6 / L7 = M6：survival with anchor ⇒ traced region（O-CH11-P6B G3，后缀 `_P6B`）

P6A 的 L6（E-local，底座 `ST/BoundedCurvatureAtDistanceSliceTerminal.lean:249`）在坏点 `(t, y)`
（terminal 形：history 截在最后一个 event，`y` 在 incoming slab `G` 的时刻 `t`）给出 **anchor**
`∀ z ∈ B_t(y, A/√R(y)), R(z) ≤ Q·R(y)`（`:249` 的结论形，逐字）。本文件把它接成 **traced region**
（深度 `T/R(y)`、`|Rm| ≤ K₀·R(y)`），全部用树内定理：

1. anchor 经 `extendAt`（history 用 `G` 的 closed prefix 延长到 `t`）搬到延长后的 history
   （树内 private `scalar_le_on_ball_extendHorizon_of_final_slab`，`open private`）；
2. 延长 history 上的 event slab 导数界（`derivativeBound_inputs_extendAt`）+ anchor ⇒
   **沿所有存在的 backward trace `R ≤ 2Q·R(y)`**
   （`scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball`，
   跨 surgery 的 ODE 比较；深度受 `2·(2Ctime)·Q·T ≤ 1` 限制）；
3. 沿 trace 的界 + 细 canonical records + pinching + `¬ CapWindowPoint` ⇒ traced region
   （`exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces`，
   内部是 traced region / cap window
   二分 `exists_isTracedRegion_or_capWindowPoint_at_scale`，cap 分支由 `¬ CapWindowPoint` 排除）。

数据前提（records 族、`hpar` 细化、`hscale` cap 尺度、pinching、slab 导数界、`¬ CapWindowPoint`）与树内
`CrossingTracedRegion:70` 逐字相同——与 `:249` 同源（D-P5 / D-P2，P6A design rev1）。没有新命名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private RetainedCoreHistory.scalar_le_on_ball_extendHorizon_of_final_slab from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionDepthInduction

namespace RetainedCoreHistory

/-- **L7（单窗口）**：`:249` 形 anchor（`B(y, A/√R)` 上 `R ≤ Q R`，`Q ≥ 2`）+ 深度 `T` 满足
`4·Ctime·Q·T ≤ 1` 与 `T ≤ R(y)·t` + 树内数据前提 ⇒ 最终在延长 history 里 `y` 处有 traced region
（半径 `A/√R`、深度 `T/R`、`|Rm| ≤ K₀ R`），`K₀` 与 `n` 无关。 -/
theorem exists_eventually_isTracedRegion_extendAt_of_anchor_P6B
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
    {A T Q : ℝ} (hA : 0 < A) (hT : 0 < T) (hQ2 : 2 ≤ Q)
    (hstep : 4 * (Ctime : ℝ) * Q * T ≤ 1)
    (hdepth : ∀ n, T ≤ (G n).flow.scalar (t n) (y n) * t n)
    (hanchor : ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n)) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
      ∀ ŷ : (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageAt
          ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))).Carrier,
      HEq ŷ (y n) →
      ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.isTracedRegion
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) ŷ
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))
        (T / (G n).flow.scalar (t n) (y n)) (K₀ * (G n).flow.scalar (t n) (y n)) := by
  obtain ⟨K₀, hK₀, hev⟩ := exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces
    hphi hinit hend hGi hrec hqcan hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hA hT
    (by linarith)
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev, hanchor] with n hn han
  intro ŷ hŷ
  have hq0 : 0 < qcan n := lt_of_lt_of_le (by positivity) (hqcan n)
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := hq0.trans (hqR n)
  have hTR : T / (G n).flow.scalar (t n) (y n) ≤ t n := by
    rw [div_le_iff₀ hR0]
    linarith [hdepth n]
  let uu : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon :=
    ⟨t n - T / (G n).flow.scalar (t n) (y n), by linarith,
      (sub_le_self _ (div_pos hT hR0).le).trans
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)).2.2⟩
  have hut : uu ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n) := by
    change t n - T / (G n).flow.scalar (t n) (y n) ≤ t n
    linarith [div_pos hT hR0]
  have hlast : ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) = Fin.last (H n).eventCount :=
    (H n).activeStage_extendHorizon_eq_last ((hend n) ▸ (hat n).le)
      ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n)
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) (hat n).le
  have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    hq0.le (hslab n) (hderG n)
  have hball := RetainedCoreHistory.scalar_le_on_ball_extendHorizon_of_final_slab (H n)
    ((hend n) ▸ (hat n).le) ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n) (y n) han
    ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) rfl _ hlast ŷ hŷ
  refine hn ŷ hŷ uu rfl ?_
  refine RetainedCoreHistory.scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball
    ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)) (Ctime := 2 * Ctime)
    (qcan := 2 * qcan n)
    (T := T) hR0 (by linarith) ?_ rfl hut hdin.1 hdin.2.1 hdin.2.2 ?_ ŷ hball
  · push_cast
    linarith
  · nlinarith [hqR n]

/-- consumer：L7 的输出正是 M8 装配 `exists_local_ancient_limit_kappa_noncollapsed_P6B` 的 `htraced`
在固定 `(A, T)` 处的形（坏点序列 `ŷ n`，history = 延长后的 `extendAt`，尺度 `R n = R(y n)`）。 -/
example
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
    {A T Q : ℝ} (hA : 0 < A) (hT : 0 < T) (hQ2 : 2 ≤ Q)
    (hstep : 4 * (Ctime : ℝ) * Q * T ≤ 1)
    (hdepth : ∀ n, T ≤ (G n).flow.scalar (t n) (y n) * t n)
    (hanchor : ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n))
    (ŷ : ∀ n, (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageAt
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))).Carrier)
    (hŷ : ∀ n, HEq (ŷ n) (y n)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.isTracedRegion
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) (ŷ n)
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))
        (T / (G n).flow.scalar (t n) (y n)) (K * (G n).flow.scalar (t n) (y n)) := by
  obtain ⟨K₀, hK₀, hev⟩ := exists_eventually_isTracedRegion_extendAt_of_anchor_P6B hphi hinit
    hend hGi hrec hqcan hpar hscale hθcap hpinch hslab hat hts hderG hqR hnot hA hT hQ2 hstep
    hdepth hanchor
  exact ⟨K₀, hK₀, hev.mono fun n hn => hn (ŷ n) (hŷ n)⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
