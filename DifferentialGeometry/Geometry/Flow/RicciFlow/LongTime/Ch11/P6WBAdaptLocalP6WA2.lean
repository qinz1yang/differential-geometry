import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WBAdaptP6WA2

/-!
# SLT 核局部孪生 / anchor 局部孪生的 `hWBloc`-free 版（O-CH11-WBADAPT G2，后缀 `_P6WA2`）

G1 `hWBloc_of_shortSLT_guarded_P6WA2`（PROVED，结论逐字 = `hWBloc` binder 类型）喂 SLTLOCAL G1
（`P6SLTLocalP6SL.lean`）的三个定理，得到**无 `hWBloc` 的孪生**：陈述 = 原陈述逐字去掉 `(hWBloc : …)`
binder 块（生成器 `build-logs/scratch/O-CH11-WBADAPT/gen2.py` 断言字节相等），证明 = 原定理 `@` 全参数调用。
* `RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6WA2`（**PROVED**）：SLT 核
  `…_window_P6M` 的坏点尺度局部孪生；前 slab 输入 = 局部合同 `hslabsLoc`（`∀ Rad B c, ∀ᶠ n`，guard
  `(t n − v)·max (q n) (R(t n, z)) ≤ c`），其余输入与 P6M 核同形。
* `RetainedCoreHistory.hanchor0_lateW_local_P6WA2` /
  `ObservedHistory.hanchor0_eventSlab_local_P6WA2`
  （**PROVISIONAL[`hslabsLoc`]**）：J10GEN3 anchor 两层的局部孪生，`hWBloc` 已付，唯一非 kernel 前提 =
  `hslabsLoc`（producer：O-CH11-SLTPROD；anchor 帧 `q := Cg·R`）。
**SLTLOCAL2-A/B 的 `hTPloc` 路线对 `hWBloc` 而言是多余的**（`hWBloc_of_hTPloc_P6SL` 不再是唯一来源）。
**不生产** `hslabsLoc`；slice `hqRR` birth 比较、final 对应件、exp 版本七层 wrapper 不在本文件；
不声称 J10 已去。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **SLT 核坏点尺度局部孪生，`hWBloc` 已付（`_P6WA2`，PROVED）**：
`RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6SL` 逐字去掉 binder `hWBloc`，
由 `hWBloc_of_shortSLT_guarded_P6WA2`（guarded ShortSLT 直接适配）支付。 -/
theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6WA2
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cq θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hqy : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    {p : ℕ → CutoffParameters} (T₀ : ℕ → ℝ)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hT b, ((records n i hT).static b).hasCanonicalWindow)
    (hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop)
    (horder : ∀ n, 2 ≤ (p n).modelOrder)
    (haccuracy : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabsLoc : ∀ Rad B c : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      (t n - v) * max (q n) ((G n).flow.scalar (t n) z) ≤ c →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hder : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hpinch : ∀ B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
          Ici (t n - B / ((G n).flow.scalar (t n) (y n)))) phi)
    (hpinchG : ∀ B : ℝ, ∀ᶠ n in atTop, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
        Ici (t n - B / ((G n).flow.scalar (t n) (y n)))) phi)
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hG n)
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
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (D θ : ℕ → ℝ) (hD : Tendsto D atTop atTop) (hθ : ∀ n, θ₀ ≤ θ n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (Btr : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      Btr.point j.succ le_rfl hl = ((records n j hT).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θ n * (((records n j hT).static b).neck.scale)⁻¹) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) :=
  @RetainedCoreHistory.eventually_scalar_bound_at_distance_window_local_P6SL.{u}
    hWBloc_of_shortSLT_guarded_P6WA2.{u} ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi Cq θ₀ hθ₀ H hend s G
    hG t ht hts y q ρ hq hqy hR hRt p T₀ hT₀ records hcan hradius horder haccuracy hW hslabsLoc hder
    hgrad hpinch hpinchG hnc hρ D θ hD hθ hnot

/-- **anchor 局部孪生，`hWBloc` 已付（`_P6WA2`，PROVISIONAL[`hslabsLoc`]）**：
`RetainedCoreHistory.hanchor0_lateW_local_P6SL` 逐字去掉 binder `hWBloc`。 -/
theorem RetainedCoreHistory.hanchor0_lateW_local_P6WA2
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap s t ρ T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
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
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n))
    {Cq : ℝ} (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqC : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hslabsLoc : ∀ Rad B c : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      (t n - v) * max (q n) ((G n).flow.scalar (t n) z) ≤ c →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderSel : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (y n) (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
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
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) :=
  @RetainedCoreHistory.hanchor0_lateW_local_P6SL.{u} hWBloc_of_shortSLT_guarded_P6WA2.{u} ε hεle κ
    C1 C2 hκ Ctime Cgrad phi hphi D θcap s t ρ T₀ p δb H records G y hend hGi hcan hpar hθcap hpinch
    hat hts hnot hT₀ hRt hR hRpos Cq q hq hqC hslabsLoc hderSel hW hgrad hnc hρ

namespace ObservedHistory

/-- **anchor 处的实际切换（kernel 帧），`hWBloc` 已付（`_P6WA2`，PROVISIONAL[`hslabsLoc`]）**：
`ObservedHistory.hanchor0_eventSlab_local_P6SL` 逐字去掉 binder `hWBloc`；唯一非 kernel 前提 = 坏点尺度局部
合同 `hslabsLoc`（K 帧，`q := Cg·R`），producer 见 O-CH11-SLTPROD。 -/
theorem hanchor0_eventSlab_local_P6WA2
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
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
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hslabsLoc : ∀ Rad B c : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤ c →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
  @ObservedHistory.hanchor0_eventSlab_local_P6SL.{u} hWBloc_of_shortSLT_guarded_P6WA2.{u} ε C1' C2'
    Ctime' hεcone hC20 phi hphi K j t hjt htj D θcap T₀ p δb records yG hcan hpar hθcap hpinch hnot
    hT₀ hRt Kh hKh σ hσ y hyG R hRpos hRn hRlt κd hκd hvolK Tn aSeed haT hsT has pT seedTrace L hL
    Cg hCg hgood hwin hdistW hslabsLoc

end ObservedHistory

/-- consumer（G2，sanity）：旧全局槽 `hslabsSel` ⇒ 新局部槽（`hslabsLoc_of_hslabs_P6SL`）⇒ 本文件 kernel 帧
anchor 孪生 ⇒ J10GEN3 原定理 `hanchor0_eventSlab_noJ10_P6JG3`，**无 `hWBloc`**。 -/
example : type_of% @ObservedHistory.hanchor0_eventSlab_noJ10_P6JG3.{u} := by
  intro ε C1' C2' Ctime' hεcone hC20 phi hphi K j t hjt htj D θcap T₀ p δb records yG hcan hpar
    hθcap hpinch hnot hT₀ hRt Kh hKh σ hσ y hyG R hRpos hRn hRlt κd hκd hvolK Tn aSeed haT hsT has
    pT seedTrace L hL Cg hCg hgood hwin hdistW hslabsSel
  exact ObservedHistory.hanchor0_eventSlab_local_P6WA2 hεcone hC20 hphi hjt htj hcan hpar
    hθcap hpinch hnot hT₀ hRt Kh hKh σ hσ y hyG R hRpos hRn hRlt hκd hvolK Tn aSeed haT hsT has pT
    seedTrace L hL hCg hgood hwin hdistW
    (hslabsLoc_of_hslabs_P6SL (G := fun n => ((K n).toHistory.event (j n)).incoming)
      (H := fun n => (K n).prefixAt (j n).castSucc) (y := yG) (q := fun n => Cg * R n) hslabsSel)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
