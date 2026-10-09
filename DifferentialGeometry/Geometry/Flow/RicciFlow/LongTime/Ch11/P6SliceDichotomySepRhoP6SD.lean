import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceLateCgLocalP6SD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSlabsCaseP6SB2

/-!
# 切片二分 D1 合取以 w 为中心的三分 producer：去 `hstaySlC`（O-CH11-SLICEDICH G3，后缀 `_P6SD`）

G2 的 L6 / L7 吃 `hstaySlC`（U 点短深度跨 surgery stay 的条件形）。lead 08:3x 核查要求：SLICE-BCBD2 G8
（`hslabs_of_sepRho_supply_P6SB2`，中心 = kernel 坏点 y）的三分法能否以 U 侧中心 w 重做。结论：能——D1 的 guard
已含端点标量 `max(Cg·R n, R(v, z))`，且 `hstaySlC` 只经 "stay ⇒ hgood ⇒ Dt" 被消费，故直接生产 D1：
* `prefixTraceOfHistory_P6SD`：history → prefix trace（定义层搬运）。
* L6″ `hUVC_of_selection_Cg_sepRho_P6SD`：(A) 先验供给 / (B) clipped reciprocal 反证 / (C) CXJD stay 以
  `(v, w, L/2)` 重新锚定（seed 预算：w 的 Good 条件 `L/2` + stay 的 `L/2` = hgood 的 `L`）。
* L7″ `hbcadC_of_hclosC_sepRho_P6SD`：PROVISIONAL[`hclosC`, `hdistQC`, `hslabK`@天花板, `hscaleK` ⇐
  (SEP-ρ⁺), CXJD 结构输入族]，**无 `hqR`、无 `hstaySlC`**。consumer = 喂 P6KA driver `hbcadC` 槽。
不声称 J10 已去：`hslabK`（天花板级先验供给）与 `hscaleK`（⇐ (SEP-ρ⁺) ⇐ C12-7）仍是输入；`hclosC` = B2。
生成器 `build-logs/scratch/O-CH11-SLICEDICH/gen/gen3.py`（从 G2 文件逐字切片 + assert 替换）。
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

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

/-- **history trace ⇒ prefix trace（`_P6SD`）**：`backwardPointTraceOfPrefix` 的逆向：终点为 `k` 的
history trace（起点 `castLE first`）限制成 `prefixAt k` 的 trace（终点 `Fin.last`）；逐点、crossing 都是定义层搬运。 -/
def prefixTraceOfHistory_P6SD (K : RetainedCoreHistory.{u}) (k : Fin (K.eventCount + 1))
    {first : Fin ((K.prefixAt k).eventCount + 1)}
    {hle : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ k}
    {z : (K.stage k).Carrier}
    (A : BackwardPointTrace K.toHistory
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first) k hle z) :
    BackwardPointTrace (K.prefixAt k).toHistory first (Fin.last (K.prefixAt k).eventCount)
      (Fin.le_last first) z where
  point m hm1 hm2 := A.point (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) m) hm1
    (Fin.le_def.mpr (Fin.le_def.mp hm2))
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) hf hl

end RetainedCoreHistory

/-- **L6″ 条件形 `hUVC` 扩展 ⇐ `hgood` + `hclosC` + 先验供给 + `hscaleK` + CXJD 族（`_P6SD`，PROVED ⇐
这些前提；**无 `hstaySlC`**）**：G2 L6 的孪生，D1 合取改由 SLICE-BCBD2 G8 三分法以 **w 为中心**生产：
`Qm := max(n+1, Q n)`；(A) `R(v′, x) > Qm`：`hslabK` 逐点；(B) `R(v′, x) ≤ Qm < R(v, z)/2`：
`scalar_gt_of_slabs_prefix_P6SB2` 反证；(C) 其余：`stay_cstar_prefix_sepRho_P6SB2` 以
`(σ, y, L) := (v, w, L/2)` 重新锚定（hgood′ ⇐ hgood：w 的 Good 条件给 seed 预算 `L/2`，窗口
eventually），跨越 record 的分离
⇐ `hscaleK`（`Cg·R n < R(v′, x) ≤ Qm` ⇒ `Qb·R n ≤ 2Qm`），再经 hgood 时间分量得 Dt。D1 的 full-history
trace 经 `prefixTraceOfHistory_P6SD` 转 prefixAt 形。 -/
theorem ObservedHistory.hUVC_of_selection_Cg_sepRho_P6SD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
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
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    {K : ℕ → RetainedCoreHistory.{u}} (hKh : Kh = fun n => (K n).toHistory) (hCg : 1 ≤ Cg)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {Q T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            |derivWithin (fun s => ((Kh n).event j').incoming.flow.scalar s x) (Iic v') v'| ≤
              Ctime' * ((Kh n).event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (Kh n) first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((Kh n).event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime' * ((Kh n).event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κs, hκdef⟩ : ∃ κs : ℝ, κs = min (min (rX / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hCc : (Ctime' : ℝ) * (1 / (2 * max (Ctime' : ℝ) 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [le_max_left (Ctime' : ℝ) 1]
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hclosC Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    Filter.Eventually.filter_mono hφt
      (hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1))),
    Filter.Eventually.filter_mono hφt (hwin (max B 0 - σ₁ + 1) (by linarith)),
    Filter.Eventually.filter_mono hφt hκR, Filter.Eventually.filter_mono hφt hdistσ,
    Filter.Eventually.filter_mono hφt (hL.eventually_ge_atTop (max (max
      (8 * localPropagationRadius C2')
      (4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4)) 2)),
    Filter.Eventually.filter_mono hφt (hT₀ (max B 0 - σ₁ + 1)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop 9),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop (6 / rX ^ 2 + 1)),
    Filter.Eventually.filter_mono hφt (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (ge_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 2))))]
    with n hcl hLn hwn hκn hdσ hLX2 hT₀n hTEn h9 hr6 hacn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hcl' := hcl j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hwinB : ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ →
      (aSeed n : ℝ) ≤ τ ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ τ := fun τ hτ => by
    obtain ⟨e1, e2⟩ := window_P6L3 hRn hRw hvσ1 hτ le_rfl hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hwin0 : (aSeed n : ℝ) ≤ v ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ v := by
    have hX0 : max 0 0 - σ₁ + 1 ≤ max B 0 - σ₁ + 1 := by
      rw [max_self]
      linarith [le_max_right B 0]
    obtain ⟨e1, e2⟩ := window_P6L3 (B := 0) (τ := v) hRn hRw hvσ1 (by simp) hX0 hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hRx
    exact (Kh n).witness_of_hgood_slab_Cg_P6LS3 (haT n) (hsT n) (has n) (seedTrace n) (y n) (R n)
      (L n) (hgood n) j' v hv1 hv2 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_P6L3 (Kh n) j' v _ w x _ hRn hRw hL0 hRad hwseed hx) hRx.le
  · intro x hx v' hv' hBv' hRx ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).gradient_of_hgood_slab_Cg_P6LS3 hC2 (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le ξ
  · have ha : (Tn n : ℝ) - r n ^ 2 / 2 ≤ v - B / ((Kh n).event j').incoming.flow.scalar v w :=
      (hroom n).trans (hwinB _ le_rfl).2
    exact regionalKappa_of_closure_P6L3 (Kh n) (haT n) (hsT n) (has n) (seedTrace n) (y n) hRn hL0
      hκn hdσ j' _ _ v ha (hvσ.trans (hsT n)) h1 h2
      (fun τ haτ hτv hτ1 _ x hx => hcl' x hx τ haτ hτv hτ1)
  · intro x hx v' hv' hBv' hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).deriv_of_hgood_slab_Cg_P6SD (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le
  · intro i first hf hij z hz Btr v' hv' hBv' hg hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    obtain ⟨e1, -⟩ := window_P6L3 hRn hRw hvσ1 hBv' le_rfl hX1 hLX
    have hT₀v' : T₀ n ≤ v' := hT₀n.trans e1
    have hsj : i.succ ≤ j'.castSucc := Fin.le_def.mpr (by
      have := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega)
    have hv'v : v' < v :=
      hv'.2.trans_le (((Kh n).time_strictMono.monotone hsj).trans hv1.le)
    have htv0 : 0 ≤ v - v' := sub_nonneg.mpr hv'v.le
    have h0 : (0 : ℝ) ≤ v' := ((Kh n).time_nonneg _).trans hv'.1.le
    have h0v : (0 : ℝ) ≤ v := h0.trans hv'v.le
    have hR1 : (1 : ℝ) ≤ R n := by
      have e1 := hRn1 n
      have e2 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith only [e1, e2]
    have hL2 : (2 : ℝ) ≤ L n := (le_max_right _ _).trans hLX2
    have hLρ : 8 * localPropagationRadius C2' ≤ L n :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hLX2
    have hLc : 4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4 ≤ L n :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hLX2
    have hRle : (v - v') * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
      have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hRn.le hCg).trans
        (le_max_left (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z))) htv0
      exact h3.trans hg
    have hTv : v - v' ≤ 1 / R n := by
      rw [le_div_iff₀ hRn]
      exact hRle.trans hc1
    have hwinJ : ∀ s : ℝ, v - (L n / 2) ^ 2 / R n ≤ s → (σ n : ℝ) - L n ^ 2 / R n ≤ s := by
      intro s hs
      have hLa : -σ₁ + 1 ≤ L n := by linarith only [hLX, le_max_right B 0]
      have hσ0 : σ₁ < 0 := lt_of_le_of_lt h12 hσ₂
      have hsq := mul_le_mul hLa hLa (by linarith only [hσ0]) hL0
      have hA' : 0 ≤ σ₁ + 3 / 4 * L n ^ 2 := by
        nlinarith only [hsq, sq_nonneg (σ₁ - 1 / 3)]
      have hdiv : 0 ≤ (σ₁ + 3 / 4 * L n ^ 2) / R n := div_nonneg hA' hRn.le
      have heq : (σ₁ + 3 / 4 * L n ^ 2) / R n =
          σ₁ / R n + L n ^ 2 / R n - (L n / 2) ^ 2 / R n := by
        rw [add_div, mul_div_assoc, div_pow]
        ring
      linarith only [hvσ1, hdiv, heq, hs]
    have hrr : Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) ≤
        max Rad 0 / Real.sqrt (R n) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left (le_max_right _ _) (Real.sqrt_pos.2 hRn)
          (Real.sqrt_le_sqrt hRw))
    have hz' := riemannianBallOf_mono _ _ hrr hz
    have hQ1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hQ0 : 0 < max ((n : ℝ) + 1) (Q n) := lt_of_lt_of_le (Nat.cast_add_one_pos n) hQ1
    subst hKh
    have hslabQ : (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (Q n))
        (Fin.last (K n).eventCount) :=
      fun e he y' t' ht hR' => hslabK n e he y' t' ht ((le_max_right _ _).trans_lt hR')
    by_cases hA : max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event i).incoming.flow.scalar v' (Btr.point i.castSucc hf hij.le)
    · -- (A) 天花板以上：先验供给逐点
      exact hslabQ i (Fin.castSucc_lt_last i) _ v' hv' hA
    push Not at hA
    let vJ : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, h0v, hvσ.trans (σ n).2.2⟩
    let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨v', h0, (hv'v.le.trans hvσ).trans (σ n).2.2⟩
    have hvJσ : vJ ≤ σ n := hvσ
    have hvJT : vJ ≤ Tn n := hvJσ.trans (hsT n)
    have hvJa : aSeed n ≤ vJ := hwin0.1
    have hvIJ : vI ≤ vJ := hv'v.le
    have hvIa : aSeed n ≤ vI := ha
    have hactJ : (K n).toHistory.activeStage vJ = j'.castSucc :=
      (K n).toHistory.activeStage_eq_of_slab_P6L3 j' vJ hv1.le hv2
    have hik : i.val < ((K n).prefixAt j'.castSucc).eventCount := by
      have := Fin.lt_def.mp hij
      simp only [Fin.val_castSucc] at this
      exact this
    let ip : Fin ((K n).prefixAt j'.castSucc).eventCount := ⟨i.val, hik⟩
    have hfi : first.val < ((K n).prefixAt j'.castSucc).eventCount + 1 := by
      have := Fin.le_def.mp hf
      simp only [Fin.val_castSucc] at this
      omega
    let fp : Fin (((K n).prefixAt j'.castSucc).eventCount + 1) := ⟨first.val, hfi⟩
    have hfp : fp ≤ ip.castSucc := Fin.le_def.mpr (Fin.le_def.mp hf)
    let Btrp := (K n).prefixTraceOfHistory_P6SD j'.castSucc (first := fp) Btr
    by_cases hB : 2 * max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event j').incoming.flow.scalar v z
    · -- (B) 不可能：trace 下界（clipped reciprocal）
      exfalso
      have hRz : (v - v') * ((K n).toHistory.event j').incoming.flow.scalar v z ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hg
      have htime : (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar vJ z *
          ((vJ : ℝ) - vI) ≤ 1 / 2 := by
        change (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar v z * (v - v') ≤
          1 / 2
        have h1' := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
        calc (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar v z * (v - v')
            = (Ctime' : ℝ) * ((v - v') *
              ((K n).toHistory.event j').incoming.flow.scalar v z) := by ring
          _ ≤ 1 / 2 := h1'.trans hCc
      have hgt := (K n).scalar_gt_of_slabs_prefix_P6SB2 hQ0 hslabQ j' vJ hactJ ip fp hfp z Btrp vI
        hv'.1 hv'.2 hvIJ hB htime
      exact absurd hgt (not_lt.mpr hA)
    push Not at hB
    -- (C) 天花板以下：CXJD stay 以 (v, w, L/2) 重新锚定 + hgood
    obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
        (((K n).toHistory.event j').incoming.flow.scalar v z / R n) Cg) 1 := ⟨_, rfl⟩
    obtain ⟨Tt, hTdef⟩ : ∃ Tt : ℝ, Tt = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
    have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
    have hQbM : Qb * R n ≤
        max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) := by
      have hCgR : R n ≤ Cg * R n := le_mul_of_one_le_left hRn.le hCg
      have hle : Qb ≤ max (Cg * R n)
          (((K n).toHistory.event j').incoming.flow.scalar v z) / R n := by
        rw [hQbdef]
        refine max_le (max_le ?_ ?_) ?_
        · exact div_le_div_of_nonneg_right (le_max_right _ _) hRn.le
        · rw [le_div_iff₀ hRn]
          exact le_max_left _ _
        · rw [le_div_iff₀ hRn, one_mul]
          exact hCgR.trans (le_max_left _ _)
      calc Qb * R n ≤ max (Cg * R n)
            (((K n).toHistory.event j').incoming.flow.scalar v z) / R n * R n :=
          mul_le_mul_of_nonneg_right hle hRn.le
        _ = _ := div_mul_cancel₀ _ hRn.ne'
    have hQbQ : Qb * R n ≤ 2 * max ((n : ℝ) + 1) (Q n) :=
      hQbM.trans (max_le (by linarith only [hRx, hA, hQ0]) hB)
    have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
    have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
      linarith only [hrad n, hTEn]
    have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
      (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
    have hscale' : ∀ (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).time e.succ) b,
        (vI : ℝ) < (K n).toHistory.time e.succ → e.succ ≤ (K n).toHistory.activeStage vJ →
        2 * max (3 / rX ^ 2) (2 * (Qb * R n)) < ((recordsK n e he).static b).neck.scale := by
      intro e he b' _ _
      have hS := hscaleK n e he b'
      have h8 : 8 * max ((n : ℝ) + 1) (Q n) < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
        nlinarith only [h9, hQ0]
      have hn1 : (1 : ℝ) ≤ max ((n : ℝ) + 1) (Q n) :=
        le_trans (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hQ1
      have hnQ : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) :=
        le_mul_of_one_le_right (Nat.cast_add_one_pos n).le hn1
      have h6 : 6 / rX ^ 2 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
        linarith only [hnQ, hr6]
      have h63 : 2 * (3 / rX ^ 2) = 6 / rX ^ 2 := by ring
      have hmx : max (3 / rX ^ 2) (2 * (Qb * R n)) <
          ((recordsK n e he).static b').neck.scale / 2 :=
        max_lt (by linarith only [h6, hS, h63]) (by linarith only [hQbQ, h8, hS])
      linarith only [hmx]
    have hRa' : 1 ≤ R n * vI := by
      have := mul_le_mul_of_nonneg_left ha hRn.le
      change 1 ≤ R n * v'
      linarith only [this, hRa n]
    have haL : (vJ : ℝ) - (L n / 2) ^ 2 / R n ≤ vI := by
      have h1L : 1 / R n ≤ (L n / 2) ^ 2 / R n :=
        div_le_div_of_nonneg_right (by nlinarith only [hL2]) hRn.le
      change v - (L n / 2) ^ 2 / R n ≤ v'
      linarith only [h1L, hTv]
    let w' : ((K n).toHistory.stageAt vJ).Carrier :=
      cast (congrArg (fun m => ((K n).stage m).Carrier) hactJ.symm) w
    have hww : HEq w' w := cast_heq _ _
    have hwJ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage vJ) vJ)
          ((seedTrace n).point ((K n).toHistory.activeStage vJ)
            ((K n).toHistory.activeStage_mono hvJa) ((K n).toHistory.activeStage_mono hvJT)) w' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) := by
      have hs := point_heq_of_eq_P6M2 (seedTrace n) hactJ ((K n).toHistory.activeStage_mono hvJa)
        ((K n).toHistory.activeStage_mono hvJT) h1 h2
      exact (edist_stage_eq_P6L2 j' hactJ v _ w' _ w hs hww).trans_le hwseed
    have hc' : 0 ≤ L n / 2 / Real.sqrt (R n) :=
      div_nonneg (div_nonneg hL0 (by norm_num)) (Real.sqrt_nonneg _)
    have hbud : riemannianEDistOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage vJ) vJ)
          ((seedTrace n).point ((K n).toHistory.activeStage vJ)
            ((K n).toHistory.activeStage_mono hvJa) ((K n).toHistory.activeStage_mono hvJT)) w' +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
      refine (add_le_add hwJ le_rfl).trans_eq ?_
      rw [add_assoc, ← ENNReal.ofReal_add hc' hc']
      congr 2
      ring
    have hdw := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hdfin n, ENNReal.ofReal_ne_top⟩) hwJ
    obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R n)
      (Rad := max Rad 0) (L := L n / 2) hrX hρ hc0 hQb1 hR1 hκdef (by linarith only [hLρ])
      (by linarith only [hLc])
    have hTeq : Tt / R n = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R n := by rw [hTdef]
    rw [← hTeq] at hnum
    have hstay := stay_cstar_prefix_sepRho_P6SB2 hC2 hCg (K n) j' hv1 hv2 (σ := vJ) rfl (haT n)
      (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) hvJT hvJa w' w hww (L n / 2) hRn
      (fun v'' hav'' hvs'' hw'' z'' hd'' hR'' => hgood n v'' hav'' (hvs''.trans hvJσ)
        (hwinJ _ hw'') z'' (hd''.trans hbud) hR'')
      ip fp hfp z hz' Btrp vI hv'.1 hv'.2 hvIa hvIJ haL hRa' hQbdef hTdef hg hℓ hKℓ hℓr hKr hKC
      hℓρ hρL ((hT₀X n).trans ha) (hOldX n) (recordsK n) hT₀v' (hcanK n)
      (hacc1.trans (min_le_right _ _)) hDm' hncK hscale' (by linarith only [hL0]) hdw hnum
    exact ObservedHistory.slabDeriv_prefix_of_hgood_stay_P6SP (K n) j'.castSucc (haT n) (hsT n)
      (has n) (seedTrace n) (y n) (R n) (L n) (hgood n) ip
      (Btrp.point ip.castSucc hfp (Fin.le_last _)) vI hvIa (hvIJ.trans hvJσ) hv'.1 hv'.2 hLτ
      (fun x hx => (hstay x hx).trans hbud) hRx

/-- **L7″ event 支 `hbcadC` producer，无 `hstaySlC`（`_P6SD`，PROVISIONAL[`hclosC`, `hdistQC`,
`hslabK`@天花板, `hscaleK` ⇐ (SEP-ρ⁺), CXJD 结构输入族]）**：G2 L7 的孪生，`hstaySlC` 换成 CXJD 结构输入族
（`hsmall` / `hclock`@Tn、`hpin`、`hRa`、`T₀X` / `hOldX`、`hdfin`；与 SLICE-BCBD2 G8 同表），U 侧经 L6″。
J10 残余在切片二分里只剩 `hslabK`（阈值 `Q n`，天花板级先验供给）与 `hscaleK`（⇐ (SEP-ρ⁺)）。 -/
theorem ObservedHistory.hbcadC_of_hclosC_sepRho_P6SD
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hC2 : 0 ≤ C2) {Aκ : ℝ} (r : ℕ → ℝ)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  have hUVC := ObservedHistory.hUVC_of_selection_Cg_sepRho_P6SD (Ctime' := Ctime') (Cg := Cg) hC2
    Kh Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκR hclosC
    hKh hCg hRn1 hcanK hacc hrad hord hscaleK hslabK hT₀ hrX hsmall hclock aP haP hpin hRa T₀X
    hT₀X hOldX hdfin
  exact ObservedHistory.hbcadC_lateHI_of_slice_data_local_P6SD hεle hκ hphi hCg htj recordsF hHI
    hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y R hσ hRpos hRn1 hT₀ Tn aSeed
    haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hUVC

/-- **consumer（期 4 调用形，`_P6SD`）**：L7″ 的输出逐字付 `exists_subseq_forall_depthExtendable_kappaC_P6KA`
的 `hbcadC` 槽（G2 consumer 的孪生：`hstaySlC` → CXJD 结构输入族）。 -/
example
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hC2 : 0 ≤ C2) {Aκ : ℝ} (r : ℕ → ℝ)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n) →
        (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n)
    (hextend : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable Kh σ y R ψ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Kh (ψ i)).stageMetric
          ((Kh (ψ i)).activeStage (σ (ψ i))) (σ (ψ i))) (y (ψ i))
          (A / Real.sqrt (R (ψ i))),
      ∀ (w : Icc (0 : ℝ) (Kh (ψ i)).horizon),
        (w : ℝ) = σ (ψ i) - T' / R (ψ i) →
      ∀ (hwt : w ≤ σ (ψ i))
        (Bt : BackwardPointTrace (Kh (ψ i)) ((Kh (ψ i)).activeStage w)
          ((Kh (ψ i)).activeStage (σ (ψ i)))
          ((Kh (ψ i)).activeStage_mono hwt) x),
        metricScalarAt ((Kh (ψ i)).stageMetric ((Kh (ψ i)).activeStage w) w)
          (Bt.point ((Kh (ψ i)).activeStage w) le_rfl
            ((Kh (ψ i)).activeStage_mono hwt)) ≤
          M * R (ψ i)) →
      ObservedHistory.DepthExtendable Kh σ y R ψ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n))))
    {κd : ℝ} (hκd : 0 < κd) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κd * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))))
    {εd : ℝ} (hεd : 0 < εd) (hεXd : εd ≤ crossingWindowNeckAccuracy.{u})
    (hεNd : εd ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) εd C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart εd)
    {Ctimed : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctimed * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R ψ T := by
  have hb := ObservedHistory.hbcadC_of_hclosC_sepRho_P6SD hεle hκ hphi hCg htj recordsF hHI hcanK
    hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y R hσ hRpos hRn1 hT₀ Tn aSeed haT
    hsT has pT seedTrace L hL hwin ρV hρV hdistQC hC2 r hgood hroom hdistσ hκR hclosC hrX hsmall
    hclock aP haP hpin hRa T₀X hT₀X hOldX hdfin
  exact ObservedHistory.exists_subseq_forall_depthExtendable_kappaC_P6KA Kh σ y R hRpos hRlim
    hsurvive hanchor0 hextend hr₀ hw hseed hκd ρnc hradii hkappaC hPhi hpinch hεd hεXd hεNd hqs
    hwitC hqcan hderivC hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
