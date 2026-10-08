import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6JointFinalP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RerunJointEvent8P6R8B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6JointFinalContractP6R8B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RerunJointFinal8P6R8B

/-!
# 四主合同的无 J10 孪生（O-CH11-J10CONTRACT G1，R-C11-16 D-4 第三步前半）

`hgapJ` / `hgapJ8` / `hgapJF` / `hgapJF8` 四个主合同各生成一个 Prop def `*_noJ10_P6JK`：
与原 binder 逐字只差一行 = 结论 ∃ 元组里的 J10 合取（event 类 `c n * Qs n < R n`，第 13 个 ∧ 分量；
final 类 `Q n < R n`，第 16 个 ∧ 分量）。J9 的 `Qs` / `Q` 保留为存在量（D-3：不再要求 qcap < R，
不换名藏回）；final 类的 horizon cap 覆盖（`DerivativeBoundBefore … (K n).horizon`）原样保留（D-3 / D-7）。

canonical 源（generic hsel 常数 `η₁ C1₁ C2₁ Ctime₁`）：
* `hgapJ`   ← `Ch11/P6JointFinalP6CK.lean:758`（J10 :837；= frozen `O-CH11-P6CGK/hgapJ.txt`）
* `hgapJ8`  ← `Ch11/P6RerunJointEvent8P6R8B.lean:395`（J10 :474）
* `hgapJF`  ← `Ch11/P6JointFinalContractP6R8B.lean:458`（J10 :545）
* `hgapJF8` ← `Ch11/P6RerunJointFinal8P6R8B.lean:471`（J10 :558）
HRESTP / HP3 / Assemble / FinalCoarse 族的副本 = 同一文本（模 `^ (2 : ℕ)` 记法）在固定 hsel 常数
`p6FineEta_C11GT6 ε`、`p6CoarseC_C11GT6 (p6FineEta_C11GT6 ε)` 处的实例（gen.py A2 对 42 份副本断言；legacy 非 D 形
`canonicalLateCore_of_joint_P6CK` 的 hgapJ（`P6NormalizePrefixKappaP6CK.lean:570`）不属本族）。

本文件只登记合同，不改任何现有合同、不切换任何消费者；旧 ⇒ 新投影的兼容测试在
`P6GapContractsNoJ10CompatP6JK`（新 consumer 不依赖它）。生成器 `build-logs/scratch/O-CH11-J10CONTRACT/gen.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6)

/-- `hgapJ` 的无 J10 孪生（R-C11-16 D-3 / D-4 第三步；合同 Prop，PROVISIONAL，不切换消费者）。
源 = `Ch11/P6JointFinalP6CK.lean:758` 的 binder `hgapJ`（frozen txt 逐字一致，gen.py A2/A6）。
与原合同逐字只差一行：删去结论 ∃ 元组第 13 个 ∧ 分量
`(∀ n, c n * Qs n < R n)`（J10，源 :837）。J9 的 `Qs` 保留为存在量
（cap-age / EventSlabsDerivative 等合取仍用）。参数 = 原定理上下文里的自由变量。 -/
def hgapJ_noJ10_P6JK
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ) (Ctime : ℝ≥0)
    (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ) (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) : Prop :=
  ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
        ∀ z : ((Kh k).stageAt v).Carrier,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
              ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k))
                  ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (L k / Real.sqrt (R k)) →
          4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
          (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
      Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
      (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
      (σ k : ℝ) < (Kh k).time j.succ) →
      (∀ k : ℕ, (k : ℝ) + 1 < R k) →
    ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (Ho n).eventCount),
        max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
          GeometricCutoffRecord (Ho n).toHistory i (p n))
      (a₀ : ℝ),
      Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
      0 < a₀ ∧
      (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
        i.succ →
        (pF n).delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) ∧
      (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n i hi b, max (Qs n) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
      (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
        ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
        ((Ho n).unscaleTime_P6X (hc n) (σ n)))
        ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
    ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
      (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
      (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
        B / (R n / c n) ≤ v →
    ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
      ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
      ((Ho n).toHistory.activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
      (Ho n).toHistory.isParabolicallyRmControlledBall v
        (tr.point ((Ho n).toHistory.activeStage v) le_rfl
          ((Ho n).toHistory.activeStage_mono hvt))
        (ϱ / Real.sqrt (R n / c n)) →
      ENNReal.ofReal (κd * ϱ ^ 3) ≤
        ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
          ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
          (tr.point ((Ho n).toHistory.activeStage v) le_rfl
            ((Ho n).toHistory.activeStage_mono hvt)) ϱ) ∧
      (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
        (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
        (Ho n).time i.succ ∈ Icc (τ / 2) τ →
        ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
          (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (D / Real.sqrt (R n)),
    ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) x ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      ∀ z : ((Kh n).stageAt (σ n)).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
            ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
      (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
        (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
        (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
    (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
    (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
          ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
      ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
      (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
      ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        (Kh n).time j'.castSucc < s →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
            ((seedTrace n).point j'.castSucc h1 h2) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stage j'.castSucc).Carrier,
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
            ((Kh n).event j').incoming.flow.scalar s z ≤
              C * ((Kh n).event j').incoming.flow.scalar v w)

/-- `hgapJ8` 的无 J10 孪生（R-C11-16 D-3 / D-4 第三步；合同 Prop，PROVISIONAL，不切换消费者）。
源 = `Ch11/P6RerunJointEvent8P6R8B.lean:395` 的 binder `hgapJ8`（frozen txt 逐字一致，gen.py A2/A6）。
与原合同逐字只差一行：删去结论 ∃ 元组第 13 个 ∧ 分量
`(∀ n, c n * Qs n < R n)`（J10，源 :474）。J9 的 `Qs` 保留为存在量
（cap-age / EventSlabsDerivative 等合取仍用）。参数 = 原定理上下文里的自由变量。 -/
def hgapJ8_noJ10_P6JK
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (η₁ C1₁ C2₁ : ℝ) (Ctime₁ : ℝ≥0)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ)
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) : Prop :=
  ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
        ∀ z : ((Kh k).stageAt v).Carrier,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
              ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k))
                  ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (L k / Real.sqrt (R k)) →
          8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
          (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
      Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
      (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
      (σ k : ℝ) < (Kh k).time j.succ) →
      (∀ k : ℕ, (k : ℝ) + 1 < R k) →
    ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (Ho n).eventCount),
        max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
          GeometricCutoffRecord (Ho n).toHistory i (p n))
      (a₀ : ℝ),
      Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
      0 < a₀ ∧
      (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
        i.succ →
        (pF n).delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) ∧
      (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
        ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n i hi b, max (Qs n) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
      (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
        ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
        ((Ho n).unscaleTime_P6X (hc n) (σ n)))
        ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
    ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
      (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
      (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
        B / (R n / c n) ≤ v →
    ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
      ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
      ((Ho n).toHistory.activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
      (Ho n).toHistory.isParabolicallyRmControlledBall v
        (tr.point ((Ho n).toHistory.activeStage v) le_rfl
          ((Ho n).toHistory.activeStage_mono hvt))
        (ϱ / Real.sqrt (R n / c n)) →
      ENNReal.ofReal (κd * ϱ ^ 3) ≤
        ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
          ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
          (tr.point ((Ho n).toHistory.activeStage v) le_rfl
            ((Ho n).toHistory.activeStage_mono hvt)) ϱ) ∧
      (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
        (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
        (Ho n).time i.succ ∈ Icc (τ / 2) τ →
        ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
          (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
      (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (D / Real.sqrt (R n)),
    ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) x ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      ∀ z : ((Kh n).stageAt (σ n)).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
            ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
      (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
        (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
        (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
    (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
    (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
          ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
      ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
      (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
      ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        (Kh n).time j'.castSucc < s →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
            ((seedTrace n).point j'.castSucc h1 h2) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stage j'.castSucc).Carrier,
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
            ((Kh n).event j').incoming.flow.scalar s z ≤
              C * ((Kh n).event j').incoming.flow.scalar v w)

/-- `hgapJF` 的无 J10 孪生（R-C11-16 D-3 / D-4 第三步；合同 Prop，PROVISIONAL，不切换消费者）。
源 = `Ch11/P6JointFinalContractP6R8B.lean:458` 的 binder `hgapJF`（frozen txt 逐字一致，gen.py A2/A6）。
与原合同逐字只差一行：删去结论 ∃ 元组第 16 个 ∧ 分量
`(∀ n, Q n < R n)`（J10，源 :545）。J9 的 `Q` 保留为存在量
（cap-age / EventSlabsDerivative 等合取仍用）。参数 = 原定理上下文里的自由变量。 -/
def hgapJF_noJ10_P6JK
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ) (Ctime : ℝ≥0)
    (T₀ Qt : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
        ∀ z : ((Kh k).stageAt v).Carrier,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
              ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k))
                  ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (L k / Real.sqrt (R k)) →
          4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
          (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
      Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
      (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
        (σ k : ℝ) < (Kh k).horizon) →
      (∀ k : ℕ, (k : ℝ) + 1 < R k) →
    ∃ (Ctime₀ : ℝ≥0) (phi : ℝ → ℝ) (Q T₀ : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
    GeometricCutoffRecord (K n).toHistory i (p n))
      (a₀ : ℕ → ℝ),
      Nonempty (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) ∧
      (Perelman.AdmissiblePinchingFunction phi) ∧
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
    -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
    (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
      (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
    ((recordsK n i hi).static b).neck.scale) ∧
      (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
      (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
    ((K n).toHistory.event i).incoming.flow
    (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        Perelman.PhiAlmostNonnegative
          (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) ∧
      (∀ n, (K n).EventSlabsDerivative Ctime₀ (Q n) (Fin.last (K n).eventCount)) ∧
      (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
          Ctime₀ (Q n) (K n).horizon) ∧
      (∀ n, T₀ n ≤ (aSeed n : ℝ)) ∧
      (∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier),
    HEq (y n) yG' →
    ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
    (hl : i.succ ≤ Fin.last (K n).eventCount)
    (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
    (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
    (x : standardCapWindow (p n).modelRadius),
    A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
      ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
      (σ n : ℝ) - (K n).time i.succ ≤
        (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹)) ∧
      (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (D / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
    ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
      ((Kh n).activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
      (Kh n).isParabolicallyRmControlledBall v
        (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
        (ϱ / Real.sqrt (R n)) →
      ENNReal.ofReal (κd * ϱ ^ 3) ≤
        Geometry.Collapse.ballVolume
          (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) ∧
      (∃ aP : ℝ, 0 < aP ∧ ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
    ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
    ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) ∧
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
          ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) ∧
      (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
        (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
        (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
    (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
    (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
          ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
      ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
        (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
    (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
    (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
    (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
      ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
          ENNReal.ofReal ρU) →
    (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
      ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
            ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
          ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
      ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
      (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / Real.sqrt (R n))) ∧
      (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∀ᶠ n in atTop,
    ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
    v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
    ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (Dw / Real.sqrt (R n)),
    ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
      (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
        hjσ x₁),
    ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
      (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
        (Fin.last (Kh n).eventCount)).Carrier),
      riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
          ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
      riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
          (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
            (R n)) →
      R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
          (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            w)),
      ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
        → τ ≤ v →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))

/-- `hgapJF8` 的无 J10 孪生（R-C11-16 D-3 / D-4 第三步；合同 Prop，PROVISIONAL，不切换消费者）。
源 = `Ch11/P6RerunJointFinal8P6R8B.lean:471` 的 binder `hgapJF8`（frozen txt 逐字一致，gen.py A2/A6）。
与原合同逐字只差一行：删去结论 ∃ 元组第 16 个 ∧ 分量
`(∀ n, Q n < R n)`（J10，源 :558）。J9 的 `Q` 保留为存在量
（cap-age / EventSlabsDerivative 等合取仍用）。参数 = 原定理上下文里的自由变量。 -/
def hgapJF8_noJ10_P6JK
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (η₁ C1₁ C2₁ : ℝ) (Ctime₁ : ℝ≥0)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) (T₀ Qt : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
      ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
        (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
        (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
          ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
      let c : ℕ → ℝ := fun k => r k ^ 2
      let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
      let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
      let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
      let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
      let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
        (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
        (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
        (∀ᶠ k in atTop,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) →
        (∀ k : ℕ, (k : ℝ) + 1 < R k) →
      ∃ (Ctime₀ : ℝ≥0) (phi : ℝ → ℝ) (Q T₀ : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
        (a₀ : ℕ → ℝ),
        Nonempty (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) ∧
        (Perelman.AdmissiblePinchingFunction phi) ∧
        (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
        (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale) ∧
        (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
          Perelman.PhiAlmostNonnegative
            (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow
            (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) ∧
        (∀ n, (K n).EventSlabsDerivative Ctime₀ (Q n) (Fin.last (K n).eventCount)) ∧
        (∀ n (hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
          (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
            Ctime₀ (Q n) (K n).horizon) ∧
        (∀ n, T₀ n ≤ (aSeed n : ℝ)) ∧
        (∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier),
      HEq (y n) yG' →
      ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ Fin.last (K n).eventCount)
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        (σ n : ℝ) - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹)) ∧
        (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) ∧
        (∃ aP : ℝ, 0 < aP ∧ ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
      ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) ∧
        (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) ∧
        (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
          (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
          (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
            ENNReal.ofReal ((A + 3) * 1)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
      (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal ((A + 3) * 1)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
        (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) ∧
        (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
      v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
        (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
          (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
              (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              w)),
        ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
          → τ ≤ v →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
