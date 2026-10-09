import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceGuardedFinalCoreP6HK

/-!
# HFIN G1：F4 / F5 的 final 条件形孪生（GAP e，后缀 `_HF`）

`P6SliceGuardedFinalCoreP6HK` 两个定理逐字（生成器断言替换），改动只有：
* 删 `hfin : ∀ n, time last < horizon`；
* `G : ∀ n, time last < horizon → IncomingSlab …`，`hG` / `hpinchF` / `hderF` 改 `∀ n h, …`；
* `hUVCF` 形陈述（final slab 内部的 `v`）在 `v` 前加 `∀ hfn : time last < horizon`；
* F4 final 支（`activeStage v = last`）内由 `ht1 : time last < v`、`ht2 : v < horizon` 取 `hfn`。
末事件时刻 = horizon（退化末 slab）时 final 数据前提全部空真。PROVED，无 binder。
生成器 `build-logs/scratch/HFIN/gen/g1.py`（源 sha256
    `b16754758fe5daadfdcdb7ce3ea725bf50aea4cdd381081d450b5bdbec3c9d4c`）。
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

/-- **F4 核心 final 条件形孪生（`_HF`，PROVED）**：`hsliceR_lateHI_core_final_localG_P6HK` 逐字，`hfin` 删去，
`G` / `hG` / `hpinchF` / `hderF` 改条件形（`time last < horizon →`）；final 支内由 `ht1 ht2` 局部取 `hfL`。 -/
theorem ObservedHistory.hsliceR_lateHI_core_final_localG_HF
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl)
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
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n h, Perelman.PhiAlmostNonnegative (G n h).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime (Q n) (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
      n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad Bw : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
        (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
              hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvs))
              ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
          x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K n).toHistory.stage
          j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((K n).toHistory.event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((K n).toHistory.event j').incoming.flow v' x ξ| ≤
                Cgrad * ((K n).toHistory.event j').incoming.flow.scalar v' x *
                  Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((K n).toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ))
                    ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).toHistory.time j'.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j'.succ →
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((K n).toHistory.event j').incoming.flow.scalar s x)
                (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).toHistory.eventCount) (first : Fin ((K n).toHistory.eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ),
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2)) →
      (∀ᶠ n in l,
      ∀ (hfn : (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
      (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
        v < (K n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).eventCount))
        (h2 : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).eventCount)).Carrier),
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n hfn).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            Cg * R n < (G n hfn).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n hfn).flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - Bw / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n hfn).flow v' x ξ| ≤
                Cgrad * (G n hfn).flow.scalar v' x *
                  Real.sqrt ((G n hfn).flow.scalar v' x) *
                  Real.sqrt (((G n hfn).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - Bw / (G n hfn).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            (v - τ) * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - Bw / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => (G n hfn).flow.scalar s x) (Iic v') v'| ≤
              Ctime * (G n hfn).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - Bw / (G n hfn).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2)) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
            ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w →
              ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage
                  v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w)
                ∧
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage ((K n).toHistory.activeStage
              v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨Cbirth, hCbirth, hP⟩ :=
    RetainedCoreHistory.slice_dichotomy_late_Cg_window_local_bothG_P6HK hεle
    κ C1
    C2 hκ Ctime Cgrad Cg (by linarith) hphi hη₃ hLc
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Bw, Rmin, ζmin, δ₀, m₀, hΛ, -, hζ, hδ₀, hmain, hmainF⟩ :=
    hP A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, Bw, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hUl hUFl => ?_⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRn1 hnat
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ₀ := h0.eventually (ge_mem_nhds hδ₀)
  have hacc' : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζmin :=
    (h0.eventually (ge_mem_nhds hζ)).mono fun n hn => (hacc n).trans hn
  have hrad' : ∀ᶠ n in atTop, Rmin ≤ (p n).modelRadius :=
    (hnat.eventually_ge_atTop Rmin).mono fun n hn => hn.trans (hrad n)
  have hord' : ∀ᶠ n in atTop, m₀ ≤ (p n).modelOrder :=
    (eventually_ge_atTop m₀).mono fun n hn => le_trans (by omega) (hord n)
  have hbirth : ∀ᶠ n : ℕ in atTop, ∀ i hi b,
      max ((n : ℝ) + 1) (Q n) ≤ Cbirth * ((recordsK n i hi).static b).neck.scale ∧
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale := by
    filter_upwards [hnat.eventually_ge_atTop (1 / Cbirth), hbirthA] with n hn1 hbA i hi b
    have hs := hscaleK n i hi b
    have hC1 : 1 ≤ ((n : ℝ) + 1) * Cbirth := (div_le_iff₀ hCbirth).1 hn1
    have hq : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    refine ⟨?_, hbA i hi b⟩
    calc max ((n : ℝ) + 1) (Q n) = max ((n : ℝ) + 1) (Q n) * 1 := by ring
      _ ≤ max ((n : ℝ) + 1) (Q n) * (((n : ℝ) + 1) * Cbirth) :=
        mul_le_mul_of_nonneg_left hC1 (by linarith)
      _ = ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) * Cbirth := by ring
      _ ≤ ((recordsK n i hi).static b).neck.scale * Cbirth :=
        mul_le_mul_of_nonneg_right hs hCbirth.le
      _ = Cbirth * ((recordsK n i hi).static b).neck.scale := by ring
  have hT1 : 0 < -σ₁ := by linarith
  have hRσ : ∀ᶠ n in atTop, Λ - σ₁ ≤ R n * σ n := by
    filter_upwards [hwin (max (Λ - σ₁) 1) (lt_max_of_lt_right one_pos)] with n hn
    have ha0 : (0 : ℝ) ≤ aSeed n := (aSeed n).2.1
    have hRn := hRpos n
    have h1 : max (Λ - σ₁) 1 / R n ≤ σ n := by linarith
    rw [div_le_iff₀ hRn] at h1
    nlinarith [le_max_left (Λ - σ₁) 1]
  filter_upwards [Filter.Eventually.filter_mono hl hδ, Filter.Eventually.filter_mono hl hrad',
    Filter.Eventually.filter_mono hl hord', Filter.Eventually.filter_mono hl hacc',
    Filter.Eventually.filter_mono hl hbirth,
    Filter.Eventually.filter_mono hl (hR.eventually_ge_atTop Λ),
    Filter.Eventually.filter_mono hl hRσ,
    Filter.Eventually.filter_mono hl (hρV.eventually_ge_atTop Λ),
    Filter.Eventually.filter_mono hl (hL.eventually_ge_atTop (4 * Dd)),
    Filter.Eventually.filter_mono hl (hwin (-σ₁) hT1),
    Filter.Eventually.filter_mono hl (hT₀ (Bw - σ₁)), hdl, hUl,
    hUFl]
    with n e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  intro x₁ hx₁ v hvt hv1 hv2 hage tr₁ _
  have hvwin : (σ n : ℝ) - -σ₁ / R n ≤ v := by
    rw [neg_div, sub_neg_eq_add]
    exact hv1
  have hav : aSeed n ≤ v := show (aSeed n : ℝ) ≤ v from e10.trans hvwin
  have hT₀v : T₀ n ≤ v - Bw / R n := by
    have : (Bw - σ₁) / R n = Bw / R n - σ₁ / R n := sub_div _ _ _
    rw [this] at e11
    linarith
  by_cases hlastF : (K n).toHistory.activeStage v = Fin.last (K n).eventCount
  · -- final slab 内部切片：final 单切片二分
    have ht1 : (K n).time (Fin.last (K n).eventCount) < v := by
      have h := hage
      rw [hlastF] at h
      exact h
    have ht2 : (v : ℝ) < (K n).horizon := by
      have h1 : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ (hRpos n)
      have h2 : (σ n : ℝ) ≤ (K n).horizon := (σ n).2.2
      linarith
    have hfL : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := ht1.trans ht2
    have h1 : (K n).toHistory.activeStage (aSeed n) ≤ Fin.last (K n).eventCount := Fin.le_last _
    have h2 : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (Tn n) :=
      hlastF.symm.le.trans ((K n).toHistory.activeStage_mono (hvt.trans (hsT n)))
    have hs := point_heq_of_eq_P6M2 (seedTrace n) hlastF ((K n).toHistory.activeStage_mono hav)
      ((K n).toHistory.activeStage_mono (hvt.trans (hsT n))) h1 h2
    have hfn : (K n).toHistory.activeStage v ≤ Fin.last (K n).eventCount := le_of_eq hlastF
    have hjσ : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (σ n) :=
      hlastF.symm.le.trans ((K n).toHistory.activeStage_mono hvt)
    have hzj := point_heq_of_eq_P6M2 tr₁ hlastF le_rfl ((K n).toHistory.activeStage_mono hvt)
      (hfn.trans le_rfl) hjσ
    have hΛv : Λ ≤ R n * v := by
      have hRv : R n * ((σ n : ℝ) + σ₁ / R n) ≤ R n * v :=
        mul_le_mul_of_nonneg_left hv1 (hRpos n).le
      have hRne := (hRpos n).ne'
      have heq : R n * ((σ n : ℝ) + σ₁ / R n) = R n * σ n + σ₁ := by
        field_simp
      linarith
    have hL0 : 0 ≤ L n / 4 / Real.sqrt (R n) := by
      have : 0 < Dd := hDd
      have : 0 ≤ L n := by linarith
      positivity
    refine hmainF (K n) (T₀ n) (recordsK n) (hcanK n) e2 e3 e4 (hpinchK0 n) (recordsF n)
      (1 / ((n : ℝ) + 1)) (hδF n) e1 (max ((n : ℝ) + 1) (Q n)) (a₀ n)
      (lt_of_lt_of_le (by positivity) (le_max_left _ _)) (fun x => (hHI n x).1)
      (fun x => (hHI n x).2) e5 hfL (G n hfL) (hG n hfL) (hpinchF n hfL)
      (fun i _ y' t' ht hR' => hslabK n i (Fin.castSucc_lt_last i) y' t' ht
        ((le_max_right _ _).trans_lt hR')) v ht1 ht2
      (fun y' t' ht hR' => hderF n hfL y' t' ⟨ht.1, ht.2.trans ht2⟩ ((le_max_right _ _).trans_lt
          hR'))
      (R n) (ρV n) (hRpos n) e6 hΛv e8
      hT₀v _ hlastF
      (tr₁.point _ le_rfl _) _ _ hs _ (e12 x₁ hx₁ v hav hvt hv1 tr₁)
      ((tr₁.restrictFirst hfn hjσ).point (Fin.last (K n).eventCount) le_rfl hjσ) hzj ?_
    intro w hw hzw hRw
    refine (fun H => ?hU) (e14 hfL v ht1 ht2 hv1 hv2 x₁ hx₁ hjσ (tr₁.restrictFirst hfn hjσ) h1 h2 w
      (hw.trans ?hd) hzw hRw)
    case hU =>
      obtain ⟨u1, u2, u3, u4, u5⟩ := H
      exact ⟨u1, u2, u3, u4, fun i first hf z hz Btr v' hv' hBv' hg hR =>
        u5 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i)
          (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt))
            first)
          (Fin.le_def.mpr (Fin.le_def.mp hf)) z hz
          ((K n).backwardPointTraceOfPrefix (Fin.last (K n).eventCount) Btr) v' hv' hBv' hg hR⟩
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    rw [← ENNReal.ofReal_add hL0 (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 (hRpos n)
    rw [← add_div]
  have hlast : (K n).toHistory.activeStage v ≠ Fin.last (K n).eventCount := hlastF
  obtain ⟨j', hj'⟩ := Fin.exists_castSucc_eq.mpr hlast
  have ht1 : (K n).time j'.castSucc < v := by
    change (K n).toHistory.time j'.castSucc < v
    rw [hj']
    exact hage
  have ht2 : (v : ℝ) < (K n).time j'.succ := by
    have hlt : ((K n).toHistory.activeStage v : ℕ) < (K n).toHistory.eventCount := by
      rw [← hj']
      exact j'.isLt
    have h := (K n).toHistory.activeStage_before_next v hlt
    have heq : (⟨((K n).toHistory.activeStage v : ℕ) + 1, by omega⟩ :
        Fin ((K n).toHistory.eventCount + 1)) = j'.succ := by
      apply Fin.ext
      simp only [← hj', Fin.val_castSucc, Fin.val_succ]
    rwa [heq] at h
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc := by
    rw [hj']
    exact (K n).toHistory.activeStage_mono hav
  have h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) := by
    rw [hj']
    exact (K n).toHistory.activeStage_mono (hvt.trans (hsT n))
  have hs := point_heq_of_eq_P6M2 (seedTrace n) hj'.symm ((K n).toHistory.activeStage_mono hav)
    ((K n).toHistory.activeStage_mono (hvt.trans (hsT n))) h1 h2
  have hfn : (K n).toHistory.activeStage v ≤ j'.castSucc := le_of_eq hj'.symm
  have hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n) :=
    (le_of_eq hj').trans ((K n).toHistory.activeStage_mono hvt)
  have hzj := point_heq_of_eq_P6M2 tr₁ hj'.symm le_rfl ((K n).toHistory.activeStage_mono hvt)
    (hfn.trans le_rfl) hjσ
  have hΛv : Λ ≤ R n * v := by
    have hRv : R n * ((σ n : ℝ) + σ₁ / R n) ≤ R n * v :=
      mul_le_mul_of_nonneg_left hv1 (hRpos n).le
    have hRne := (hRpos n).ne'
    have heq : R n * ((σ n : ℝ) + σ₁ / R n) = R n * σ n + σ₁ := by
      field_simp
    linarith
  have hL0 : 0 ≤ L n / 4 / Real.sqrt (R n) := by
    have : 0 < Dd := hDd
    have : 0 ≤ L n := by linarith
    positivity
  refine hmain (K n) (T₀ n) (recordsK n) (hcanK n) e2 e3 e4 (hpinchK0 n) (recordsF n)
    (1 / ((n : ℝ) + 1)) (hδF n) e1 (max ((n : ℝ) + 1) (Q n)) (a₀ n)
    (lt_of_lt_of_le (by positivity) (le_max_left _ _)) (fun x => (hHI n x).1)
    (fun x => (hHI n x).2) e5 j'
    (fun i _ y' t' ht hR' => hslabK n i (Fin.castSucc_lt_last i) y' t' ht
      ((le_max_right _ _).trans_lt hR')) v ht1 ht2
    (fun y' t' ht hR' => hslabK n j' (Fin.castSucc_lt_last j') y' t' ⟨ht.1, ht.2.trans ht2⟩
      ((le_max_right _ _).trans_lt hR'))
    (R n) (ρV n) (hRpos n) e6 hΛv e8
    hT₀v _ hj'.symm
    (tr₁.point _ le_rfl _) _ _ hs _ (e12 x₁ hx₁ v hav hvt hv1 tr₁)
    ((tr₁.restrictFirst hfn hjσ).point j'.castSucc le_rfl hjσ) hzj ?_
  intro w hw hzw hRw
  refine (fun H => ?hUe) (e13 j' v ht1 ht2 hv1 hv2 x₁ hx₁ hjσ (tr₁.restrictFirst hfn hjσ) h1 h2 w
    (hw.trans ?hde) hzw hRw)
  case hUe =>
    obtain ⟨u1, u2, u3, u4, u5⟩ := H
    exact ⟨u1, u2, u3, u4, fun i first hf z hz Btr v' hv' hBv' hg hR =>
      u5 (Fin.castLE (Nat.le_of_lt_succ j'.castSucc.isLt) i)
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j'.castSucc.isLt)) first)
        (Fin.le_def.mpr (Fin.le_def.mp hf)) (Fin.lt_def.mpr i.isLt) z hz
        ((K n).backwardPointTraceOfPrefix j'.castSucc Btr) v' hv' hBv' hg hR⟩
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add hL0 (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 (hRpos n)
  rw [← add_div]

/-- **F5 final 条件形孪生（`_HF`，PROVED）**：`hbcadC_lateHI_of_slice_data_final_cond_localG_P6HK` 逐字，
`hfin` 删去，final 数据条件形，`hUVCF` 槽在 `v` 前加 `∀ hfn`。 -/
theorem ObservedHistory.hbcadC_lateHI_of_slice_data_final_cond_localG_HF
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl)
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
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n h, Perelman.PhiAlmostNonnegative (G n h).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime (Q n) (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
      n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
        (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
              hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvs))
              ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hUVC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
          x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K n).toHistory.stage
          j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((K n).toHistory.event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((K n).toHistory.event j').incoming.flow v' x ξ| ≤
                Cgrad * ((K n).toHistory.event j').incoming.flow.scalar v' x *
                  Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((K n).toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ))
                    ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).toHistory.time j'.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j'.succ →
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((K n).toHistory.event j').incoming.flow.scalar s x)
                (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).toHistory.eventCount) (first : Fin ((K n).toHistory.eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ),
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2))
    (hUVCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (hfn : (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
      (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
        v < (K n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).eventCount))
        (h2 : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).eventCount)).Carrier),
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n hfn).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            Cg * R n < (G n hfn).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n hfn).flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n hfn).flow v' x ξ| ≤
                Cgrad * (G n hfn).flow.scalar v' x *
                  Real.sqrt ((G n hfn).flow.scalar v' x) *
                  Real.sqrt (((G n hfn).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n hfn).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            (v - τ) * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => (G n hfn).flow.scalar s x) (Iic v') v'| ≤
              Ctime * (G n hfn).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2)) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₂),
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤ A * R n →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt))
            (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hB⟩ :=
    ObservedHistory.hbcadC_of_slice_dichotomy_open_final_P6FC.{u}
  have hR1 : ∀ᶠ n in atTop, 1 ≤ R n := Eventually.of_forall fun n => by
    have h1 := hRn1 n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  refine hB K σ y R hRpos hR1 ?_
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, Bw, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_final_localG_HF hεle hκ hphi hCg hη₃ hLc hG recordsF
      hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos hRn1
      hT₀
      Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun φ hφ σ₁ σ₂ h12 hσ₂ Dw hDw T Kc hT hKc htr => ?_⟩
  refine hcore (map φ atTop) hφ.tendsto_atTop σ₁ σ₂ h12 hσ₂ Dw hDw ?_
    (hUVC Rad Bw σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
    (hUVCF Rad Bw σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  filter_upwards [hdistQC φ hφ Dw T Kc hDw (by linarith) hKc htr] with n hn
  intro x hx v hav hvs hv tr
  refine hn x hx v hav hvs ?_ tr
  have h1 : -T / R n ≤ σ₁ / R n := div_le_div_of_nonneg_right (by linarith) (hRpos n).le
  rw [sub_eq_add_neg, ← neg_div]
  linarith
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
