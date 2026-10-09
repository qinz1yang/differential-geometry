import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bSwitchCoarseP6HPB3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DbbMinRescaleP6KT

/-!
# kernel body 截断形孪生（O-CH11-KTRUNC1 G1，`_P6KT`）

lead 10-08 裁定：kernel body 的 `hslabK`（NotKBody，HPB3:70）与 final (D1)(D2)（FinalBody，HPB3:263–264）改为
**截断形**——终点 `time j.succ` / `horizon` 换成 `min (time j.succ) (tK n)` / `min horizon (tK n)`，
`tK` 与 `Q T₀` 同层隐式引入，并在 `has` 后加连接行 `hTnK : ∀ n, (Tn n : ℝ) ≤ tK n`（下游取 `tK := Tn`）。
无新 Prop / 新具名合同：截断形 = 既有 `DerivativeBoundBefore` 的终点参数化。冻结件（HPB3 Body / Exp）不动。
* `NotKBodyT_P6KT` / `FinalBodyT_P6KT`：HPB3 Body 逐字 + 上述 3（final 4）处编辑（生成器断言计数）；
* `NotKKernelExpT_P6KT` / `FinalKernelExpT_P6KT`：exp 形（`C = p6CoarseC ε`），同 HPB3 Exp 逐字换 Body；
* 桥（PROVED）：T ⇒ 原（取 `tK := Tn`，`min_le_left` 单调，`hTnK := le_rfl`）；反向不成立（T 更强：前提更弱）。
kernel 证明里 `hslabK` / (D1)(D2) 的使用点全部在 `≤ t n = σ n ≤ Tn n` 的 slab 上（G0 核查，见
`state-O-CH11-KTRUNC1.md`），故 T 形由 G2（`P6KernelTrunc*P6KT`）以与 JK2 相同的槽付出。
生成：`build-logs/scratch/O-CH11-KTRUNC1/gen/gen_g1.py`。
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


namespace ObservedHistory

open GC.LongTime.Ch11 (epsW_CXOU2 epsW_CXOU2_pos p6CoarseC_C11GT6)

/-- **event notK kernel Body 的截断形（`_P6KT`）**：`NotKBodyNoJ10_P6HPB3` 逐字，`hslabK` 换截断形
（终点 `min ((K n).time j.succ) (tK n)`）、`{Q T₀ tK}`、`has` 后加 `hTnK`。 -/
def NotKBodyT_P6KT (ε C : ℝ) : Prop :=
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} →
      {Q T₀ tK : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (hslabK : ∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (hpos : ∀ n, ∃ j : Fin (Kh n).eventCount, (Kh n).time j.castSucc < (σ n : ℝ) ∧
        (σ n : ℝ) < (Kh n).time j.succ) →
      (R : ℕ → ℝ) →
      (hRdef : ∀ n, R n =
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) →
      (hnotKs : ∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' → (K n).time j'.castSucc < (σ n : ℝ) → (σ n : ℝ) < (K n).time j'.succ →
        ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ j'.castSucc hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      {κd : ℝ} → (hκd : 0 < κd) →
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
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) →
      {aP : ℝ} → (haP : 0 < aP) →
      (hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (hdistσ : ∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
      (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
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
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False

/-- **final kernel Body 的截断形（`_P6KT`）**：`FinalBodyNoJ10_P6HPB3` 逐字，(D1) 换截断形
（终点 `min ((K n).time j.succ) (tK n)`）、(D2) 终点换 `min (K n).horizon (tK n)`、`{Q T₀ tK}`、
`has` 后加 `hTnK`。 -/
def FinalBodyT_P6KT (ε C : ℝ) : Prop :=
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (_ : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (_ : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {Q T₀ tK : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (_ : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (_ : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (_ : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (_ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (_ : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (_ : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (_ : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (_ : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (_ : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (_ : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (_ : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (_ : ∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time j.succ) (tK n))) →
      (_ : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (min (K n).horizon (tK n))) →
      (_ : ∀ n : ℕ, (n : ℝ) + 1 <
        (G n).flow.scalar (t n) (yG n)) →
      (_ : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl
          (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      (Kh : ℕ → ObservedHistory.{u}) → (_ : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (_ : ∀ n, (σ n : ℝ) = t n) → (_ : ∀ n, HEq (y n) (yG n)) →
      (_ : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      (hRpos : ∀ n, 0 < R n) →
      {κd : ℝ} → (hκd : 0 < κd) →
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
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) →
      {aP : ℝ} → (haP : 0 < aP) →
      (hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) →
      (_ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (_ : Tendsto L atTop atTop) →
      (Cg : ℝ) → (_ : 2 ≤ Cg) →
      (_ : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (_ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (_ : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      {κ Aκ : ℝ} → (_ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (_ : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (_ : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (_ : ∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
      (_ : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
      (_ : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
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
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hκRF : ∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
        (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ENNReal.ofReal (Aκ * r n)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
      (hclosGF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
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
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (_ : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False

/-- **exp 形截断 event kernel（`_P6KT`）**：`NotKKernelExpNoJ10_P6HPB3` 逐字，Body 换 `NotKBodyT_P6KT`。 -/
def NotKKernelExpT_P6KT : Prop :=
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW_CXOU2.{u} →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    NotKBodyT_P6KT.{u} ε (p6CoarseC_C11GT6.{u} ε)

/-- **exp 形截断 final kernel（`_P6KT`）**：`FinalKernelExpNoJ10_P6HPB3` 逐字，Body 换 `FinalBodyT_P6KT`。 -/
def FinalKernelExpT_P6KT : Prop :=
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW_CXOU2.{u} →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    FinalBodyT_P6KT.{u} ε (p6CoarseC_C11GT6.{u} ε)

/-- **桥 T ⇒ 原（PROVED，`_P6KT`）**：截断形 Body 推出 HPB3 原 Body（`tK := Tn`；全形 `hslabK` 经
`eventSlabsDerivT_of_full_P6KT` 截断；`hTnK := le_rfl`）。 -/
theorem notKBodyNoJ10_of_T_P6KT {ε C : ℝ} (h : NotKBodyT_P6KT.{u} ε C) :
    NotKBodyNoJ10_P6HPB3.{u} ε C := by
  unfold NotKBodyT_P6KT at h
  unfold NotKBodyNoJ10_P6HPB3
  intro C1' C2' Ctime' h1 h2 h3 Ctime phi hphi K Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc
    hrad hord hscaleK hbirthA hpinchK0 hslabK Kh hKh σ y hpos R hRdef hRpos hRlt hnotKs κd hκd hvolK
    aP haP hpinL Tn aSeed haT hsT has
  exact h h1 h2 h3 hphi (tK := fun n => (Tn n : ℝ)) recordsF hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 (fun n => (K n).eventSlabsDerivT_of_full_P6KT (hslabK n) (Tn n)) Kh hKh σ y
    hpos R hRdef hRpos hRlt hnotKs hκd hvolK haP hpinL Tn aSeed haT hsT has (fun _ => le_rfl)

/-- **桥 T ⇒ 原（PROVED，`_P6KT`）**：截断形 final Body 推出 HPB3 原 final Body（`tK := Tn`）。 -/
theorem finalBodyNoJ10_of_T_P6KT {ε C : ℝ} (h : FinalBodyT_P6KT.{u} ε C) :
    FinalBodyNoJ10_P6HPB3.{u} ε C := by
  unfold FinalBodyT_P6KT at h
  unfold FinalBodyNoJ10_P6HPB3
  intro C1' C2' Ctime' h1 h2 h3 Ctime phi hphi K t htl htK G hG Q T₀ p pF recordsK recordsF yG a₀
    hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hpinchF hD1 hD2 hqR hnotK Kh hKh σ y R
    hσ hyG hRn hRpos κd hκd hvolK aP haP hpinL hT₀ Tn aSeed haT hsT has
  exact h h1 h2 h3 hphi htl htK hG (tK := fun n => (Tn n : ℝ)) recordsF hHI hcanK hδF hacc hrad
    hord hscaleK hbirthA hpinchK0 hpinchF
    (fun n => (K n).eventSlabsDerivT_of_full_P6KT (hD1 n) (Tn n))
    (fun n => (G n).derivativeBoundBefore_mono (min_le_left _ _) (hD2 n)) hqR hnotK Kh hKh σ y R
    hσ hyG hRn hRpos hκd hvolK haP hpinL hT₀ Tn aSeed haT hsT has (fun _ => le_rfl)

/-- **桥 T ⇒ 原（exp 形，PROVED，`_P6KT`）**。 -/
theorem notKKernelExp_of_T_P6KT (h : NotKKernelExpT_P6KT.{u}) : NotKKernelExpNoJ10_P6HPB3.{u} :=
  fun ε hε h11 hW hX hN hc => notKBodyNoJ10_of_T_P6KT (h ε hε h11 hW hX hN hc)

/-- **桥 T ⇒ 原（exp 形，PROVED，`_P6KT`）**。 -/
theorem finalKernelExp_of_T_P6KT (h : FinalKernelExpT_P6KT.{u}) : FinalKernelExpNoJ10_P6HPB3.{u} :=
  fun ε hε h11 hW hX hN hc => finalBodyNoJ10_of_T_P6KT (h ε hε h11 hW hX hN hc)

/-- **桥 T-exp ⇒ J10GEN2B ∃ 形（PROVED，`_P6KT`）**：经 HPB3 `notKKernelNoJ10_of_exp_P6HPB3`。 -/
theorem notKKernelNoJ10_of_T_P6KT (h : NotKKernelExpT_P6KT.{u}) : NotKKernelNoJ10_P6JB.{u} :=
  notKKernelNoJ10_of_exp_P6HPB3 (notKKernelExp_of_T_P6KT h)

/-- **桥 T-exp ⇒ J10GEN2B ∃ 形（PROVED，`_P6KT`）**：经 HPB3 `finalKernelNoJ10_of_exp_P6HPB3`。 -/
theorem finalKernelNoJ10_of_T_P6KT (h : FinalKernelExpT_P6KT.{u}) : FinalKernelNoJ10_P6JB.{u} :=
  finalKernelNoJ10_of_exp_P6HPB3 (finalKernelExp_of_T_P6KT h)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
