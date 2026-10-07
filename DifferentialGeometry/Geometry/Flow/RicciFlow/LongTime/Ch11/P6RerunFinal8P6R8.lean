import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RerunPrefixDecP6R8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestFinalPlusP6HF

/-!
# `hrerunF8`：final 支阈值 8 重跑收口 + 精度解耦（O-CH11-RERUN8 G2，后缀 `_P6R8`）

HREST2 `hbd_P6HB` 的 binder **`hrerunF8`**（冻结合同 = `P6HbdLateP6HB` 的槽文本，逐字）的证明：
坏点 `¬Good η₁ C1₁ C2₁ Ctime₁`、Good 区 `(ε, C1, C2, Ctime)`、阈值 `8 * R k`、final 内部类 ⇒ `False`。
在 G1a 的解耦 final prefix 上重放 HCLOSEF 两层（陈述由 build-logs/scratch/O-CH11-RERUN8/gen3.py 生成）：
* `hcloseF_plus_dec_P6R8` = HCLOSEF `hcloseF_plus_P6HF` 解耦：`hsel` 在坏点常数，`hgood` / `hwit` / `hbcad`
  在 Good 区 `(ε, C1', C2', Ctime')`；`0 ≤ C2'` 改为显式前提 `hC2'`。
* **`hrerunF8_P6R8`**：结论 = `hrerunF8` 槽逐字；证明 = HCLOSEF `finalBranch_lateHI_plus_P6HF` 逐字，`Cg := 8`；
  槽里的种子小曲率前提 `hasSmallParabolicCurvature` 不用（同 HREST `finalBranch_lateHI_P6HR`）。数据 binder
  **`hgapF8`** = `hgapF⁺` 的孪生（阈值 `8 * R k`、`hsel` 与 `hcwpLF` 在坏点常数、`hgood` 在 `(ε, C1, C2, Ctime)`）。
常数同 G1（`p6CoarseC_C11GT6 η₁` 下界、`Classical.choose ancientWitness_decoupled_P6P` 精度上限）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6)

namespace ObservedHistory

/-- **`hcloseF⁺` 精度解耦（`_P6R8`）**：见文件头。 -/
theorem hcloseF_plus_dec_P6R8 {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεcone : ε ≤ coneAccuracy)
    {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hC1 : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (hC2 : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁) (hCt : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁)
    {C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2' : 0 ≤ C2') :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (_ : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (_ : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
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
      (_ : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (_ : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon) →
      (_ : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
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
      (_ : GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) →
      (_ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
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
      (_ : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) →
      False := by
  intro Ctime phi hphi K t htl htK G hG Q T₀ p pF recordsK recordsF yG a₀ hHI hcanK hδF hacc hrad
    hord hscaleK hbirthA hpinchK0 hpinchF hslabK hderF hqR hnotK Kh hKh σ y R hσ hyG hRn hRpos d hT₀
    Tn aSeed haT hsT has pT seedTrace L hL Cg hCg hgood hwin hdistQ κ Aκ hκ r ρV hρV hroom hdistσ
    hκR hclosG hκRF hclosGF hsel
  subst hKh
  have hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon :=
    fun n => (htl n).trans (htK n)
  have hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro D T hD hT
    filter_upwards [hdistQ D T hD hT, hL.eventually_ge_atTop 0] with n hn hL0
    intro x hx v hav hvs hvT tr
    refine (hn x hx v hav hvs hvT tr).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hqRR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n :=
    fun n => (hqR n).le.trans_eq (hRn n).symm
  -- U 侧：event 块（逐字 P6CG）+ final slab 块（G3a，`hκRF` / `hclosGF`）
  have hUVG := ObservedHistory.hUVG_of_selection_Cg_P6S3 (Ctime' := Ctime') (Cg := Cg) hC2'
    (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin
    hroom hdistσ hκR hclosG
  have hUVGF := ObservedHistory.hUVGF_of_selection_Cg_P6HF (Ctime' := Ctime') (Cg := Cg) hC2' hfin
    hG Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκRF hclosGF
  have hbcad := ObservedHistory.hbcad_lateHI_of_slice_data_final_P6HF hεcone hκ hphi (by linarith)
    hfin hG recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y
      R
    hRpos hqRR hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQ hUVG hUVGF
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨qcan, θcap, D, hqc, hθ, hD, hqcan, hQq, hθcap, hDn⟩ := exists_params_P6D Q
  -- K 层 → prefix 形（prefix 取 `Fin.last`）
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hscale : ∀ (n : ℕ) (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hi b,
      ((n : ℝ) + 1) * qcan n ≤
        (((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static b
          ).neck.scale :=
    fun n i hi b => by
      rw [hqc n]
      exact hscaleK n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i) hi b
  have hslab' : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount) :=
    fun n => RetainedCoreHistory.eventSlabsDerivative_mono_P6D (hslabK n) (hQq n)
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  have hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n) :=
    fun n x v hv hR => by
      have hlt : qcan n < (G n).flow.scalar v x := by
        have := hq0 n
        linarith
      have h := hderF n x v ⟨hv.1, hv.2.trans (htK n)⟩ ((hQq n).trans_lt hlt)
      rw [hctime]
      have h0 : 0 ≤ (Ctime : ℝ) * (G n).flow.scalar v x ^ 2 :=
        mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
      linarith
  have hqR' : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n) := fun n => by
    rw [hqc n]
    exact hqR n
  have hnot := fun n => (K n).not_capWindowPoint_prefix_of_late_P6N (Fin.last (K n).eventCount)
    (recordsK n) (yG n) (hnotK n)
  have hnot' : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static b
            ).window x ∧
        ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤ θcap n *
          ((((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static b
            ).neck.scale)⁻¹ :=
    fun n => by
      rw [hD n, hθ n]
      exact hnot n
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt)
      i),
      hpinchF n⟩
  have hbirthA' : ∀ᶠ n in atTop,
      ∀ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hi b,
      1 ≤ a₀ n *
        (((K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n) i hi).static b
          ).neck.scale :=
    hbirthA.mono fun n hn i hi b =>
      hn (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i) hi b
  have hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime
      (qcan n) (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) :=
    fun n => (K n).eventSlabsDerivative_prefixAt _
      (fun i _ => hslab' n i (Fin.castSucc_lt_last i))
  have hHI' := fun n => (K n).hHI_prefixAt_P6LT (Fin.last (K n).eventCount) (hHI n)
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (Fin.last (K n).eventCount) (recordsK n)
    (hcanK n)
  have hδF' : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
      T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
      (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤
        1 / ((n : ℝ) + 1) :=
    fun n i hi => hδF n (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i) hi
  -- selection / `Pre841` 侧（final slab 版）
  obtain ⟨ρnc, hradii, hkappa⟩ := exists_tracedKappa_of_kseq_P6D2 d.volume_ge
  obtain ⟨Phi, hPhi, hpinchK⟩ := exists_tracedPinching_of_pre841_P6M d
  have hC20 : 0 ≤ C2' := hC2'
  have hnc := hnc_window_final_P6M hfin hG htl σ hσ y yG hyG R hRpos hRn d.kappa_pos ρnc hkappa
  have hρ : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_final_Cg_P6HF hfin hG htl σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_final_Cg_P6HF hC20 hfin hG htl σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT
    has pT seedTrace L hL hgood hwin hdist
  have hq2 : ∀ n, 2 * qcan n ≤ Cg * R n := fun n => by
    have h1 := hqR' n
    have h2 := hqcan n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    have h4 : 2 * R n ≤ Cg * R n := mul_le_mul_of_nonneg_right hCg (hRpos n).le
    rw [hRn n] at h4 ⊢
    linarith
  have hqC : ∀ n, Cg * R n ≤ Cg * (G n).flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  have hGi : ∀ n, (G n).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
      (K n).initialMetric (Fin.last (K n).eventCount) := fun n => by
    rw [hG n]
    exact (K n).final_initial ((htl n).trans (htK n))
  have hanchor0 := RetainedCoreHistory.hanchor0_lateW_P6LT
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount)) (G := G)
    (s := fun n => (K n).horizon) (y := yG) (ρ := ρnc) hεcone d.kappa_pos hphi
    (fun n => (K n).prefixAt_time_last _) hGi hcan hqcan hpar hθcap hpinch hslab htl htK hderG hqR'
    hnot' hT₀' hRt (Cq := Cg) (fun n => Cg * R n) hq2 hqC hW hgrad hnc hρ
  obtain ⟨r₀, hr₀, hctrl⟩ := exists_hctrl_lateHI_final_P6HF
    (records := fun n => (K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n))
    hphi htl htK hG (fun n => (K n).prefixRecords (Fin.last (K n).eventCount) (recordsF n)) hHI'
    hcan hδF' hqcan hpar hscale hbirthA' hθcap hpinch hslab hderG hqR' hnot' hT₀' hRt hanchor0
    (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn
  have hctrl' := hctrl r₀ hr₀ le_rfl
  obtain ⟨hwit, hderivK⟩ := hwit_hderiv_of_selection_Cg_P6M3 (fun n => (K n).toHistory) Tn aSeed σ
    haT hsT has pT seedTrace y R L hRpos hL hgood hwin hdist
  exact false_of_selection_finalSlab_lateHI_prefix_dec_P6R8 hη hε hεW hεX hεN hC1 hC2 hCt
    hphi htl htK hG
    (records := fun n => (K n).prefixLateRecords_P6N (Fin.last (K n).eventCount) (recordsK n))
    (fun n => (K n).prefixRecords (Fin.last (K n).eventCount) (recordsF n)) hHI' hcan hδF' hqcan
    hpar hscale hbirthA' hθcap hpinch hslab hderG hqR' hnot' hT₀' hRt hanchor0
    (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hr₀ d.kappa_pos (hseed_of_pre841_P6M d hr₀
      hctrl')
    d.kappa_pos ρnc hradii hkappa hPhi hpinchK (Cs := Cg) (Cq := Cg) (qs := fun n => Cg * R n)
    (qd := fun n => Cg * R n) (fun _ => le_rfl) (fun _ => le_rfl) hwit hderivK hbcad hsel

/-- **`hrerunF8` 槽（阈值 8、坏点 `η₁`、Good 区 `ε`）**：见文件头。 -/
theorem hrerunF8_P6R8 {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{u})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεcone : ε ≤ coneAccuracy)
    {C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hC1 : p6CoarseC_C11GT6.{u} η₁ ≤ C1₁)
    (hC2 : p6CoarseC_C11GT6.{u} η₁ ≤ C2₁) (hCt : (p6CoarseC_C11GT6.{u} η₁).toNNReal ≤ Ctime₁)
    {C1 C2 : ℝ} {Ctime : ℝ≥0} (hC2' : 0 ≤ C2)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (hgapF8 : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let K : ℕ → RetainedCoreHistory.{u} := fun k =>
          (F.tower.history (ind k)).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
          (∀ n, Q n < R n) ∧
          (∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier),
        HEq (y n) yG' →
        (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        (Kh n).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ n) (y n)) ∧
          Nonempty (GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) ∧
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
          (∃ (κ Aκ : ℝ) (r ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) ∧
            (∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
            (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
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
                ENNReal.ofReal (L n / Real.sqrt (R n)))) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) → False := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 _hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood hwin hwin' hroomT hradii hfin
  have hφt : Tendsto (fun k : ℕ => k + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hlt : ∀ k : ℕ, (k : ℝ) + 1 < R (k + 1) := fun k => by
    have h := hRr (k + 1)
    push_cast at h
    linarith
  have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (k + 1) * (Tn (k + 1) : ℝ) := fun k => by
    have h := hTc (k + 1)
    push_cast at h
    linarith
  obtain ⟨Ctime₀, phi, Q, T₀, p, pF, recordsK, a₀, ⟨recordsF⟩, hphi, hHI, hcanK, hδF, hacc, hrad,
    hord, hscaleK, hbirthA, hpinchK0, hpinchF, hslabK, hderF, hT₀a, hQR, hcwpLF, ⟨d⟩, hdistQ,
    ⟨κ, Aκ, r, ρV, hκ, hρV, hroom, hdistσ, hκR, hκRF⟩, hclosG, hclosGF⟩ :=
    hgapF8 (fun k => ind (k + 1)) (fun k => c (k + 1)) (fun k => hc (k + 1)) (fun k => Tn (k + 1))
      (fun k => pT (k + 1)) hTc' (fun k => aSeed (k + 1)) (fun k => haT (k + 1))
      (fun k => hclock (k + 1)) (fun k => h1 (k + 1)) (fun k => seedTrace (k + 1))
      (fun k => σ (k + 1)) (fun k => y (k + 1)) (fun k => R (k + 1)) (fun k => hsT (k + 1))
      (fun k => has (k + 1)) (fun k => L (k + 1)) (fun k => hRdef (k + 1)) (fun k => hRpos (k + 1))
      (fun k => (hlt k).le) (hL.comp hφt) (fun k => hsel (k + 1)) (fun k => hgood (k + 1))
      (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
      (hroomT.comp hφt) (hradii.comp hφt) (fun k => hfin (k + 1)) hlt
  obtain ⟨yG, hyG, hsc⟩ := RetainedCoreHistory.finalInterior_data_P6HR
    (K := fun k => (F.tower.history (ind (k + 1))).rescale_P6N (c (k + 1)) (hc (k + 1)))
    (fun k => σ (k + 1)) (fun k => y (k + 1)) (fun k => hfin (k + 1))
  have hRn := fun n => (hRdef (n + 1)).trans (hsc n)
  have hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) < R (n + 1) := fun n => max_lt (hlt n) (hQR n)
  have hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ (n + 1) : ℝ) - B / R (n + 1) := by
    intro B
    rcases le_or_gt B 0 with hB0 | hB0
    · refine Eventually.of_forall fun n => ?_
      have h1' : (aSeed (n + 1) : ℝ) ≤ σ (n + 1) := has (n + 1)
      have h2 : B / R (n + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hB0 (hRpos (n + 1)).le
      linarith [hT₀a n]
    · filter_upwards [hφt.eventually (hwin B hB0)] with n hn
      linarith [hT₀a n]
  exact hcloseF_plus_dec_P6R8 hη hε hεW hεX hεN hεcone hC1 hC2 hCt hC2' hphi
    (K := fun k => (F.tower.history (ind (k + 1))).rescale_P6N (c (k + 1)) (hc (k + 1)))
    (t := fun n => (σ (n + 1) : ℝ)) (fun n => (hfin (n + 1)).1) (fun n => (hfin (n + 1)).2)
    (fun n => rfl) (recordsK := recordsK) recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA
    hpinchK0 (fun n => hpinchF n _) hslabK (fun n => hderF n _)
    (fun n => (hqR n).trans_eq (hRn n)) (fun n hC => hsel (n + 1) (hcwpLF n (yG n) (hyG n) hC))
    (fun k => Kh (k + 1)) rfl (fun k => σ (k + 1)) (fun k => y (k + 1)) (fun k => R (k + 1))
    (fun _ => rfl) hyG hRn (fun k => hRpos (k + 1)) d hT₀ (fun k => Tn (k + 1))
    (fun k => aSeed (k + 1)) (fun k => haT (k + 1)) (fun k => hsT (k + 1)) (fun k => has (k + 1))
    (fun k => pT (k + 1)) (fun k => seedTrace (k + 1)) (fun k => L (k + 1)) (hL.comp hφt) 8
    (by norm_num) (fun k => hgood (k + 1)) (fun T hT => hφt.eventually (hwin T hT)) hdistQ hκ r ρV
    hρV hroom hdistσ hκR hclosG hκRF hclosGF (fun k => hsel (k + 1))

/-- consumer：坏点常数取 ceiling 下界本身时，`hrerunF8_P6R8` 只剩数据 binder `hgapF8`。 -/
example {P : OrientedThreeStage.{0}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {η₁ : ℝ}
    (hη : 0 < η₁ ∧ η₁ < 1 / 11) {ε : ℝ} (hε : 0 < ε)
    (hεW : ε ≤ Classical.choose ancientWitness_decoupled_P6P.{0})
    (hεX : ε ≤ crossingWindowNeckAccuracy.{0}) (hεN : ε ≤ crossingNeckAccuracy.{0})
    (hεcone : ε ≤ coneAccuracy) {C1 C2 : ℝ} {Ctime : ℝ≥0} (hC2' : 0 ≤ C2) :
    True := by
  have _h := hrerunF8_P6R8 (F := F) (C1 := C1) (Ctime := Ctime) hη hε hεW hεX hεN hεcone
    (le_refl (p6CoarseC_C11GT6.{0} η₁)) (le_refl (p6CoarseC_C11GT6.{0} η₁))
    (le_refl (p6CoarseC_C11GT6.{0} η₁).toNNReal) hC2'
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
