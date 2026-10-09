import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10CgDJ3JT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixProdHNF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KDataSupplyP6D

/-!
# J10TAIL G4：hnot 由 HNOTRES 组合付清（DW / Cg 线，`_JT`）

* `j10ResE3_of_seq_JT`（PROVED）：序列形 hnot + `hev` ⇒ 逐点形 `J10ResE3_JT`；
* `DrvResE_DJ3_HNR_JT` / `DrvResE_Cg_DJ3_HNR_JT`：DJ3 孪生的 HNOTRES `_HNR` 档参数化版，无 J10 hnot 合取；
* `drvDJ3_of_HNR_JT` / `drvCgDJ3_of_HNR_JT`（PROVISIONAL[常数约束 `Cs ≤ C1, C2`、`Ctime₀ ≤ Ctime`]）：
  `hnotK_seq_a0_HNF` 取档（`drvRX_HNO_of_HNR` 同法）⇒ DJ3 孪生（hnot 合取付清）。
DT 线不做（Dt 来自先验 TDS，HNOTRES 同）。无新顶层 binder。生成器 `build-logs/scratch/J10TAIL/gen/g4.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

/-- **序列形 hnot ⇒ 逐点形（`_JT`，PROVED）**：`J10ResE2_DJ` / HNOTRES 的 `∀ j : ∀ n, …` 形 + `hev` ⇒
`J10ResE3_JT`（`Function.update` 把给定 `jn` 拼进 `hev` 选出的序列，`yG` 经 activeStage cast 重建）。 -/
theorem j10ResE3_of_seq_JT {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)}
    (hev : ∀ n, ∃ j : Fin (K n).eventCount, (K n).time j.castSucc < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).time j.succ)
    (hseq : ∀ (j : ∀ n, Fin (K n).eventCount) (_hjt : ∀ n, (K n).time (j n).castSucc < (σ n : ℝ))
      (_htj : ∀ n, (σ n : ℝ) < (K n).time (j n).succ)
      (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier), (∀ n, HEq (yK n) (yG n)) →
      ∀ n,
        ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
          (hi : T₀K n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
          (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
          (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
            (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
          (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (qK n).modelRadius),
          A.point i.succ le_rfl hl =
              (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            (σ n : ℝ) - ((K n).prefixAt (j n).castSucc).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i
                hi).static b).neck.scale)⁻¹) :
    J10ResE3_JT K σ yK qK T₀K recordsK := by
  classical
  intro n jn hjt htj yG hyG
  choose jc hjtc htjc using hev
  let j : ∀ m, Fin (K m).eventCount := Function.update jc n jn
  have hjn : j n = jn := Function.update_self n jn jc
  have hjo : ∀ m, m ≠ n → j m = jc m := fun m h => Function.update_of_ne h jn jc
  have hjt' : ∀ m, (K m).time (j m).castSucc < (σ m : ℝ) := fun m => by
    by_cases h : m = n
    · subst h
      rw [hjn]
      exact hjt
    · rw [hjo m h]
      exact hjtc m
  have htj' : ∀ m, (σ m : ℝ) < (K m).time (j m).succ := fun m => by
    by_cases h : m = n
    · subst h
      rw [hjn]
      exact htj
    · rw [hjo m h]
      exact htjc m
  have hact : ∀ m, (K m).toHistory.activeStage (σ m) = (j m).castSucc := fun m =>
    activeStage_eq_of_mem_slab_HSX (K m) (j m) (σ m) (hjt' m).le (htj' m)
  let yG' : ∀ m, ((K m).stage (j m).castSucc).Carrier := fun m =>
    cast (congrArg (fun s => ((K m).stage s).Carrier) (hact m)) (yK m)
  have hyG' : ∀ m, HEq (yK m) (yG' m) := fun m => (cast_heq _ _).symm
  have key : ∀ (j₁ : Fin (K n).eventCount) (y₁ : ((K n).stage j₁.castSucc).Carrier),
      j₁ = jn → HEq y₁ yG → (
        ¬ ∃ (i : Fin ((K n).prefixAt j₁.castSucc).eventCount)
          (hi : T₀K n ≤ ((K n).prefixAt j₁.castSucc).time i.succ)
          (hl : i.succ ≤ Fin.last ((K n).prefixAt j₁.castSucc).eventCount)
          (A : BackwardPointTrace ((K n).prefixAt j₁.castSucc).toHistory i.succ
            (Fin.last ((K n).prefixAt j₁.castSucc).eventCount) hl y₁)
          (b : (((K n).prefixAt j₁.castSucc).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (qK n).modelRadius),
          A.point i.succ le_rfl hl =
              (((K n).prefixLateRecords_P6N j₁.castSucc (recordsK n) i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            (σ n : ℝ) - ((K n).prefixAt j₁.castSucc).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * ((((K n).prefixLateRecords_P6N j₁.castSucc (recordsK n) i
                hi).static b).neck.scale)⁻¹) →
        ¬ ∃ (i : Fin ((K n).prefixAt jn.castSucc).eventCount)
          (hi : T₀K n ≤ ((K n).prefixAt jn.castSucc).time i.succ)
          (hl : i.succ ≤ Fin.last ((K n).prefixAt jn.castSucc).eventCount)
          (A : BackwardPointTrace ((K n).prefixAt jn.castSucc).toHistory i.succ
            (Fin.last ((K n).prefixAt jn.castSucc).eventCount) hl yG)
          (b : (((K n).prefixAt jn.castSucc).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (qK n).modelRadius),
          A.point i.succ le_rfl hl =
              (((K n).prefixLateRecords_P6N jn.castSucc (recordsK n) i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            (σ n : ℝ) - ((K n).prefixAt jn.castSucc).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * ((((K n).prefixLateRecords_P6N jn.castSucc (recordsK n) i
                hi).static b).neck.scale)⁻¹ := by
    rintro j₁ y₁ rfl h hP
    obtain rfl := eq_of_heq h
    exact hP
  exact key (j n) (yG' n) hjn ((hyG' n).symm.trans hyG) (hseq j hjt' htj' yG' hyG' n)

/-- **`DrvResE_DJ3_JT` 的档参数化孪生（`_JT`，逐字缩写 def，非合同 Prop）**：HNOTRES `_HNR` 同款四改
（预给 `Nf ζ Rn δ₀ m₀`、records 档换序列、birth 因子 `max (n+1) (Nf n)`、`1 ≤ a₀K·scale` ∀ n），
并删去 `J10ResE3_JT` 合取（hnot 由 `hnotK_seq_a0_HNF` 付）。 -/
def DrvResE_DJ3_HNR_JT {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (T₀ Qt : ℕ → ℝ) (a₀ : ℝ) : Prop :=
  ∀ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ), (∀ n, 0 < ζ n) → (∀ n, 0 < δ₀ n) →
    (∀ n : ℕ, ζ n ≤ 1 / ((n : ℝ) + 1)) → (∀ n : ℕ, δ₀ n ≤ 1 / ((n : ℝ) + 1)) →
    (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) → (∀ n : ℕ, n + 2 ≤ m₀ n) →
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
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
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
        ∃ (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            GeometricCutoffRecord (K n).toHistory i (qK n)),
          (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
            ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
              (σ n : ℝ) - T / R n < (K n).time i.succ →
              2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
                ((recordsK n i hi).static b).neck.scale) ∧
          (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n : ℕ, (qK n).modelAccuracy ≤ ζ n) ∧
          (∀ n : ℕ, Rn n ≤ (qK n).modelRadius) ∧
          (∀ n : ℕ, m₀ n ≤ (qK n).modelOrder) ∧
          ∃ (r₀ w : ℝ), 0 < r₀ ∧ 0 < w ∧
          (∀ᶠ n in atTop,
              ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
                Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
                    (r₀ / Real.sqrt (R n)))) ∧
          ∃ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
                    (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) ∧
          ∃ (κU : ℝ) (phi : ℝ → ℝ), 0 < κU ∧ Perelman.AdmissiblePinchingFunction phi ∧
          ∃ (Q a₀K : ℕ → ℝ),
          (∀ n, a₀K n = a₀ / c n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
            -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
          (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ δ₀ n) ∧
          (∀ (n : ℕ) i hi b, max ((n : ℝ) + 1) (Nf n) * max ((n : ℝ) + 1) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b,
            1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi) ∧
          (∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2) ∧
          (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) ∧
          (∃ (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
            (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
              ((K n).time (Fin.last (K n).eventCount)) (K n).horizon),
            (∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl) ∧
            (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
            (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) phi) ∧
            (∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)) ∧
          (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
            (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
            (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ∀ b : ℝ, 0 < b → b ≤ (1 / 200 : ℝ) → (Kh n).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
            (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
            (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ∀ b : ℝ, 0 < b → b ≤ (1 / 200 : ℝ) → (Kh n).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
              Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi) ∧
          ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ (j : ∀ k, Fin (K k).eventCount),
            (∀ k, (K k).time (j k).castSucc < (σ k : ℝ)) →
            (∀ k, (σ k : ℝ) < (K k).time (j k).succ) →
            ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
              ∀ (i : Fin (K n).eventCount)
                (_hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
                (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
                ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
                  (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * ((((records (ind n) i).rescale_P6M (c n)
                    (hc n)).static b).neck.scale)⁻¹) →
                ((n : ℝ) + 1) * max ((n : ℝ) + 1)
                    ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
                  (((records (ind n) i).rescale_P6M (c n) (hc n)).static b).neck.scale

/-- **`DrvResE_Cg_DJ3_JT` 的档参数化孪生（`_JT`，逐字缩写 def，非合同 Prop）**：同上。 -/
def DrvResE_Cg_DJ3_HNR_JT {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (Cg ε C1 C2 : ℝ)
    (Ctime : ℝ≥0) (εb C1b C2b : ℝ) (Ctimeb : ℝ≥0) (T₀ Qt : ℕ → ℝ)
    (a₀ : ℝ) : Prop :=
  ∀ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ), (∀ n, 0 < ζ n) → (∀ n, 0 < δ₀ n) →
    (∀ n : ℕ, ζ n ≤ 1 / ((n : ℝ) + 1)) → (∀ n : ℕ, δ₀ n ≤ 1 / ((n : ℝ) + 1)) →
    (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) → (∀ n : ℕ, n + 2 ≤ m₀ n) →
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
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl εb C1b C2b Ctimeb (σ k) (y k)) →
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
              Cg * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
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
        ∃ (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            GeometricCutoffRecord (K n).toHistory i (qK n)),
          (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
            ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
              (σ n : ℝ) - T / R n < (K n).time i.succ →
              2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
                ((recordsK n i hi).static b).neck.scale) ∧
          (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n : ℕ, (qK n).modelAccuracy ≤ ζ n) ∧
          (∀ n : ℕ, Rn n ≤ (qK n).modelRadius) ∧
          (∀ n : ℕ, m₀ n ≤ (qK n).modelOrder) ∧
          ∃ (r₀ w : ℝ), 0 < r₀ ∧ 0 < w ∧
          (∀ᶠ n in atTop,
              ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
                Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
                    (r₀ / Real.sqrt (R n)))) ∧
          ∃ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
                    (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))))) ∧
          ∃ (κU : ℝ) (phi : ℝ → ℝ), 0 < κU ∧ Perelman.AdmissiblePinchingFunction phi ∧
          ∃ (Q a₀K : ℕ → ℝ),
          (∀ n, a₀K n = a₀ / c n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
            -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) ∧
          (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
            (q.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ δ₀ n) ∧
          (∀ (n : ℕ) i hi b, max ((n : ℝ) + 1) (Nf n) * max ((n : ℝ) + 1) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b,
            1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi) ∧
          (∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2) ∧
          (∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) ∧
          (∃ (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
            (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
              ((K n).time (Fin.last (K n).eventCount)) (K n).horizon),
            (∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl) ∧
            (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
            (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) phi) ∧
            (∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)) ∧
          (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
            (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
            (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ∀ b : ℝ, 0 < b → b ≤ (1 / 200 : ℝ) → (Kh n).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
            (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
            (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ∀ b : ℝ, 0 < b → b ≤ (1 / 200 : ℝ) → (Kh n).isParabolicallyRmControlledBall τ zz b →
                ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
                  riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                    (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
            ((K n).toHistory.event i).incoming.flow
            (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
              Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi) ∧
          ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ (j : ∀ k, Fin (K k).eventCount),
            (∀ k, (K k).time (j k).castSucc < (σ k : ℝ)) →
            (∀ k, (σ k : ℝ) < (K k).time (j k).succ) →
            ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
              ∀ (i : Fin (K n).eventCount)
                (_hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
                (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
                ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
                  (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * ((((records (ind n) i).rescale_P6M (c n)
                    (hc n)).static b).neck.scale)⁻¹) →
                ((n : ℝ) + 1) * max ((n : ℝ) + 1)
                    ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
                  (((records (ind n) i).rescale_P6M (c n) (hc n)).static b).neck.scale

/-- **hnot 由 hnotK producer 付（`_JT`，PROVISIONAL[`DrvResE_DJ3_HNR_JT` 残余；
常数约束 `Cs ≤ C1`、`Cs ≤ C2`、`Ctime₀ ≤ Ctime`（HNOTRES G-c）]）**：
`hnotK_seq_a0_HNF` + HNOTRES `drvRX_HNO_of_HNR` 同法取档，`j10ResE3_of_seq_JT` 落到逐点形。 -/
theorem drvDJ3_of_HNR_JT {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
      {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ},
      Cs ≤ C1 → Cs ≤ C2 → Ctime₀ ≤ Ctime →
      DrvResE_DJ3_HNR_JT F q records ε C1 C2 Ctime T₀ Qt a₀ →
      DrvResE_DJ3_JT F q records ε C1 C2 Ctime T₀ Qt a₀ := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, hall⟩ := RetainedCoreHistory.hnotK_seq_a0_HNF.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, ?_⟩
  intro P g F q records C1 C2 Ctime T₀ Qt a₀ hC1 hC2 hCt h
  obtain ⟨Cb, Rn0, ζ0, δ0, m0, hCb, hRn0, hζ0, hδ0, hprod⟩ :=
    hall Ctime (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) RetainedCoreHistory.thetaCap_lt_one_HNF
  have h' := h (fun n => (Cb n)⁻¹) (fun n => min (ζ0 n) (1 / ((n : ℝ) + 1)))
    (fun n => max (Rn0 n) ((n : ℝ) + 1)) (fun n => min (δ0 n) (1 / ((n : ℝ) + 1)))
    (fun n => max (m0 n) (n + 2)) (fun n => lt_min (hζ0 n) (by positivity))
    (fun n => lt_min (hδ0 n) (by positivity)) (fun n => min_le_right _ _)
    (fun n => min_le_right _ _) (fun n => le_max_right _ _) (fun n => le_max_right _ _)
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, r₀, w, hr0, hw, hvol, Phi, hPhi,
    hcurv, κU, phi, hκ, hphi, Q, a₀K, ha₀K, hHI, hδ, hb, hbA, hPhiA, hT₀X, hslab, hrest2⟩ :=
    h' A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  have hQp : ∀ n : ℕ, 0 < max ((n : ℝ) + 1) (Q n) := fun n =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hslab' : ∀ n : ℕ, (K n).EventSlabsDerivative Ctime (max ((n : ℝ) + 1) (Q n))
      (Fin.last (K n).eventCount) := fun n =>
    RetainedCoreHistory.eventSlabsDerivative_mono_P6D (hslab n) (le_max_right _ _)
  refine ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, fun n => (hacc n).trans (min_le_right _ _),
    fun n => (le_max_right _ _).trans (hrad n), fun n => (le_max_right _ _).trans (hord n), r₀,
    w, hr0, hw, hvol, Phi, hPhi, hcurv, κU, phi, hκ, hphi, Q, a₀K, ha₀K, hHI,
    fun n i hi => (hδ n i hi).trans (min_le_right _ _),
    fun n i hi b => ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_of_lt (hQp n))).trans (hb n i hi b)),
    Filter.Eventually.of_forall fun n i hi b => hbA n i hi b, hPhiA, ?_, hT₀X, hslab, hrest2⟩
  refine j10ResE3_of_seq_JT hev fun j hjt htj yG hyG => ?_
  refine RetainedCoreHistory.hnot_prefix_of_hnotK_HNF (t := fun n => (σ n : ℝ))
    (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) (D := fun n => (n : ℝ) + 1) j recK yG (fun _ => le_rfl)
    (fun _ => le_rfl) ?_
  exact hprod hC1 hC2 hCt σ hjt htj (Q := fun n => max ((n : ℝ) + 1) (Q n)) (T₀ := T₀K)
    (p := qK) (pF := fun n => q.rescale_P6N (c n) (hc n)) (recordsK := recK)
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := a₀K) hHI hcanK
    (fun n i hi => (hδ n i hi).trans (min_le_left _ _))
    (fun n => (hacc n).trans (min_le_left _ _)) (fun n => (le_max_left _ _).trans (hrad n))
    (fun n => (le_max_left _ _).trans (hord n)) hQp
    (fun n => ((K n).prefixDt_of_lastDt_HNF (j n) (hslab' n) le_rfl).1)
    (fun n => ((K n).prefixDt_of_lastDt_HNF (j n) (hslab' n) (htj n).le).2)
    (fun n i hi b _ _ => by
      have h1 := hb n i hi b
      have h2 : (Cb n)⁻¹ * max ((n : ℝ) + 1) (Q n) ≤ ((recK n i hi).static b).neck.scale :=
        ((mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (hQp n))).trans h1)
      exact (inv_mul_le_iff₀ (hCb n)).mp h2)
    (fun n i hi b _ _ => hbA n i hi b) y hyG hsel

/-- **hnot 由 hnotK producer 付（`_JT`，PROVISIONAL[`DrvResE_Cg_DJ3_HNR_JT` 残余；
常数约束 `Cs ≤ C1b`、`Cs ≤ C2b`、`Ctime₀ ≤ Ctimeb`（HNOTRES G-c）]）**：
`hnotK_seq_a0_HNF` + HNOTRES `drvRX_HNO_of_HNR` 同法取档，`j10ResE3_of_seq_JT` 落到逐点形。 -/
theorem drvCgDJ3_of_HNR_JT {εb : ℝ} (hε : 0 < εb) (hε' : εb < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
      {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1b C2b : ℝ} {Ctimeb : ℝ≥0}
      {T₀ Qt : ℕ → ℝ} {a₀ : ℝ},
      Cs ≤ C1b → Cs ≤ C2b → Ctime₀ ≤ Ctimeb →
      DrvResE_Cg_DJ3_HNR_JT F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ →
      DrvResE_Cg_DJ3_JT F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, hall⟩ := RetainedCoreHistory.hnotK_seq_a0_HNF.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, ?_⟩
  intro P g F q records Cg ε C1 C2 Ctime C1b C2b Ctimeb T₀ Qt a₀ hC1 hC2 hCt h
  obtain ⟨Cb, Rn0, ζ0, δ0, m0, hCb, hRn0, hζ0, hδ0, hprod⟩ :=
    hall Ctime (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) RetainedCoreHistory.thetaCap_lt_one_HNF
  have h' := h (fun n => (Cb n)⁻¹) (fun n => min (ζ0 n) (1 / ((n : ℝ) + 1)))
    (fun n => max (Rn0 n) ((n : ℝ) + 1)) (fun n => min (δ0 n) (1 / ((n : ℝ) + 1)))
    (fun n => max (m0 n) (n + 2)) (fun n => lt_min (hζ0 n) (by positivity))
    (fun n => lt_min (hδ0 n) (by positivity)) (fun n => min_le_right _ _)
    (fun n => min_le_right _ _) (fun n => le_max_right _ _) (fun n => le_max_right _ _)
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, hacc, hrad, hord, r₀, w, hr0, hw, hvol, Phi, hPhi,
    hcurv, κU, phi, hκ, hphi, Q, a₀K, ha₀K, hHI, hδ, hb, hbA, hPhiA, hT₀X, hslab, hrest2⟩ :=
    h' A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  have hQp : ∀ n : ℕ, 0 < max ((n : ℝ) + 1) (Q n) := fun n =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hslab' : ∀ n : ℕ, (K n).EventSlabsDerivative Ctime (max ((n : ℝ) + 1) (Q n))
      (Fin.last (K n).eventCount) := fun n =>
    RetainedCoreHistory.eventSlabsDerivative_mono_P6D (hslab n) (le_max_right _ _)
  refine ⟨qK, T₀K, recK, hsep, hT₀K, hcanK, fun n => (hacc n).trans (min_le_right _ _),
    fun n => (le_max_right _ _).trans (hrad n), fun n => (le_max_right _ _).trans (hord n), r₀,
    w, hr0, hw, hvol, Phi, hPhi, hcurv, κU, phi, hκ, hphi, Q, a₀K, ha₀K, hHI,
    fun n i hi => (hδ n i hi).trans (min_le_right _ _),
    fun n i hi b => ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_of_lt (hQp n))).trans (hb n i hi b)),
    Filter.Eventually.of_forall fun n i hi b => hbA n i hi b, hPhiA, ?_, hT₀X, hslab, hrest2⟩
  refine j10ResE3_of_seq_JT hev fun j hjt htj yG hyG => ?_
  refine RetainedCoreHistory.hnot_prefix_of_hnotK_HNF (t := fun n => (σ n : ℝ))
    (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) (D := fun n => (n : ℝ) + 1) j recK yG (fun _ => le_rfl)
    (fun _ => le_rfl) ?_
  exact hprod hC1 hC2 hCt σ hjt htj (Q := fun n => max ((n : ℝ) + 1) (Q n)) (T₀ := T₀K)
    (p := qK) (pF := fun n => q.rescale_P6N (c n) (hc n)) (recordsK := recK)
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (a₀ := a₀K) hHI hcanK
    (fun n i hi => (hδ n i hi).trans (min_le_left _ _))
    (fun n => (hacc n).trans (min_le_left _ _)) (fun n => (le_max_left _ _).trans (hrad n))
    (fun n => (le_max_left _ _).trans (hord n)) hQp
    (fun n => ((K n).prefixDt_of_lastDt_HNF (j n) (hslab' n) le_rfl).1)
    (fun n => ((K n).prefixDt_of_lastDt_HNF (j n) (hslab' n) (htj n).le).2)
    (fun n i hi b _ _ => by
      have h1 := hb n i hi b
      have h2 : (Cb n)⁻¹ * max ((n : ℝ) + 1) (Q n) ≤ ((recK n i hi).static b).neck.scale :=
        ((mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (hQp n))).trans h1)
      exact (inv_mul_le_iff₀ (hCb n)).mp h2)
    (fun n i hi b _ _ => hbA n i hi b) y hyG hsel

/-- **组合 consumer（`_JT`，PROVISIONAL[`DrvResE_DJ3_HNR_JT` 残余；`Cs ≤ C1, C2`、`Ctime₀ ≤ Ctime`]）**：
HNR 档参数化孪生 ⇒ DRVWIRE 核 `DrvResE_DW`（再接既有全局桥 `hDrvJ/hDext_of_drvRes_DW`）；`ha₀` 引擎级。 -/
theorem drvDW_of_HNR_JT {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
      {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}, 0 < a₀ → 0 ≤ C2 →
      Cs ≤ C1 → Cs ≤ C2 → Ctime₀ ≤ Ctime →
      DrvResE_DJ3_HNR_JT F q records ε C1 C2 Ctime T₀ Qt a₀ →
      DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, hall⟩ := drvDJ3_of_HNR_JT.{u} hε hε'
  exact ⟨Ct₀, Cs, hCt₀, hCs, fun ha₀ hC2 h1 h2 h3 h =>
    drvResE_DW_of_DJ3_JT ha₀ hC2 (hall h1 h2 h3 h)⟩

/-- **组合 consumer Cg 线（`_JT`，PROVISIONAL[同上，常数取 `C1b C2b Ctimeb`]）**：⇒ `DrvResE_Cg_DC`。 -/
theorem drvCgDC_of_HNR_JT {εb : ℝ} (hε : 0 < εb) (hε' : εb < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
      {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1b C2b : ℝ} {Ctimeb : ℝ≥0}
      {T₀ Qt : ℕ → ℝ} {a₀ : ℝ}, 0 < a₀ → 0 ≤ C2 →
      Cs ≤ C1b → Cs ≤ C2b → Ctime₀ ≤ Ctimeb →
      DrvResE_Cg_DJ3_HNR_JT F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt a₀ →
      DrvResE_Cg_DC F q records Cg ε C1 C2 Ctime εb C1b C2b Ctimeb T₀ Qt := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, hall⟩ := drvCgDJ3_of_HNR_JT.{u} hε hε'
  exact ⟨Ct₀, Cs, hCt₀, hCs, fun ha₀ hC2 h1 h2 h3 h =>
    drvResE_Cg_DC_of_DJ3_JT ha₀ hC2 (hall h1 h2 h3 h)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
