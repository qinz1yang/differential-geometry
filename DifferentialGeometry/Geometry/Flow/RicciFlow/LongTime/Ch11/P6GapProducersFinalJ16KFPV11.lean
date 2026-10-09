import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapJ16WireFinalCJ16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersFinalLocKFP

/-!
# final producer：J16PT 条件形 × KFPROD 三合取（O-CH11-W10，后缀 `_V11`）

J16PT G6 `hgapJF{,8}_locC_of_producers_J16`（final OPEN = {hK, hDext} 经 hJ11F / hOpenF*J）逐字孪生，叠加
KFPROD
`gen6g.py` 对 FCOND R4 producer 的同一组编辑：结论换 `hgapJF{,8}_locCR_KFP`（R43 三合取），加前提
`hCt0 : Ctime₀ ≤ Ctime`；`0 < a₀/c` ⇐ `div_pos`；`ρ̃⁻² ≤ Q` ⇐ `neckRadius_rescale_inv_sq_P6X` +
`le_max_right`。
生成器 `build-logs/scratch/W10/gen/gen_kfp.py`。
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
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6CoarseC_eq_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6
  p6FineEta_le_C11GT6)

namespace ObservedHistory

theorem hgapJF_locCR_of_producers_J16_V11 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z))
    {Ctime₀ : ℝ≥0} (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime₀)
    (hCt0 : Ctime₀ ≤ Ctime)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {T₀ Qt : ℕ → ℝ}
    (hT₀ : ∀ n, lateThrJF_P6WR2 a₀ records hP5L hδq hanti n ≤ T₀ n)
    (hJ11F : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
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
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ)))
    (hJ15F : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))))
    (hOpenFJ : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier),
        HEq (y n) yG' →
        ¬ (∃ (i : Fin (K n).eventCount)
        (hi : max 1 (T₀ n / c n) ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl =
          (((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) *
              ((((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale)⁻¹))) ∧
          (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T)) :
    hgapJF_locCR_KFP F q ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨Phi, hPhi, hphi⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      (a₀ := 1) one_pos
  have hT₀' : ∀ n, Classical.choose (diagonalPack_nom_CXKN (H := F.tower.history) records
      (fun n => 1 / ((n : ℝ) + 1) ^ 2) (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1))
      (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) (fun n => ⟨by positivity, le_rfl⟩)
      (fun n => by positivity) (fun n => by positivity) ha₀ (fun _ => 0) hP5L hδq hanti) n ≤
      T₀ n := fun n => by
    have h := hT₀ n
    unfold lateThrJF_P6WR2 at h
    simp only [eq_true ha₀, dite_true] at h
    exact h
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hfin hlt
  obtain ⟨hK, hDx⟩ :=
    hOpenFJ A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
  -- D-7：records / J4 / J5 / J8 取 KNOM 的一次 `choose_spec`（固定档 ζ = δ₀ = 1/(n+1)、Rn = n+1、m₀ = n+2）
  obtain ⟨p, recordsK, hcan, hδ, hacc, hrad, hord, -, hJ8, -, -, -⟩ :=
    Classical.choose_spec (diagonalPack_nom_CXKN (H := F.tower.history) records
      (fun n => 1 / ((n : ℝ) + 1) ^ 2) (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1))
      (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) (fun n => ⟨by positivity, le_rfl⟩)
      (fun n => by positivity) (fun n => by positivity) ha₀ (fun _ => 0) hP5L hδq hanti) T₀ hT₀' ind
  obtain ⟨hJ6, hCWS⟩ := hK p recordsK hcan hδ hacc hrad hord hJ8
  obtain ⟨κd, hκd, hvolO⟩ :=
    hJ11F A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
    p recordsK hcan hδ hacc hrad hord hJ8 hJ6
  obtain ⟨κ, ρV, hκ, hρV, hκR, hκRF⟩ :=
    hJ15F A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
    p recordsK hcan hδ hacc hrad hord hJ8 hJ6
  -- 重标度窗口 HI（年龄 `0 + τ`）⇐ 原尺度 records + 初始 HI（同 jointD 映射）
  have hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (0 + τ') x :=
    fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (records (ind n)) ha₀ (hHI (ind n))
  have hJ16 := ObservedHistory.j16_of_depthExt_HI_J16 Kh Tn aSeed σ haT hsT has pT seedTrace
    y R L hRpos hRr h1 hwin (fun _ => 0) (fun _ => le_rfl) hpin hDx
  have hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
      ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, 1 ≤ a ∧
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x := by
    intro T hT
    filter_upwards [hwin T hT] with n hn
    intro v _ hv x
    exact ⟨0 + (v : ℝ), by linarith [h1 n], hpin n v x⟩
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have := hRr n
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simp only [one_pow, mul_one]
    exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlateR : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hwin T hT] with n hn
    have ha1 : (1 : ℝ) ≤ (σ n : ℝ) - T / R n := (h1 n).trans hn
    calc (1 : ℝ) ≤ R n * 1 := by linarith [hR1 n]
      _ ≤ R n * ((σ n : ℝ) - T / R n) := mul_le_mul_of_nonneg_left ha1 (by linarith [hR1 n])
  -- event `hclosG` ⇐ J16 `hscalU` + first exit（同 jointD）
  have hclosG := hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
    (fun _ => 1) hL hsm hclock hRr1 hwin hlateR le_rfl hpin hJ16
  -- 条件形 `hdistC`（FINALQ G1）：`R ≤ Q`、`2 < Tn`（原尺度 `2 r² < Tno`）、其余为 ∃ 元组自有数据
  have hRQ : ∀ n, R n ≤ c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹ := by
    intro n
    refine (hQρ n).trans ?_
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q]
    have hcT : c n * (Tn n : ℝ) = (Tno n : ℝ) := by
      change c n * ((Tno n : ℝ) / c n) = (Tno n : ℝ)
      have hcne : c n ≠ 0 := (hc n).ne'
      field_simp
    rw [hcT]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hc n).le
  have htimeT : ∀ n, 2 * (1 : ℝ) ^ 2 < (Tn n : ℝ) := by
    intro n
    have h2 := htime n
    have hcn := hc n
    change 2 * (1 : ℝ) ^ 2 < (Tno n : ℝ) / c n
    rw [lt_div_iff₀ hcn]
    change 2 * (1 : ℝ) ^ 2 * (r n ^ 2) < (Tno n : ℝ)
    linarith
  have hdistC := hdistC_final_of_scaleK_P6FQ (K := K) σ y R hfin hRpos (fun n => (hlt n).le) Tn
    aSeed haT hsT has pT seedTrace L hL hroom htimeT hsm hclock hwin
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (fun n => div_pos ha₀ (hc n))
    (fun n => (Ho n).hHI_rescale_P6X3 (hc n) (hHI (ind n)))
    (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n)) hacc hrad hord
    (fun n => (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hJ6 n)) hRQ
    (fun n => max_le (h1 n) (by rw [div_le_iff₀ (hc n)]; linarith [hT₀l n]))
  have hclosGF := ObservedHistory.hclosGF_C_of_depthExt_HI_J16 Kh Tn aSeed σ haT hsT has pT
    seedTrace y R L hRpos hL hwin hdistC hRr h1 (fun _ => 0) (fun _ => le_rfl) hpin hDx
  have hQρF : ∀ n, ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
      c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹ := fun n => by
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q,
      (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hc n).le
  refine ⟨Ctime₀, Phi, fun n => c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹,
    fun n => max 1 (T₀ n / c n), fun n => (p n).rescale_P6N (c n) (hc n),
    fun n => q.rescale_P6N (c n) (hc n), fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n),
    fun n => a₀ / c n, hCt0, fun n => div_pos ha₀ (hc n), hQρF,
    ⟨fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)⟩, hPhi,
    fun n => (Ho n).hHI_rescale_P6X3 (hc n) (hHI (ind n)),
    fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n),
    fun n => (Ho n).hδF_rescale_P6X3 (hc n) (hδ n), hacc, hrad, hord,
    fun n => (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hJ6 n),
    Eventually.of_forall fun n => (Ho n).hbirthA_rescale_P6X3 (hc n) (recordsK n) (hJ8 n),
    fun n i => (Ho n).toHistory.phiAlmostNonnegative_rescale_P6X2 hphi (hc n) (records (ind n)) ha₀
      (hHI (ind n)) (le_max_left _ _) i,
    fun n hK => (Ho n).phiAlmostNonnegative_finalSlab_rescale_P6WR2 hphi (hc n) (records (ind n))
      ha₀ (hHI (ind n)) (le_max_left _ _) hK,
    fun n => (Ho n).eventSlabsDerivT_rescale_P6KT (hc n)
      (GC.LongTime.Ch11.hslabKT_of_supply_P6KT2 hTD le_rfl hanti (fun t ht => q.neckRadius_pos t ht)
        ind (fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹)
        (fun n => (Tno n : ℝ)) (fun _ => le_max_right _ _) n),
    fun n hK => (Ho n).derivativeBoundBefore_finalSlab_min_rescale_P6KT (hc n)
      (tK := (Tno n : ℝ))
      (fun hK' => GC.LongTime.Ch11.finalSlabDerivT_of_supply_P6KT hTD le_rfl (ind n)
        (fun _ ht0 htK => GC.LongTime.Ch11.ceil_of_antitone_P6KT2 hanti
          (fun t ht => q.neckRadius_pos t ht) (le_max_right _ _) ht0 htK.le) hK') hK,
    fun n => max_le (h1 n) (by rw [div_le_iff₀ (hc n)]; linarith [hT₀l n]),
    hCWS, ⟨κd, hκd, hvolK_of_orig_P6CK (Ho := Ho) (c := c) hc σ y R hRpos hvolO⟩,
    ⟨1, one_pos, hpinL⟩, hdistC, ⟨κ, ρV, hκ, hρV, hκR, hκRF⟩, hclosG, hclosGF⟩

theorem hgapJF8_locCR_of_producers_J16_V11 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z))
    {Ctime₀ : ℝ≥0} (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime₀)
    (hCt0 : Ctime₀ ≤ Ctime)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {T₀ Qt : ℕ → ℝ}
    (hT₀ : ∀ n, lateThrJF_P6WR2 a₀ records hP5L hδq hanti n ≤ T₀ n)
    (hJ11F8 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
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
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
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
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ)))
    (hJ15F8 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
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
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)))))
    (hOpenF8J : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
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
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier),
        HEq (y n) yG' →
        ¬ (∃ (i : Fin (K n).eventCount)
        (hi : max 1 (T₀ n / c n) ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl =
          (((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) *
              ((((Ho n).recordsKRescale_P6X3 (hc n) (recordsK n) i hi).static b).neck.scale)⁻¹))) ∧
          (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T)) :
    hgapJF8_locCR_KFP F q (p6FineEta_C11GT6 ε) (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨Phi, hPhi, hphi⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      (a₀ := 1) one_pos
  have hT₀' : ∀ n, Classical.choose (diagonalPack_nom_CXKN (H := F.tower.history) records
      (fun n => 1 / ((n : ℝ) + 1) ^ 2) (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1))
      (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) (fun n => ⟨by positivity, le_rfl⟩)
      (fun n => by positivity) (fun n => by positivity) ha₀ (fun _ => 0) hP5L hδq hanti) n ≤
      T₀ n := fun n => by
    have h := hT₀ n
    unfold lateThrJF_P6WR2 at h
    simp only [eq_true ha₀, dite_true] at h
    exact h
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hfin hlt
  obtain ⟨hK, hDx⟩ :=
    hOpenF8J A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
  -- D-7：records / J4 / J5 / J8 取 KNOM 的一次 `choose_spec`（固定档 ζ = δ₀ = 1/(n+1)、Rn = n+1、m₀ = n+2）
  obtain ⟨p, recordsK, hcan, hδ, hacc, hrad, hord, -, hJ8, -, -, -⟩ :=
    Classical.choose_spec (diagonalPack_nom_CXKN (H := F.tower.history) records
      (fun n => 1 / ((n : ℝ) + 1) ^ 2) (fun n => (n : ℝ) + 1) (fun n => 1 / ((n : ℝ) + 1))
      (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) (fun n => ⟨by positivity, le_rfl⟩)
      (fun n => by positivity) (fun n => by positivity) ha₀ (fun _ => 0) hP5L hδq hanti) T₀ hT₀' ind
  obtain ⟨hJ6, hCWS⟩ := hK p recordsK hcan hδ hacc hrad hord hJ8
  obtain ⟨κd, hκd, hvolO⟩ :=
    hJ11F8 A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
    p recordsK hcan hδ hacc hrad hord hJ8 hJ6
  obtain ⟨κ, ρV, hκ, hρV, hκR, hκRF⟩ :=
    hJ15F8 A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm
    hT₀l    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hfin hlt
    p recordsK hcan hδ hacc hrad hord hJ8 hJ6
  -- 重标度窗口 HI（年龄 `0 + τ`）⇐ 原尺度 records + 初始 HI（同 jointD 映射）
  have hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (0 + τ') x :=
    fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (records (ind n)) ha₀ (hHI (ind n))
  have hJ16 := ObservedHistory.j16_of_depthExt_HI_J16 Kh Tn aSeed σ haT hsT has pT seedTrace
    y R L hRpos hRr h1 hwin (fun _ => 0) (fun _ => le_rfl) hpin hDx
  have hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
      ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, 1 ≤ a ∧
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x := by
    intro T hT
    filter_upwards [hwin T hT] with n hn
    intro v _ hv x
    exact ⟨0 + (v : ℝ), by linarith [h1 n], hpin n v x⟩
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have := hRr n
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simp only [one_pow, mul_one]
    exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlateR : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hwin T hT] with n hn
    have ha1 : (1 : ℝ) ≤ (σ n : ℝ) - T / R n := (h1 n).trans hn
    calc (1 : ℝ) ≤ R n * 1 := by linarith [hR1 n]
      _ ≤ R n * ((σ n : ℝ) - T / R n) := mul_le_mul_of_nonneg_left ha1 (by linarith [hR1 n])
  -- event `hclosG` ⇐ J16 `hscalU` + first exit（同 jointD）
  have hclosG := hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
    (fun _ => 1) hL hsm hclock hRr1 hwin hlateR le_rfl hpin hJ16
  -- 条件形 `hdistC`（FINALQ G1）：`R ≤ Q`、`2 < Tn`（原尺度 `2 r² < Tno`）、其余为 ∃ 元组自有数据
  have hRQ : ∀ n, R n ≤ c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹ := by
    intro n
    refine (hQρ n).trans ?_
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q]
    have hcT : c n * (Tn n : ℝ) = (Tno n : ℝ) := by
      change c n * ((Tno n : ℝ) / c n) = (Tno n : ℝ)
      have hcne : c n ≠ 0 := (hc n).ne'
      field_simp
    rw [hcT]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hc n).le
  have htimeT : ∀ n, 2 * (1 : ℝ) ^ 2 < (Tn n : ℝ) := by
    intro n
    have h2 := htime n
    have hcn := hc n
    change 2 * (1 : ℝ) ^ 2 < (Tno n : ℝ) / c n
    rw [lt_div_iff₀ hcn]
    change 2 * (1 : ℝ) ^ 2 * (r n ^ 2) < (Tno n : ℝ)
    linarith
  have hdistC := hdistC_final_of_scaleK_P6FQ (K := K) σ y R hfin hRpos (fun n => (hlt n).le) Tn
    aSeed haT hsT has pT seedTrace L hL hroom htimeT hsm hclock hwin
    (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) (fun n => div_pos ha₀ (hc n))
    (fun n => (Ho n).hHI_rescale_P6X3 (hc n) (hHI (ind n)))
    (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n)) hacc hrad hord
    (fun n => (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hJ6 n)) hRQ
    (fun n => max_le (h1 n) (by rw [div_le_iff₀ (hc n)]; linarith [hT₀l n]))
  have hclosGF := ObservedHistory.hclosGF_C_of_depthExt_HI_J16 Kh Tn aSeed σ haT hsT has pT
    seedTrace y R L hRpos hL hwin hdistC hRr h1 (fun _ => 0) (fun _ => le_rfl) hpin hDx
  have hQρF : ∀ n, ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
      c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹ := fun n => by
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q,
      (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hc n).le
  refine ⟨Ctime₀, Phi, fun n => c n * max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹,
    fun n => max 1 (T₀ n / c n), fun n => (p n).rescale_P6N (c n) (hc n),
    fun n => q.rescale_P6N (c n) (hc n), fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n),
    fun n => a₀ / c n, hCt0, fun n => div_pos ha₀ (hc n), hQρF,
    ⟨fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)⟩, hPhi,
    fun n => (Ho n).hHI_rescale_P6X3 (hc n) (hHI (ind n)),
    fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recordsK n) (hcan n),
    fun n => (Ho n).hδF_rescale_P6X3 (hc n) (hδ n), hacc, hrad, hord,
    fun n => (Ho n).hscaleK_rescale_P6X3 (hc n) (recordsK n) (hJ6 n),
    Eventually.of_forall fun n => (Ho n).hbirthA_rescale_P6X3 (hc n) (recordsK n) (hJ8 n),
    fun n i => (Ho n).toHistory.phiAlmostNonnegative_rescale_P6X2 hphi (hc n) (records (ind n)) ha₀
      (hHI (ind n)) (le_max_left _ _) i,
    fun n hK => (Ho n).phiAlmostNonnegative_finalSlab_rescale_P6WR2 hphi (hc n) (records (ind n))
      ha₀ (hHI (ind n)) (le_max_left _ _) hK,
    fun n => (Ho n).eventSlabsDerivT_rescale_P6KT (hc n)
      (GC.LongTime.Ch11.hslabKT_of_supply_P6KT2 hTD le_rfl hanti (fun t ht => q.neckRadius_pos t ht)
        ind (fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹)
        (fun n => (Tno n : ℝ)) (fun _ => le_max_right _ _) n),
    fun n hK => (Ho n).derivativeBoundBefore_finalSlab_min_rescale_P6KT (hc n)
      (tK := (Tno n : ℝ))
      (fun hK' => GC.LongTime.Ch11.finalSlabDerivT_of_supply_P6KT hTD le_rfl (ind n)
        (fun _ ht0 htK => GC.LongTime.Ch11.ceil_of_antitone_P6KT2 hanti
          (fun t ht => q.neckRadius_pos t ht) (le_max_right _ _) ht0 htK.le) hK') hK,
    fun n => max_le (h1 n) (by rw [div_le_iff₀ (hc n)]; linarith [hT₀l n]),
    hCWS, ⟨κd, hκd, hvolK_of_orig_P6CK (Ho := Ho) (c := c) hc σ y R hRpos hvolO⟩,
    ⟨1, one_pos, hpinL⟩, hdistC, ⟨κ, ρV, hκ, hρV, hκR, hκRF⟩, hclosG, hclosGF⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
