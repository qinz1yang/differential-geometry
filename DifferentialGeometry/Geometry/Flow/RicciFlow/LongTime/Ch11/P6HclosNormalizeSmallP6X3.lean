import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HclosNormalizeP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeSmallP6X3

/-!
# D-17 端到端（hclosG 首出时刻版）去掉 `hsmallN` 缺口（O-CH11-P6SEL3 G4b，后缀 `_P6X3`）

**`canonicalLateCore_of_normalizedS_hclos_P6X3`**：G3 `canonicalLateCore_of_normalized_hclos_P6X3` 的
升级版：
种子小曲率 `hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1` 从 `hgapS` 的结论（缺口 `hsmallN`）移到
`hgapSS` / `hrestS` 的量词前缀——由 G4a `canonicalLateCore_of_normalizedS_P6X3` 供给（原 history 的 hsmall
经 `hasSmallParabolicCurvature_rescale_P6X3`，`c = r²`）。前缀里多一项只让 `hgapSS` / `hrestS` 更弱。
证明：G4a normalizedS ∘ 纯类分解（`exists_strictMono_interior_or_boundary_P6S`，event 类下标平移）∘
event 支（`hgapSS` ⇒ 原尺度 K 层经 G1 `KdataRescale_P6X3`、`hcwpL` 换形、`hclosG` 经 P6ANCH4
`hclosG_of_firstExit_P6M4`（`hsmall` 取前缀、`hpin` 取 G3 `hpin_rescale_P6X3`）⇒ P6SEL2 G1a
`false_of_selected_eventInterior_lateHI_P6X2`）；final / 边界类 ⇒ `hrestS`。
剩余显式 binder：`hgapSS`（K 层原尺度项 + selection 侧 `T₀ ≤ c·aSeed`、`c·Q < R`、`hcwpL`、`d`、`hdistQ`、
κ 组、`hscalU`）与 `hrestS`。陈述由 build-logs/scratch/O-CH11-P6SEL3/mk_g4b.py 生成。
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

namespace ObservedHistory

/-- **D-17 端到端，hclosG 首出时刻版，无 `hsmallN`（`_P6X3`）**：见文件头。 -/
theorem canonicalLateCore_of_normalizedS_hclos_P6X3 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C ≤ C1 → C ≤ C2 → C.toNNReal ≤ Ctime →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      (hgapSS : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let K : ℕ → RetainedCoreHistory.{u} := fun k =>
          (F.tower.history (ind k)).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
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
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (Ctime₀ : ℝ≥0) (Q T₀ : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            T₀ n ≤ (Ho n).time i.succ → GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℕ → ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          (∀ n, 0 < a₀ n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) (a₀ n) x ∧
            -3 / a₀ n ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Q n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, T₀ n ≤ c n * (aSeed n : ℝ)) ∧
          (∀ n, c n * Q n < R n) ∧
          (∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' →
        (∃ (i : Fin (Ho n).eventCount) (hi : T₀ n ≤ (Ho n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (Ho n).toHistory i.succ j'.castSucc hl yG')
        (b : ((Ho n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (c n * ((recordsK n i hi).static b).neck.scale)⁻¹) →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) ∧
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
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestS : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
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
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selected_eventInterior_lateHI_P6X2.{u}
  obtain ⟨Phi, hPhi, hK⟩ := KdataRescale_P6X3.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall' hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall' hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1 C2 Ctime} hC1 hC2 hCt => ?_⟩
  intro P g F q hanti hcan hder hgap hrest
  have evb : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
          let K : ℕ → RetainedCoreHistory.{u} := fun k =>
            (F.tower.history (ind k)).rescale_P6N (c k) (hc k)
          let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
          let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
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
            ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
            (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).time j.succ) →
            (∀ k : ℕ, (k : ℝ) + 1 < R k) →
          False := by
    intro ind c hc K Kh Ho Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
      hRr hL hsel hgood hwin hwin' hroom hradii hev hlt
    obtain ⟨Ctime₀, Q, T₀, p, pF, recordsK, a₀, ⟨recordsF⟩, ha₀, hHI, hcanK, hδF, hacc, hrad, hord,
      hscaleK, hbirthA, hslabK, hT₀a, hQR, hcwpL, ⟨d⟩, hdistQ,
      ⟨κ, Aκ, r, ρV, hκ, hρV, hroomκ, hdistσ, hκR⟩, hscalU⟩ :=
      hgap ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
        hsel hgood hwin hwin' hroom hradii hev hlt
    obtain ⟨hHI', hcanK', hδF', hscaleK', hbirthA', hpinch', hslab'⟩ :=
      hK (fun k => F.tower.history (ind k)) c hc Ctime₀ Q T₀ p pF recordsK a₀ recordsF ha₀ hHI
        hcanK hδF hscaleK hbirthA hslabK
    have hT₀a' : ∀ n, max 1 (T₀ n / c n) ≤ (aSeed n : ℝ) := fun n => by
      refine max_le (h1 n) ?_
      rw [div_le_iff₀ (hc n)]
      linarith [hT₀a n]
    have hR1 : ∀ n, 1 ≤ R n := fun n => by
      have := hRr n
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
      simp only [one_pow, mul_one]
      exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
      intro T hT
      filter_upwards [hwin T hT] with n hn
      have ha1 : (1 : ℝ) ≤ (σ n : ℝ) - T / R n := (h1 n).trans hn
      calc (1 : ℝ) ≤ R n * 1 := by linarith [hR1 n]
        _ ≤ R n * ((σ n : ℝ) - T / R n) := mul_le_mul_of_nonneg_left ha1 (by linarith [hR1 n])
    have hclosG := hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
      (fun _ => 1) hL hsm hclock hRr1 hwin hlate le_rfl
      (fun n => (F.tower.history (ind n)).toHistory.hpin_rescale_P6X3 (hc n) (recordsF n) (ha₀ n)
        (hHI n)) hscalU
    refine hB' hC1 hC2 hCt hPhi (K := K) (Q := fun n => c n * Q n)
      (T₀ := fun n => max 1 (T₀ n / c n)) (p := fun n => (p n).rescale_P6N (c n) (hc n))
      (pF := fun n => (pF n).rescale_P6N (c n) (hc n)) (a₀ := fun n => a₀ n / c n)
      (recordsK := fun n => (F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recordsK n))
      (fun n i => (recordsF n i).rescale_P6M (c n) (hc n)) hHI' hcanK' hδF' hacc hrad hord hscaleK'
      hbirthA' hpinch' hslab' Kh rfl σ y hev R hRdef hRpos hlt hQR
      (fun n j' yG' hy hcw => ?_) d Tn aSeed haT hsT has hT₀a' pT seedTrace L hL 4 (by norm_num)
      hgood hwin hdistQ hκ r ρV hρV hroomκ hdistσ hκR hclosG hsel
    obtain ⟨i, hi, hl, A, b, x, hA, hx, ht⟩ := hcw
    have hi' : T₀ n ≤ (F.tower.history (ind n)).time i.succ :=
      RetainedCoreHistory.le_time_of_rescale_P6X3 (hc n)
        (t := (F.tower.history (ind n)).time i.succ) hi
    refine hcwpL n j' yG' hy ⟨i, hi', hl,
      (F.tower.history (ind n)).traceOfRescale_P6N (c n) (hc n) A, b, x, ?_, hx, ?_⟩
    · exact hA.trans (congrArg (fun w => w x)
        (((recordsK n i hi').static b).rescale_P6M_window (c n) (hc n)))
    · exact ht.trans_eq (congrArg (fun z => (1 - 1 / ((n : ℝ) + 2)) * z⁻¹)
        (((recordsK n i hi').static b).rescale_P6M_scale (c n) (hc n)))
  refine GC.LongTime.Ch11.canonicalLateCore_of_normalizedS_P6X3 hanti hcan hder ?_
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
    hL hsel hgood hwin hwin' hroom hradii
  have key : ∀ φ : ℕ → ℕ, StrictMono φ →
      ((∀ k, ∃ j : Fin (Kh (φ k)).eventCount, (Kh (φ k)).time j.castSucc < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).time j.succ) ∧ ∀ k : ℕ, (k : ℝ) + 1 < R (φ k)) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).horizon) ∨
        (∀ k, ¬ ∃ W : SpatialCanonicalWitness ((Kh (φ k)).stageMetric
            ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k))) ε C1 C2 (y (φ k)),
          W.capTubeHasNeckChart ε) → False := by
    intro φ hφ hcls
    have hφt := hφ.tendsto_atTop
    have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hTc (φ k))
    have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R (φ k) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hRr (φ k))
    rcases hcls with ⟨hev, hlt⟩ | hcls'
    · exact evb (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
        (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
        (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
        (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
        (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
        (fun k => hRpos (φ k)) hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
        (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
        (hroom.comp hφt) (hradii.comp hφt) hev hlt
    · exact hrest (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k)) (fun k => Tn (φ k))
        (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
        (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
        (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
        (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
        (fun k => hRpos (φ k)) hRr' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
        (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
        (hroom.comp hφt) (hradii.comp hφt) hcls'
  obtain ⟨ψ, hψ, hcls⟩ := exists_strictMono_interior_or_boundary_P6S (Kh := Kh) σ y hsel
  rcases hcls with hev | hfin | hbd
  · have hs : StrictMono fun k : ℕ => ψ (k + 1) :=
      hψ.comp fun a b hab => Nat.add_lt_add_right hab 1
    refine key (fun k => ψ (k + 1)) hs (Or.inl ⟨fun k => hev (k + 1), fun k => ?_⟩)
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (ψ (k + 1) : ℝ) := by exact_mod_cast hψ.id_le (k + 1)
    have hk2 := hRr (ψ (k + 1))
    push_cast at hk1
    linarith
  · exact key ψ hψ (Or.inr (Or.inl hfin))
  · exact key ψ hψ (Or.inr (Or.inr hbd))

/-- consumer：同一组前提 ⇒ S15（`LargerBallCanonicalLateSupply_C11E`，经 `s15_of_canonicalLateCore_P6X`）。 -/
theorem s15_of_normalizedS_hclos_P6X3 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C ≤ C1 → C ≤ C2 → C.toNNReal ≤ Ctime →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      (hgapSS : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let K : ℕ → RetainedCoreHistory.{u} := fun k =>
          (F.tower.history (ind k)).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
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
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
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
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (Ctime₀ : ℝ≥0) (Q T₀ : ℕ → ℝ) (p pF : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            T₀ n ≤ (Ho n).time i.succ → GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℕ → ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          (∀ n, 0 < a₀ n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) (a₀ n) x ∧
            -3 / a₀ n ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Q n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, T₀ n ≤ c n * (aSeed n : ℝ)) ∧
          (∀ n, c n * Q n < R n) ∧
          (∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' →
        (∃ (i : Fin (Ho n).eventCount) (hi : T₀ n ≤ (Ho n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (Ho n).toHistory i.succ j'.castSucc hl yG')
        (b : ((Ho n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (c n * ((recordsK n i hi).static b).neck.scale)⁻¹) →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) ∧
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
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestS : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
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
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.LargerBallCanonicalLateSupply_C11E F ε C1 C2 := by
  obtain ⟨epsW, hepsW, hB⟩ := canonicalLateCore_of_normalizedS_hclos_P6X3.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall' hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall' hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1 C2 Ctime} hC1 hC2 hCt => ?_⟩
  intro P g F q hanti hcan hder hgap hrest
  exact GC.LongTime.Ch11.s15_of_canonicalLateCore_P6X
    (hB' hC1 hC2 hCt hanti hcan hder hgap hrest)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
