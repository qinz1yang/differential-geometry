import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalRequests
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleBirthStagePropagation

/-!
# S-CH11-FIX12 patched-at-path `PreparedSpatialBirthQueryBase`

来源：donor `PreparedSpatialBirthQueryBase.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）。patched-at-path：下游
`PreparedSpatialPositivePoleWeightedPropagation` 对它做
`open private birth_first_stage_of_fixed_saved_data … from` 原路径（原路径文本 = 本文件）：
* 裸名 `normalizedDatum`（`DifferentialGeometry.Geometry.Neck`）与 `SpatialCanonicalWitness`
  （`…Perelman.CanonicalNeighborhood.FiniteHorn`）在本树 unknown identifier（`open` 不传递）→ 补两行
  `open`；
* `hReserve` 里 `rw [← hbirth]`：目标里的时间是 `(F.tower.history n).time poleEvent.succ`，`hbirth`
  讲 let 变量 `H.time poleEvent.succ`，`rw` 句法上找不到 → 先在 `H.time` 形上证 `hmem` 再
  `exact hmem`（defeq；同 `PreparedSpatialBirthPhysicalRequests`）；
* 陈述里只出现、证明不引用的 binder 加 `_`（unusedVariables）。

-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Manifold DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace GC.GeneralFlow
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- The actual selected raw cap family pays the first incoming stage using the two
weak reserve inequalities of the fixed-flow propagation query. -/
private theorem birth_first_stage_of_fixed_saved_data
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (constants : ClosedBirthConstants) (pBase : CutoffParameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hRequest : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2)
    (hWindow : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ pBase.recenterConstant →
      parameters.delta (H.time i.succ) ≤ req.2.2.2 →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ req.2.2.2) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ (StandardCap.transitionEnd + 10)}
      )
    (hSupport :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ pBase.recenterConstant →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0
    )
    (S : PreparedSpatialChain pBase constants P g)
    (radii : ℕ → ℝ)
    (hRadiiPos : ∀ n : ℕ, 0 < radii n)
    (hRadiiNext : ∀ n : ℕ, (S.state (n + 1)).radius = radii n) :
    let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).1
    let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.1
    let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.2.1
    ∀ W : ∀ n : ℕ, PreparedSpatialStepRetention
      (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
      (εcut n) (Dcut n) (mcut n),
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q)
      (block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ),
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      q.recenterConstant ≤ pBase.recenterConstant →
      (∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount),
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift
        ∀ T : ℝ, T ∈ Icc s (2 * s) → (S.state (m + 1)).radius ≤ q.neckRadius T) →
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        let m := block n j;
        m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)
      ) →
      (
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier)
        (r A v rhoTest : ℝ),
        0 < r → 1 ≤ A → 0 ≤ v → v ^ 2 ≤ r ^ 2 / 2 → 2 * r ^ 2 < t.val →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest →
      ∀ (first : Fin (H.eventCount + 1)) (_hle : first ≤ H.activeStage t),
        t.val - v ^ 2 ∈ H.stageDomain first →
      let nodeA : Fin H.eventCount → ℝ := fun i =>
        preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ (block n i)) *
          Real.sqrt (2 * (3 : ℝ) ^ (block n i))
      let nodeE : Fin H.eventCount → ℝ := fun i => Real.sqrt ((3 : ℝ) ^ (block n i))
      let nodeR : Fin H.eventCount → ℝ := fun i => radii (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (radii (block n i) ^ 2)⁻¹
      let nodeRho : Fin H.eventCount → ℝ := fun _ => 1
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.succ) (_hl : i.succ ≤ H.activeStage t)
        (_hstart : t.val - v ^ 2 ≤ H.time i.succ),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        q.delta (H.time i.succ) ≤ req.2.2.2 ∧
        q.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records n j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i
      ) →
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
          H.isParabolicallyRmControlledBall t p r →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ r →
        q.neckRadius t.val / 100 ≤ rhoTest →
        (∀ s ∈ Icc (t.val / 2) t.val,
          q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
        seedTrace.isRmControlled (hat := hSeedTime) r →
      riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x <
        ENNReal.ofReal (A * r) →
      ∀ (poleEvent : Fin H.eventCount), H.activeStage t = poleEvent.succ →
        t.val = H.time poleEvent.succ →
      ∀ b : ℝ, 0 < b → b ^ 2 ≤ r ^ 2 / 2 →
        H.time poleEvent.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ioc (0 : ℝ) b,
        M w ≠ ⊤ ∧ 0 ≤ m w ∧
        m w ≤ 2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r)) ∧
      AntitoneOn f (Ioc (0 : ℝ) b) ∧
      (∀ w ∈ Ioc (0 : ℝ) b, f w ≤ 2 * r) ∧
      Tendsto (fun w : ℝ => m w / w) (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
  classical
  intro εcut Dcut mcut W F q records block hInitialData hrecenter hRadiusForward hRaw hPhysical
    n H t p x r A rhoTest hr hA hT hseed htest hSeedScale hTest
    hAccuracy aSeed hSeedTime hSeedClock seedTrace _htrace hdist
    poleEvent hactive hbirth b hb hhalf hage Cweight M mvalue f
  let m := block n poleEvent
  let Aact := preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) *
    Real.sqrt (2 * (3 : ℝ) ^ m)
  let E := Real.sqrt ((3 : ℝ) ^ m)
  let rTerm := radii m / 100
  let qDeriv := (radii m ^ 2)⁻¹
  have hle : poleEvent.castSucc ≤ H.activeStage t :=
    poleEvent.castSucc_le_succ.trans hactive.symm.le
  have hpast : t.val - b ^ 2 ∈ H.stageDomain poleEvent.castSucc := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico]
    refine ⟨hage.le, ?_⟩
    rw [← hbirth]
    exact sub_lt_self _ (sq_pos_of_pos hb)
  have hstart : t.val - b ^ 2 ≤ H.time poleEvent.succ := by
    rw [← hbirth]
    exact sub_le_self _ (sq_nonneg b)
  have hPhysicalAt := hPhysical n t x r A b rhoTest hr hA hb.le hhalf hT
    hAccuracy htest hTest poleEvent.castSucc hle hpast
  obtain ⟨hE, hrTerm, hqDeriv, hRadiusCap, hbE, hPoleTest, hdelta, hRadius,
    _hLater, _hDerivative, _hIndividualCaps⟩ :=
    hPhysicalAt.1 poleEvent poleEvent.castSucc_le_succ hactive.symm.le hstart
  have hfit : preparedSpatialPhysicalActionFactor A * r ≤ Aact :=
    hPhysicalAt.2 poleEvent poleEvent.castSucc_le_succ hactive.symm.le hstart
  obtain ⟨_hmn, i, _hCountLo, _hCountHi, _hIndex, hBirth, _hBirthBand,
    _hPresentation, _hDelta, hRawRadius, hRawOrder, hRawAccuracy, hCap⟩ :=
    hRaw n poleEvent
  have hEntry := hRadiusForward m i
  dsimp only at hEntry
  rw [← hBirth] at hEntry
  have hReserve : radii m ≤ q.neckRadius t.val := by
    rw [← hRadiiNext m]
    apply hEntry t.val
    have hmem : (t : ℝ) ∈ Icc (H.time poleEvent.succ) (2 * H.time poleEvent.succ) := by
      rw [← hbirth]
      exact ⟨le_rfl, by linarith only [t.property.1]⟩
    exact hmem
  have hrTermLe : rTerm ≤ r :=
    (div_le_div_of_nonneg_right hReserve (by norm_num)).trans hSeedScale
  have hRequestedAt : preparedSpatialPhysicalQualityRequest request m (radii m) =
      request Aact E rTerm qDeriv 1 := by
    rw [preparedSpatialPhysicalQualityRequest, ite_eq_left (hRadiiPos m)]
  have hReq : εcut m = (request Aact E rTerm qDeriv 1).1 ∧
      Dcut m = (request Aact E rTerm qDeriv 1).2.1 ∧
      mcut m = (request Aact E rTerm qDeriv 1).2.2.1 :=
    ⟨congrArg Prod.fst hRequestedAt, congrArg (fun z => z.2.1) hRequestedAt,
      congrArg (fun z => z.2.2.1) hRequestedAt⟩
  have hCaps : ∀ z : (H.event poleEvent).RetainedBoundaryIndex,
      ∃ raw : (H.event poleEvent).PresentedStaticCap q.fixed
          (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
          (W m).fineParameters.modelAccuracy z,
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((records n poleEvent).static z).neck.scale := by
    intro z
    obtain ⟨_zNative, raw, _hLabel, hCanonical, _hDelta, _hOrder, _hNeck, _hWitness,
      _hOutput, _hMetric, _hInclusion, _hCap, _hRetained, _hCollapse,
      _hWindowMetric, _hWindowPoints, hScale, _hRemaining⟩ := hCap z
    exact ⟨raw, hCanonical, hScale⟩
  choose caps hcanonical hscale using hCaps
  obtain ⟨_hfSeed, hStage⟩ :=
    ObservedHistory.distinct_pole_birth_minimum_receives_first_incoming_stage
      a₀ pBase.recenterConstant constants.Ctime ha₀ request hRequest hWindow hSupport
      H q (records n) hrecenter (hInitialData n).1 (hInitialData n).2
      t p x r A hr hA hT hseed hdist aSeed hSeedTime hSeedClock seedTrace
      poleEvent hactive hbirth b Aact E rTerm qDeriv 1 hb hhalf hage
      hE hrTerm hqDeriv hRadiusCap hbE hrTermLe hPoleTest hfit hdelta hRadius caps
      (hReq.2.1.symm.le.trans hRawRadius) (hReq.2.2.symm.le.trans hRawOrder)
      (hRawAccuracy.trans hReq.1.le) hcanonical hscale
  exact ⟨hStage.1, hStage.2.1, hStage.2.2.1, hStage.2.2.2.1, hStage.2.2.2.2.1⟩

end GC.GeneralFlow
