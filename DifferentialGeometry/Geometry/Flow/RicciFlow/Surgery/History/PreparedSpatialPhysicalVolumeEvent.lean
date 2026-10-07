import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBirthVolumeOrReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalVolumeOrReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SmallTestLargeReserveVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialClosedEventRestart

/-!
# S-CH11-FIX11 patched-at-path `PreparedSpatialPhysicalVolumeEvent`

来源：donor `PreparedSpatialPhysicalVolumeEvent.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；下游模块对本路径 `open private … from`，
所以修补文本就放在原路径（patched-at-path）。只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 陈述里 `SpatialCanonicalWitness`（l.312/1209）、`normalizedDatum`（l.424/497/1321/1394）
  unknown identifier（statement 级；`autoImplicit false`）→ header 补
  `open DifferentialGeometry.Geometry.Neck` 与
  `open …Perelman.CanonicalNeighborhood.FiniteHorn`（同 FIX12 / FIX11 G8 对
  `PreparedSpatialPhysicalVolumeOrReserve` / `PreparedSpatialBirthVolumeOrReserve` 补的那批）；
* `open private GC.GeneralFlow.closed_pole_volume_or_reserve_with_saved_window_scale_bound from
  …PreparedSpatialBirthVolumeOrReserve` 的 `GC.GeneralFlow.` 前缀在本树不生效 → 去前缀；
* `S.exists_query_activation_class …` 点记号：它是 `PreparedSpatialQueryReserve` 里
  `namespace PreparedSpatialChain` 的 private 定理，`open private … from` 只开放全名 →
  `PreparedSpatialChain.exists_query_activation_class S …`（同 G4 / G5）；
* `hObservation` 里 `unfold ObservationTower.observe; rw [Nat.ceil_natCast]; rfl`：motive 不
  type correct（`atIndex _a ↑n ⋯ ⋯` 的证明项依赖 `_a`）→
  `simp only [ObservationTower.observe, Nat.ceil_natCast]; rfl`（同 FIX12 / G8）；
* **heartbeat 例外（lead 预裁：{300000, 400000, 600000} 取实测最小通过值，≤ 600000）**：
  两条声明各约 900 / 720 行，陈述不可拆（donor 陈述原样），逐声明加
  `set_option maxHeartbeats N in`（不整文件），注释置于 docstring 之前。实测（同一份修补文本，
  只改值）：两条声明在 300000 与 400000 均超限（`whnf` / `isDefEq` timeout），两条同为
  600000 通过 → 两处都取 600000；
* 12 个陈述 / 中间 binder（`hf` / `hl` / `hle` / `hstart`）不被引用 → 加 `_` 前缀。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
namespace GC.GeneralFlow
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

open private closed_event_weighted_restart_of_fixed_saved_data from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialClosedEventRestart
open private PreparedSpatialChain.exists_query_activation_class from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQueryReserve
open private restricted_small_parabolic_curvature from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalVolumeOrReserve
open private cast_point cast_point_heq ball_mem_iff_of_metric_heq
  ball_volume_eq_of_metric_heq lift_restricted_time restricted_controlled_ball from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic

open private closed_pole_volume_or_reserve_with_saved_window_scale_bound from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBirthVolumeOrReserve

set_option maxHeartbeats 600000 in
-- heartbeat exception 600000 (measured 300000/400000 fail, 600000 pass), lead 04:5x
/-- One original surgery carries the two volume branches and its saved positive-event restart. -/
theorem exists_surgery_with_same_flow_volume_or_reserve_and_positive_event_restart_with_closed_support_and_window_scale_bound
    (Dstar : ℝ) (hDstar : StandardCap.transitionEnd < Dstar) :
    ∃ εcap cBG : ℝ, 0 < εcap ∧ 0 < cBG ∧
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ constants : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∃ cMax : ℝ, 0 < cMax ∧
    ∃ κVol : ℝ → ℝ, (∀ A : ℝ, 0 < A → 0 < κVol A) ∧
    ∃ cSpatial : ℝ, 0 < cSpatial ∧
    ∃ κLarge : ℝ → ℝ, (∀ A : ℝ, 0 < A → 0 < κLarge A) ∧
    let cMargin : ℝ := min cMax cSpatial
    let κAll : ℝ → ℝ := fun A => min (κVol A) (κLarge A)
    0 < cMargin ∧ cMargin ≤ cMax ∧ cMargin ≤ cSpatial ∧
    (∀ A : ℝ, 0 < A → 0 < κAll A) ∧
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase constants P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMargin ∧
      base.prepared.HasReserveQuality Dstar εcap ∧
      base.DistanceData Cdist ∧
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2) ∧
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        req.1 ≤ (E + 1)⁻¹ ∧ E ≤ req.2.1 ∧ E ≤ (req.2.2.1 : ℝ)) ∧
      (∀ (Aact Ebound rTerm qDeriv ρ : ℝ),
    0 ≤ Ebound → 0 < rTerm → 0 < qDeriv → 0 < ρ →
  let req := request Aact Ebound rTerm qDeriv ρ
  ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (event : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {Dbig ζ : ℝ} {m : ℕ},
    req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 →
    ∀ {b : event.RetainedBoundaryIndex}
      (raw : event.PresentedStaticCap fixed Dbig m ζ b), raw.hasCanonicalWindow →
      ∀ x : standardCapWindow Dbig, ‖x.val‖ < Dbig → ∀ ell : ℝ,
        ell ^ 4 * normSq0S event.outputMetric (raw.window x) 4
          (metricRm04At event.outputMetric (raw.window x)) ≤ 1 →
        raw.neck.scale * ell ^ 2 ≤ 18) ∧
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
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
      ) ∧
    (
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
    ) ∧
    let policy : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase constants P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase constants
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ :=
      fun n _ _ rNext => preparedSpatialPhysicalQualityRequest request n rNext
    ∃ (S : PreparedSpatialChain pBase constants P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase constants
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (rNext : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εcap) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εcap) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMargin) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < rNext n ∧ (S.state (n + 1)).radius = rNext n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (policy n (S.state n) (future n) (rNext n)).2.2.2) ∧
    let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).1
    let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.1
    let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.2.1
    ∃ W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n),
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      (
      (
      (
      (
      F.tower = S.tower ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
        ((F.tower.history n).toHistory.event i).HasUniformDistanceScalar Cdist) ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          constants.epsilon (max constants.C1s constants.Cbirth) (max constants.C2s (max constants.Cbirth (constants.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart constants.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) constants.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t
      ) ∧
      (∀ t : ℝ, 0 ≤ t →
        q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t ∧
        q.neckRadius t =
          (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) ∧
      (∀ t : ℝ, 0 < t → q.delta t < S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) ∧
      (∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift;
        s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        q.delta s = S.accuracy m ∧
        (∀ u : ℝ, s ≤ u → q.delta u ≤ S.accuracy m) ∧
        (∀ T : ℝ, T ∈ Icc s (2 * s) →
          (S.state (m + 1)).radius ≤ q.neckRadius T) ∧
        (∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
          A < 12 * (3 : ℝ) ^ m) ∧
        ∀ n : ℕ, s ≤ (n : ℝ) →
        ∃ j : Fin (F.tower.history n).eventCount,
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ = s ∧
          HEq (records n j).nominalRadius ((W m).fineRecords i).nominalRadius ∧
          HEq (records n j).delta ((W m).fineRecords i).delta ∧
          HEq (records n j).order ((W m).fineRecords i).order ∧
          HEq (records n j).neck ((W m).fineRecords i).neck ∧
          HEq (records n j).static
            (fun z => translate_presented_static_cap
              ((S.state (m + 1)).native.coreEvent i) (S.state (m + 1)).shift
              ((((W m).fineRecords i).restrictModelWindow ((W m).fineWindows i)
                (S.state m).parameters.modelRadius_pos
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))) ∧
      (∀ (m n : ℕ) (j : Fin ((F.tower.history n).eventCount + 1)),
        (S.state (m + 1)).offset ≤ j.val →
        ∀ (y : ((F.tower.history n).stage j).Carrier) (s : ℝ),
          s ∈ Ioo ((F.tower.history n).time j)
            ((F.tower.history n).toHistory.stageEndTime j) →
          s < (3 : ℝ) ^ (m + 1) →
          ((S.state (m + 1)).radius ^ 2)⁻¹ <
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun u =>
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
      ) ∧
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        ∃ m : ℕ, m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
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
                  raw.window x = raw.inclusion (raw.witness.cap z))
      ) ∧
      ∃ block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ,
        (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
          block n j ≤ n ∧
          ∃ i : Fin (S.state (block n j + 1)).native.eventCount,
            j.val = ((S.state (block n j + 1)).affine.eventIndex i).val ∧
            (F.tower.history n).time j.succ =
              (S.state (block n j + 1)).native.time i.succ + (S.state (block n j + 1)).shift ∧
            (F.tower.history n).time j.succ ∈
              Ioc (preparedSpatialHorizon (block n j)) ((3 : ℝ) ^ (block n j))) ∧
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
      ) ∧
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
      let nodeR : Fin H.eventCount → ℝ := fun i => rNext (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (rNext (block n i) ^ 2)⁻¹
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
      ) ∧
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.time (H.activeStage t) < t.val →
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
      ∀ (a k b : ℝ), 0 < a → a < k → k < b → b ^ 2 ≤ r ^ 2 / 2 →
      ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t),
        t.val - k ^ 2 = H.time i.succ →
        t.val - a ^ 2 < H.stageEndTime i.succ →
        H.time i.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let Dweight := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ico a k,
        M w ≤ ((2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) : WithTop ℝ)) →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      let Opost := seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl
      ∃ (qEnd : (H.stage i.succ).Carrier) (L mEvent : ℝ),
        M k = (mEvent : WithTop ℝ) ∧
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd =
          (mEvent : WithTop ℝ) ∧
        (∀ y : (H.stage i.succ).Carrier,
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd ≤
            H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost y) ∧
        H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x qEnd =
          (L : WithTop ℝ) ∧
        riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) Opost qEnd <
          ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
        r / 4 ≤ L + r ∧ 0 < mEvent ∧
        mEvent ≤ 2 * r * k * Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) ∧
        L ≤ (Dweight - 1) * r ∧
      ∃ gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x ∧
        gamma ⟨i.succ, le_rfl, hl⟩ k = qEnd ∧
        (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
          (hj : j.succ ≤ H.activeStage t),
          ∃ z : (H.event j).old,
            z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
              (Real.sqrt (t.val - H.time j.succ)) ∧
            (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
              (Real.sqrt (t.val - H.time j.succ))) ∧
        (∑ j : H.StageInterval i.succ (H.activeStage t),
          H.stageRegularizedAction j.val t.val (gamma j)
            (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L ∧
        H.regularizedExtendedAction i.succ (H.activeStage t) t.val (3 / a₀) 0 k gamma =
          (L : WithTop ℝ) ∧
      let blockIndex := block n i
      let Dcap := (W blockIndex).fineParameters.modelRadius
      let ncap := (W blockIndex).fineParameters.modelOrder
      let εcap := (W blockIndex).fineParameters.modelAccuracy
      ∃ nativeIndex : Fin (S.state (blockIndex + 1)).native.eventCount,
        i.val = ((S.state (blockIndex + 1)).affine.eventIndex nativeIndex).val ∧
        H.time i.succ = (S.state (blockIndex + 1)).native.time nativeIndex.succ +
          (S.state (blockIndex + 1)).shift ∧
      ∃ caps : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap q.fixed Dcap ncap εcap c,
        (∀ c, (caps c).hasCanonicalWindow) ∧
        εcap ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < Dcap ∧
        (∀ c, (caps c).neck.scale = ((records n i).static c).neck.scale) ∧
        (∀ c, ∃ cNative : ((S.state (blockIndex + 1)).native.toHistory.event nativeIndex).RetainedBoundaryIndex,
          HEq cNative c ∧
          HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static cNative).neck ∧
          HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static cNative).witness ∧
          HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static cNative).inclusion ∧
          (caps c).witness.windowMetric = (((W blockIndex).fineRecords nativeIndex).static cNative).witness.windowMetric ∧
          (∀ z : standardCapWindow Dcap,
            HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static cNative).window z)) ∧
          (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
            ((records n i).static c).inclusion (((records n i).static c).witness.cap z))) ∧
      ∃ O z : (H.event i).old,
        O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
        (H.event i).oldOutput O = Opost ∧
        (H.event i).oldOutput z = qEnd ∧
        (∀ c, (H.event i).oldOutput O ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        (∀ c, (H.event i).oldOutput z ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        M k ≠ ⊤ ∧ 0 < m k ∧ f k ≤ 2 * r ∧
        UpperSemicontinuousWithinAt f (Ici k) k ∧
        (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
        AntitoneOn f (Icc k b) ∧
        (∀ w ∈ Icc k b,
          m w ≤ Real.exp (Cweight * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) *
            (w / k) * m k ∧
          m w ≤ 2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r))
      ) ∧
      (∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (T : Icc (0 : ℝ) H.horizon) {r : ℝ},
          0 < r → 2 * r ^ 2 < (T : ℝ) → q.neckRadius T / 100 < r →
        let σ := q.neckRadius T
        ∃ j : ℕ,
          (S.state j).prepared.HasReserveQuality Dstar εcap ∧
          σ = (S.state j).radius ∧
          (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
            ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
              T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
          (S.state j).shift < T - (σ / 100) ^ 2 ∧
          T < (3 : ℝ) ^ j ∧
          0 < σ / 100 ∧
          σ / 100 ≤ cMargin / Real.sqrt (S.state j).prepared.Qall ∧
          (let M := (S.state j).prepared.Qall
           let c := (σ / 100) * Real.sqrt M
           1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
           (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
           (S.state j).prepared.Qzero ≤ M ∧
           0 < c ∧ c ≤ cMargin ∧ σ / 100 = c / Real.sqrt M ∧
           c ^ 2 / M < T - (S.state j).shift) ∧
          ∀ (A : ℝ), 0 < A →
          ∀ (p x : (H.stageAt T).Carrier),
            GC.LongTime.hasSmallParabolicCurvature H T p r →
            ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) p r) →
            x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r) →
          ∀ ρ : ℝ, ρ < r → H.isParabolicallyRmControlledBall T x ρ →
            ENNReal.ofReal (κVol A * ρ ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ) ∨
            ∃ ρ' : ℝ, σ / 100 ≤ ρ' ∧ ρ' < r ∧ ρ ≤ ρ' ∧
              H.isParabolicallyRmControlledBall T x ρ' ∧
              ENNReal.ofReal (cBG * (ρ / ρ') ^ 3) *
                  riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                    (H.stageMetric (H.activeStage T) T)
                    (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ') ≤
                riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                  (H.stageMetric (H.activeStage T) T)
                  (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ)) ∧
      (∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (T : Icc (0 : ℝ) H.horizon) {r : ℝ},
          0 < r → 2 * r ^ 2 < (T : ℝ) →
        let σ := q.neckRadius T
        ∃ j : ℕ,
          (S.state j).prepared.HasReserveQuality Dstar εcap ∧
          σ = (S.state j).radius ∧
          (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
            ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
              T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
          (S.state j).shift < T ∧
          T < (3 : ℝ) ^ j ∧
          0 < σ / 100 ∧
          σ / 100 ≤ cMargin / Real.sqrt (S.state j).prepared.Qall ∧
          (let M := (S.state j).prepared.Qall
           let c := (σ / 100) * Real.sqrt M
           1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
           (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
           (S.state j).prepared.Qzero ≤ M ∧
           0 < c ∧ c ≤ cMargin ∧ σ / 100 = c / Real.sqrt M) ∧
          ∀ (A : ℝ), 0 < A →
          ∀ (p x : (H.stageAt T).Carrier),
            GC.LongTime.hasSmallParabolicCurvature H T p r →
            ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) p r) →
            x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r) →
          ∀ ρ : ℝ, ρ < r → H.isParabolicallyRmControlledBall T x ρ →
            ENNReal.ofReal (κAll A * ρ ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ) ∨
            ∃ ρ' : ℝ, σ / 100 ≤ ρ' ∧ ρ' < r ∧ ρ ≤ ρ' ∧
              H.isParabolicallyRmControlledBall T x ρ' ∧
              ENNReal.ofReal (cBG * (ρ / ρ') ^ 3) *
                  riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                    (H.stageMetric (H.activeStage T) T)
                    (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ') ≤
                riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                  (H.stageMetric (H.activeStage T) T)
                  (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ)) := by
  classical
  obtain ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, makeInitial⟩ :=
    closed_pole_volume_or_reserve_with_saved_window_scale_bound.{u} Dstar hDstar
  refine ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, hκVol, makeAtMargin⟩ :=
    makeInitial P g
  obtain ⟨cSpatial, hcSpatial, makeLarge⟩ :=
    exists_test_volume_in_same_observation_of_large_reserve P g constants
  choose κLargeOf hκLargeOf largeOf using
    (fun A : Ioi (0 : ℝ) => makeLarge A A.2)
  let κLarge : ℝ → ℝ := fun A => if hA : 0 < A then κLargeOf ⟨A, hA⟩ else 1
  have hκLarge : ∀ A : ℝ, 0 < A → 0 < κLarge A := by
    intro A hA
    simpa only [κLarge, dite_eq_left hA] using hκLargeOf ⟨A, hA⟩
  let cMargin : ℝ := min cMax cSpatial
  let κAll : ℝ → ℝ := fun A => min (κVol A) (κLarge A)
  have hcMargin : 0 < cMargin := lt_min hcMax hcSpatial
  have hMarginMax : cMargin ≤ cMax := min_le_left _ _
  have hMarginSpatial : cMargin ≤ cSpatial := min_le_right _ _
  have hκAll : ∀ A : ℝ, 0 < A → 0 < κAll A := by
    intro A hA
    exact lt_min (hκVol A hA) (hκLarge A hA)
  refine ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, hκVol, cSpatial, hcSpatial,
    κLarge, hκLarge, hcMargin, hMarginMax, hMarginSpatial, hκAll, ?_⟩
  obtain ⟨pBase, base, hBaseHistory, hBaseInitial, hBaseShift, hBaseOffset,
      hBaseRadius, hBaseConstant, hBaseFit, hBaseQuality, hBaseDistance,
      request, hRequest, hCof, hWindowScale, hWindow, hSupport, hChain⟩ :=
    makeAtMargin cMargin hcMargin hMarginMax
  refine ⟨pBase, base, hBaseHistory, hBaseInitial, hBaseShift, hBaseOffset,
    hBaseRadius, hBaseConstant, hBaseFit, hBaseQuality, hBaseDistance,
    request, hRequest, hCof, hWindowScale, hWindow, hSupport, ?_⟩
  obtain ⟨S, future, rNext, hFutureQuality, hStateQuality, hZero, hAllFit,
      hDistance, hState, hQuarter, hRequested, W, F, q, κ, records, hSaved, _hBirthStage⟩ :=
    hChain
  obtain ⟨hOld, hSmallQuery⟩ := hSaved
  obtain ⟨hQualityRaw, block, hBlock, hRaw, hPhysical⟩ := hOld
  have hEvent := closed_event_weighted_restart_of_fixed_saved_data
    P g constants pBase a₀ ha₀ request hRequest hWindow
    (by
      intro H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
        aSeed hSeedTime hSeedClock seedTrace _C _D a has hat v hv hhalf hclock _hpole
      exact hSupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
        aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock)
    S rNext
    (fun n => (hState n).1) (fun n => (hState n).2.1) W F q records block
    (fun n => hQualityRaw.1.2.2.2.1 n)
    hQualityRaw.1.1.2.2.1.2.2.2.2.le
    (fun m i => (hQualityRaw.1.2.2.2.2.1 m i).2.2.2.1)
    hRaw hPhysical
  refine ⟨S, future, rNext, hFutureQuality, hStateQuality, hZero, hAllFit,
    hDistance, hState, hQuarter, hRequested, W, F, q, κ, records,
    ⟨hQualityRaw, block, hBlock, hRaw, hPhysical, hEvent⟩, hSmallQuery, ?_⟩
  have hTower : F.tower = S.tower := hQualityRaw.1.1.1
  have hDiagonal := hQualityRaw.1.2.1
  have hshift0 : (S.state 0).shift = 0 := by
    rw [hZero]
    exact hBaseShift
  have hradius0 : ∀ s : ℝ,
      (S.state 0).parameters.neckRadius s = (S.state 0).radius := by
    rw [hZero]
    exact hBaseConstant
  have hshift (n : ℕ) : (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount) :=
    (hState n).2.2.2.1
  have hoffset (n : ℕ) : (S.state (n + 1)).offset = (S.state n).history.eventCount :=
    (hState n).2.2.2.2.1
  intro n H T r hr hTime σ
  by_cases hsmall : σ / 100 < r
  · obtain ⟨j, hQualityj, hσj, hBand, hWindowj, hCapacity, hb, hBound,
        hNumbers, hTest⟩ := hSmallQuery n T hr hTime hsmall
    have hshiftT : (S.state j).shift < (T : ℝ) :=
      hWindowj.trans_le (sub_le_self _ (sq_nonneg (σ / 100)))
    obtain ⟨hone, hcan, hspatial, hbirth, hzero, hc, hc_le, hceq, _⟩ := hNumbers
    refine ⟨j, hQualityj, hσj, hBand, hshiftT, hCapacity, hb, hBound,
      ⟨hone, hcan, hspatial, hbirth, hzero, hc, hc_le, hceq⟩, ?_⟩
    intro A hA p x hseed hseedVolume hx ρ hρr htest
    rcases hTest A hA p x hseed hseedVolume hx ρ hρr htest with hvolume | hreserve
    · left
      have hcoef : κAll A ≤ κVol A := min_le_left _ _
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcoef (pow_nonneg htest.1.le 3))).trans hvolume
    · exact Or.inr hreserve
  · have hlarge : r ≤ σ / 100 := le_of_not_gt hsmall
    have hTpos : 0 < (T : ℝ) := by nlinarith [sq_nonneg r]
    have hRadiusDiagonal : q.neckRadius T =
        (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T :=
      (hDiagonal T T.2.1).2
    obtain ⟨j, hσj, hBand, hshiftHalf, hCapacity⟩ :=
      PreparedSpatialChain.exists_query_activation_class S hshift0 hradius0 hshift hTpos
    rw [← hRadiusDiagonal] at hσj
    change σ = (S.state j).radius at hσj
    have hshiftT : (S.state j).shift < (T : ℝ) :=
      hshiftHalf.trans (by linarith)
    have hb : 0 < σ / 100 := div_pos (q.neckRadius_pos T T.2.1) (by norm_num)
    let M := (S.state j).prepared.Qall
    let c := (σ / 100) * Real.sqrt M
    have hM : 0 < M := (S.state j).prepared.Qall_pos
    have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    have hfitj : σ * Real.sqrt M ≤ 100 * cMargin := by
      rw [hσj]
      exact hAllFit j
    have hc : 0 < c := mul_pos hb hsqrt
    have hc_le : c ≤ cMargin := by
      dsimp only [c]
      nlinarith [hcMargin]
    have hBound : σ / 100 ≤ cMargin / Real.sqrt M :=
      (le_div_iff₀ hsqrt).mpr hc_le
    have hceq : σ / 100 = c / Real.sqrt M := by
      apply (eq_div_iff (ne_of_gt hsqrt)).mpr
      rfl
    have hbirth : (S.state j).prepared.Qbirth ≤ M := by
      dsimp only [M]
      rw [(S.state j).prepared.Qall_eq]
      exact le_max_left _ _
    have hzero : (S.state j).prepared.Qzero ≤ M := by
      dsimp only [M]
      rw [(S.state j).prepared.Qall_eq]
      exact le_max_right _ _
    have hcanonical : max 1 (max (S.state j).prepared.qcan (S.state j).prepared.qs) ≤ M :=
      (S.state j).prepared.Qbirth_ge.trans hbirth
    have hone : 1 ≤ M := (le_max_left _ _).trans hcanonical
    have hcan : (S.state j).prepared.qcan ≤ M :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hcanonical)
    have hspatial : (S.state j).prepared.qs ≤ M :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hcanonical)
    refine ⟨j, hStateQuality j, hσj, hBand, hshiftT, hCapacity, hb, hBound,
      ⟨hone, hcan, hspatial, hbirth, hzero, hc, hc_le, hceq⟩, ?_⟩
    have hshift_nonneg : 0 ≤ (S.state j).shift := (S.state j).affine.shift_nonneg
    have hτpos : 0 < (T : ℝ) - (S.state j).shift := sub_pos.mpr hshiftT
    have hτtop : (T : ℝ) - (S.state j).shift < (W j).oldNative.horizon := by
      rw [(W j).oldNative_horizon]
      exact sub_lt_sub_right hCapacity _
    let τ : Icc (0 : ℝ) (W j).oldNative.horizon :=
      ⟨(T : ℝ) - (S.state j).shift, hτpos.le, hτtop.le⟩
    have hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift := by
      dsimp only [τ]
      ring
    have hfitSpatial : (S.state j).radius * Real.sqrt (S.state j).prepared.Qall ≤
        100 * cSpatial :=
      (hAllFit j).trans (mul_le_mul_of_nonneg_left hMarginSpatial (by norm_num))
    have hHorizon : H.horizon = (n : ℝ) := F.tower.horizon_eq n
    let u : Icc (0 : ℝ) H.horizon :=
      ⟨(n : ℝ), Nat.cast_nonneg n, hHorizon.ge⟩
    have hObservation : F.observation.observe (n : ℝ) (Nat.cast_nonneg n) = H.restrict u := by
      simp only [ObservationTower.observe, Nat.ceil_natCast]
      rfl
    let tR : Icc (0 : ℝ) (H.restrict u).horizon :=
      ⟨(T : ℝ), T.2.1, by change (T : ℝ) ≤ (n : ℝ); rw [← hHorizon]; exact T.2.2⟩
    have hstage : (H.restrict u).stageAt tR = H.stageAt T := H.restrict_stageAt u tR
    have hmetric : HEq
        ((H.restrict u).stageMetric ((H.restrict u).activeStage tR) tR)
        (H.stageMetric (H.activeStage T) T) := H.restrict_sliceMetric u tR
    intro A hA p x hseed hseedVolume hx ρ hρr htest
    let pR := cast_point hstage.symm p
    let xR := cast_point hstage.symm x
    have hpR : HEq pR p := cast_point_heq hstage.symm p
    have hxR : HEq xR x := cast_point_heq hstage.symm x
    have hseedR : GC.LongTime.hasSmallParabolicCurvature (H.restrict u) tR pR r :=
      restricted_small_parabolic_curvature H u tR pR p hpR hseed
    have htestR : (H.restrict u).isParabolicallyRmControlledBall tR xR ρ :=
      restricted_controlled_ball H u tR xR x hxR htest
    have hVolumeSeed := ball_volume_eq_of_metric_heq hstage
      ((H.restrict u).stageMetric ((H.restrict u).activeStage tR) tR)
      (H.stageMetric (H.activeStage T) T) hmetric hpR r
    have hVolumeX (s : ℝ) := ball_volume_eq_of_metric_heq hstage
      ((H.restrict u).stageMetric ((H.restrict u).activeStage tR) tR)
      (H.stageMetric (H.activeStage T) T) hmetric hxR s
    have hxRestricted : xR ∈ riemannianBallOf
        ((H.restrict u).stageMetric ((H.restrict u).activeStage tR) tR) pR (A * r) :=
      (ball_mem_iff_of_metric_heq hstage
        ((H.restrict u).stageMetric ((H.restrict u).activeStage tR) tR)
        (H.stageMetric (H.activeStage T) T) hmetric hpR hxR (A * r)).mpr hx
    have hreservej : r ≤ (S.state j).radius / 100 := by
      rw [← hσj]
      exact hlarge
    have hphysical := largeOf ⟨A, hA⟩ S F hTower j (W j)
      (hshift j) (hoffset j) hshift_nonneg hfitSpatial (n : ℝ) (Nat.cast_nonneg n)
    rw [hObservation] at hphysical
    have hvolume := hphysical tR τ hclock hτtop pR xR r hseedR
      (by rw [hVolumeSeed]; exact hseedVolume) hxRestricted hreservej ρ hρr htestR
    have hvolumeLarge : ENNReal.ofReal (κLarge A * ρ ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
          (H.stageMetric (H.activeStage T) T)
          (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ) := by
      simpa only [κLarge, dite_eq_left hA, hVolumeX ρ] using hvolume
    left
    have hcoef : κAll A ≤ κLarge A := min_le_right _ _
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcoef (pow_nonneg htest.1.le 3))).trans hvolumeLarge

set_option maxHeartbeats 600000 in
-- heartbeat exception 600000 (measured 300000/400000 fail, 600000 pass), lead 04:5x
theorem exists_surgery_with_same_flow_volume_or_reserve_and_positive_event_restart
    (Dstar : ℝ) (hDstar : StandardCap.transitionEnd < Dstar) :
    ∃ εcap cBG : ℝ, 0 < εcap ∧ 0 < cBG ∧
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ constants : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∃ cMax : ℝ, 0 < cMax ∧
    ∃ κVol : ℝ → ℝ, (∀ A : ℝ, 0 < A → 0 < κVol A) ∧
    ∃ cSpatial : ℝ, 0 < cSpatial ∧
    ∃ κLarge : ℝ → ℝ, (∀ A : ℝ, 0 < A → 0 < κLarge A) ∧
    let cMargin : ℝ := min cMax cSpatial
    let κAll : ℝ → ℝ := fun A => min (κVol A) (κLarge A)
    0 < cMargin ∧ cMargin ≤ cMax ∧ cMargin ≤ cSpatial ∧
    (∀ A : ℝ, 0 < A → 0 < κAll A) ∧
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase constants P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMargin ∧
      base.prepared.HasReserveQuality Dstar εcap ∧
      base.DistanceData Cdist ∧
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2) ∧
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
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
      ) ∧
    (
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
      H.time (H.activeStage t) < t.val →
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
    ) ∧
    let policy : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase constants P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase constants
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ :=
      fun n _ _ rNext => preparedSpatialPhysicalQualityRequest request n rNext
    ∃ (S : PreparedSpatialChain pBase constants P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase constants
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (rNext : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εcap) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εcap) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMargin) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < rNext n ∧ (S.state (n + 1)).radius = rNext n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (policy n (S.state n) (future n) (rNext n)).2.2.2) ∧
    let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).1
    let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.1
    let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.2.1
    ∃ W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n),
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      (
      (
      (
      (
      F.tower = S.tower ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
        ((F.tower.history n).toHistory.event i).HasUniformDistanceScalar Cdist) ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          constants.epsilon (max constants.C1s constants.Cbirth) (max constants.C2s (max constants.Cbirth (constants.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart constants.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) constants.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t
      ) ∧
      (∀ t : ℝ, 0 ≤ t →
        q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t ∧
        q.neckRadius t =
          (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) ∧
      (∀ t : ℝ, 0 < t → q.delta t < S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) ∧
      (∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift;
        s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        q.delta s = S.accuracy m ∧
        (∀ u : ℝ, s ≤ u → q.delta u ≤ S.accuracy m) ∧
        (∀ T : ℝ, T ∈ Icc s (2 * s) →
          (S.state (m + 1)).radius ≤ q.neckRadius T) ∧
        (∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
          A < 12 * (3 : ℝ) ^ m) ∧
        ∀ n : ℕ, s ≤ (n : ℝ) →
        ∃ j : Fin (F.tower.history n).eventCount,
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ = s ∧
          HEq (records n j).nominalRadius ((W m).fineRecords i).nominalRadius ∧
          HEq (records n j).delta ((W m).fineRecords i).delta ∧
          HEq (records n j).order ((W m).fineRecords i).order ∧
          HEq (records n j).neck ((W m).fineRecords i).neck ∧
          HEq (records n j).static
            (fun z => translate_presented_static_cap
              ((S.state (m + 1)).native.coreEvent i) (S.state (m + 1)).shift
              ((((W m).fineRecords i).restrictModelWindow ((W m).fineWindows i)
                (S.state m).parameters.modelRadius_pos
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))) ∧
      (∀ (m n : ℕ) (j : Fin ((F.tower.history n).eventCount + 1)),
        (S.state (m + 1)).offset ≤ j.val →
        ∀ (y : ((F.tower.history n).stage j).Carrier) (s : ℝ),
          s ∈ Ioo ((F.tower.history n).time j)
            ((F.tower.history n).toHistory.stageEndTime j) →
          s < (3 : ℝ) ^ (m + 1) →
          ((S.state (m + 1)).radius ^ 2)⁻¹ <
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun u =>
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
      ) ∧
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        ∃ m : ℕ, m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
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
                  raw.window x = raw.inclusion (raw.witness.cap z))
      ) ∧
      ∃ block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ,
        (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
          block n j ≤ n ∧
          ∃ i : Fin (S.state (block n j + 1)).native.eventCount,
            j.val = ((S.state (block n j + 1)).affine.eventIndex i).val ∧
            (F.tower.history n).time j.succ =
              (S.state (block n j + 1)).native.time i.succ + (S.state (block n j + 1)).shift ∧
            (F.tower.history n).time j.succ ∈
              Ioc (preparedSpatialHorizon (block n j)) ((3 : ℝ) ^ (block n j))) ∧
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
      ) ∧
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
      let nodeR : Fin H.eventCount → ℝ := fun i => rNext (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (rNext (block n i) ^ 2)⁻¹
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
      ) ∧
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.time (H.activeStage t) < t.val →
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
      ∀ (a k b : ℝ), 0 < a → a < k → k < b → b ^ 2 ≤ r ^ 2 / 2 →
      ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t),
        t.val - k ^ 2 = H.time i.succ →
        t.val - a ^ 2 < H.stageEndTime i.succ →
        H.time i.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let Dweight := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ico a k,
        M w ≤ ((2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) : WithTop ℝ)) →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      let Opost := seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl
      ∃ (qEnd : (H.stage i.succ).Carrier) (L mEvent : ℝ),
        M k = (mEvent : WithTop ℝ) ∧
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd =
          (mEvent : WithTop ℝ) ∧
        (∀ y : (H.stage i.succ).Carrier,
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd ≤
            H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost y) ∧
        H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x qEnd =
          (L : WithTop ℝ) ∧
        riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) Opost qEnd <
          ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
        r / 4 ≤ L + r ∧ 0 < mEvent ∧
        mEvent ≤ 2 * r * k * Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) ∧
        L ≤ (Dweight - 1) * r ∧
      ∃ gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x ∧
        gamma ⟨i.succ, le_rfl, hl⟩ k = qEnd ∧
        (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
          (hj : j.succ ≤ H.activeStage t),
          ∃ z : (H.event j).old,
            z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
              (Real.sqrt (t.val - H.time j.succ)) ∧
            (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
              (Real.sqrt (t.val - H.time j.succ))) ∧
        (∑ j : H.StageInterval i.succ (H.activeStage t),
          H.stageRegularizedAction j.val t.val (gamma j)
            (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L ∧
        H.regularizedExtendedAction i.succ (H.activeStage t) t.val (3 / a₀) 0 k gamma =
          (L : WithTop ℝ) ∧
      let blockIndex := block n i
      let Dcap := (W blockIndex).fineParameters.modelRadius
      let ncap := (W blockIndex).fineParameters.modelOrder
      let εcap := (W blockIndex).fineParameters.modelAccuracy
      ∃ nativeIndex : Fin (S.state (blockIndex + 1)).native.eventCount,
        i.val = ((S.state (blockIndex + 1)).affine.eventIndex nativeIndex).val ∧
        H.time i.succ = (S.state (blockIndex + 1)).native.time nativeIndex.succ +
          (S.state (blockIndex + 1)).shift ∧
      ∃ caps : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap q.fixed Dcap ncap εcap c,
        (∀ c, (caps c).hasCanonicalWindow) ∧
        εcap ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < Dcap ∧
        (∀ c, (caps c).neck.scale = ((records n i).static c).neck.scale) ∧
        (∀ c, ∃ cNative : ((S.state (blockIndex + 1)).native.toHistory.event nativeIndex).RetainedBoundaryIndex,
          HEq cNative c ∧
          HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static cNative).neck ∧
          HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static cNative).witness ∧
          HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static cNative).inclusion ∧
          (caps c).witness.windowMetric = (((W blockIndex).fineRecords nativeIndex).static cNative).witness.windowMetric ∧
          (∀ z : standardCapWindow Dcap,
            HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static cNative).window z)) ∧
          (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
            ((records n i).static c).inclusion (((records n i).static c).witness.cap z))) ∧
      ∃ O z : (H.event i).old,
        O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
        (H.event i).oldOutput O = Opost ∧
        (H.event i).oldOutput z = qEnd ∧
        (∀ c, (H.event i).oldOutput O ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        (∀ c, (H.event i).oldOutput z ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        M k ≠ ⊤ ∧ 0 < m k ∧ f k ≤ 2 * r ∧
        UpperSemicontinuousWithinAt f (Ici k) k ∧
        (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
        AntitoneOn f (Icc k b) ∧
        (∀ w ∈ Icc k b,
          m w ≤ Real.exp (Cweight * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r) *
            (w / k) * m k ∧
          m w ≤ 2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r))
      ) ∧
      (∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (T : Icc (0 : ℝ) H.horizon) {r : ℝ},
          0 < r → 2 * r ^ 2 < (T : ℝ) → q.neckRadius T / 100 < r →
        let σ := q.neckRadius T
        ∃ j : ℕ,
          (S.state j).prepared.HasReserveQuality Dstar εcap ∧
          σ = (S.state j).radius ∧
          (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
            ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
              T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
          (S.state j).shift < T - (σ / 100) ^ 2 ∧
          T < (3 : ℝ) ^ j ∧
          0 < σ / 100 ∧
          σ / 100 ≤ cMargin / Real.sqrt (S.state j).prepared.Qall ∧
          (let M := (S.state j).prepared.Qall
           let c := (σ / 100) * Real.sqrt M
           1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
           (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
           (S.state j).prepared.Qzero ≤ M ∧
           0 < c ∧ c ≤ cMargin ∧ σ / 100 = c / Real.sqrt M ∧
           c ^ 2 / M < T - (S.state j).shift) ∧
          ∀ (A : ℝ), 0 < A →
          ∀ (p x : (H.stageAt T).Carrier),
            GC.LongTime.hasSmallParabolicCurvature H T p r →
            ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) p r) →
            x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r) →
          ∀ ρ : ℝ, ρ < r → H.isParabolicallyRmControlledBall T x ρ →
            ENNReal.ofReal (κVol A * ρ ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ) ∨
            ∃ ρ' : ℝ, σ / 100 ≤ ρ' ∧ ρ' < r ∧ ρ ≤ ρ' ∧
              H.isParabolicallyRmControlledBall T x ρ' ∧
              ENNReal.ofReal (cBG * (ρ / ρ') ^ 3) *
                  riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                    (H.stageMetric (H.activeStage T) T)
                    (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ') ≤
                riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                  (H.stageMetric (H.activeStage T) T)
                  (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ)) ∧
      (∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (T : Icc (0 : ℝ) H.horizon) {r : ℝ},
          0 < r → 2 * r ^ 2 < (T : ℝ) →
        let σ := q.neckRadius T
        ∃ j : ℕ,
          (S.state j).prepared.HasReserveQuality Dstar εcap ∧
          σ = (S.state j).radius ∧
          (j = 0 ∧ T ≤ (5 / 6 : ℝ) ∨
            ∃ k : ℕ, j = k + 1 ∧ (5 / 6 : ℝ) * 3 ^ k < T ∧
              T ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) ∧
          (S.state j).shift < T ∧
          T < (3 : ℝ) ^ j ∧
          0 < σ / 100 ∧
          σ / 100 ≤ cMargin / Real.sqrt (S.state j).prepared.Qall ∧
          (let M := (S.state j).prepared.Qall
           let c := (σ / 100) * Real.sqrt M
           1 ≤ M ∧ (S.state j).prepared.qcan ≤ M ∧
           (S.state j).prepared.qs ≤ M ∧ (S.state j).prepared.Qbirth ≤ M ∧
           (S.state j).prepared.Qzero ≤ M ∧
           0 < c ∧ c ≤ cMargin ∧ σ / 100 = c / Real.sqrt M) ∧
          ∀ (A : ℝ), 0 < A →
          ∀ (p x : (H.stageAt T).Carrier),
            GC.LongTime.hasSmallParabolicCurvature H T p r →
            ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) p r) →
            x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r) →
          ∀ ρ : ℝ, ρ < r → H.isParabolicallyRmControlledBall T x ρ →
            ENNReal.ofReal (κAll A * ρ ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                (H.stageMetric (H.activeStage T) T)
                (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ) ∨
            ∃ ρ' : ℝ, σ / 100 ≤ ρ' ∧ ρ' < r ∧ ρ ≤ ρ' ∧
              H.isParabolicallyRmControlledBall T x ρ' ∧
              ENNReal.ofReal (cBG * (ρ / ρ') ^ 3) *
                  riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                    (H.stageMetric (H.activeStage T) T)
                    (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ') ≤
                riemannianVolumeMeasure ThreeModel (H.stageAt T).Carrier
                  (H.stageMetric (H.activeStage T) T)
                  (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ)) := by
  obtain ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, makeInitial⟩ :=
    exists_surgery_with_same_flow_volume_or_reserve_and_positive_event_restart_with_closed_support_and_window_scale_bound.{u}
      Dstar hDstar
  refine ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, hκVol,
      cSpatial, hcSpatial, κLarge, hκLarge, hSelected⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, hκVol,
    cSpatial, hcSpatial, κLarge, hκLarge, ?_⟩
  obtain ⟨hcMargin, hMarginMax, hMarginSpatial, hκAll,
      pBase, base, hBaseHistory, hBaseInitial, hBaseShift, hBaseOffset,
      hBaseRadius, hBaseConstant, hBaseFit, hBaseQuality, hBaseDistance,
      request, hRequest, _hCof, _hWindowScale, hWindow, hSupport, hChain⟩ := hSelected
  refine ⟨hcMargin, hMarginMax, hMarginSpatial, hκAll,
    pBase, base, hBaseHistory, hBaseInitial, hBaseShift, hBaseOffset,
    hBaseRadius, hBaseConstant, hBaseFit, hBaseQuality, hBaseDistance,
    request, hRequest, hWindow, ?_, hChain⟩
  intro H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace _C _D a has hat v hv hhalf hclock _hpole
  exact hSupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock

end GC.GeneralFlow
