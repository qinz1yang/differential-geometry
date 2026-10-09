import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBirthPhysicalRequests
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalVolumeOrReserve

/-!
# S-CH11-FIX11 patched-at-path `PreparedSpatialBirthVolumeOrReserve`

来源：donor `PreparedSpatialBirthVolumeOrReserve.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；下游模块对本路径 `open private … from`，
所以修补文本就放在原路径（patched-at-path）。只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 陈述里 `volume`（×4）、`SpatialCanonicalWitness`（×2）、`normalizedDatum`（×4）
  unknown identifier（statement 级；`autoImplicit false`）→ header 补 `open MeasureTheory`
  （并入首行）、`open DifferentialGeometry.Geometry.Neck`、
  `open …Perelman.CanonicalNeighborhood.FiniteHorn`（与 FIX12 给
  `PreparedSpatialPhysicalVolumeOrReserve` 补的同一批；donor 自带的
  `open DifferentialGeometry.Integral.Measure` 不够解析 `volume`）；
* `open private
  GC.GeneralFlow.prepared_spatial_closed_physical_request_chains_with_window_scale_bound
  from …` 的 `GC.GeneralFlow.` 前缀在本树不生效（后文无前缀引用报 "Unknown identifier"）
  → 去掉前缀；
* `hObservation` 里 `unfold ObservationTower.observe; rw [Nat.ceil_natCast]; rfl`：motive 不
  type correct（`atIndex _a ↑n ⋯ ⋯` 的证明项依赖 `_a`）→
  `simp only [ObservationTower.observe, Nat.ceil_natCast]; rfl`（同 FIX12 对
  `PreparedSpatialPhysicalVolumeOrReserve` 的修法）；
* **heartbeat 例外（lead 04:0x ruling A；04:3x 批第一条上限 600000）**：两条整条（陈述 + 证明）
  约 700 / 600 行的声明，陈述不可拆（donor 陈述原样），逐声明加
  `set_option maxHeartbeats N in`（不整文件）。实测：
  `closed_pole_volume_or_reserve_with_saved_window_scale_bound` 在 400000 / 450000 / 500000
  超限，600000 通过（800000、1000000 亦通过）→ 取 600000；
  `exists_surgery_with_physical_requests_and_test_volume_or_reserve_at_closed_poles` 在
  200000 超限、400000 通过 → 取 400000；
* 12 个陈述 / 中间 binder（`hf` / `hl` / `hle` / `hstart`）不被引用 → 加 `_` 前缀。
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
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

open private cast_point cast_point_heq ball_mem_iff_of_metric_heq
  ball_volume_eq_of_metric_heq restricted_controlled_ball from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix.Basic
open private extended_restricted_controlled_ball from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.HistoryParabolicBallPrefixTransport
open private restricted_small_parabolic_curvature from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalVolumeOrReserve

open private prepared_spatial_closed_physical_request_chains_with_window_scale_bound from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalPolicyReserveQuality

set_option maxHeartbeats 600000 in
-- heartbeat exception 600000 (measured 400000/450000/500000 fail, 600000 pass), lead 04:3x
private theorem closed_pole_volume_or_reserve_with_saved_window_scale_bound
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
    ∀ cMargin : ℝ, 0 < cMargin → cMargin ≤ cMax →
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
                  (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ))
      ) ∧
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.isParabolicallyRmControlledBall t p r →
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x < ENNReal.ofReal (A * r) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest → rhoTest < r →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
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
  obtain ⟨εcap, cBG, hεcap, hcBG, reserveVolume⟩ :=
    exists_test_volume_or_reserve_in_same_observation_of_retained_class_quality.{u}
      Dstar hDstar
  obtain ⟨Cdist, hCdist, constants, makeInitial⟩ :=
    prepared_spatial_closed_physical_request_chains_with_window_scale_bound.{u}
      Dstar εcap (StandardCap.transitionEnd_pos.trans hDstar) hεcap
  refine ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  obtain ⟨cMax, hcMax, makeVolume⟩ := reserveVolume P g constants
  choose κOf hκOf volumeOf using (fun A : Ioi (0 : ℝ) => makeVolume A A.2)
  let κVol : ℝ → ℝ := fun A => if hA : 0 < A then κOf ⟨A, hA⟩ else 1
  refine ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, ?_, ?_⟩
  · intro A hA
    simpa only [κVol, dite_eq_left hA] using hκOf ⟨A, hA⟩
  intro cMargin hcMargin hMargin
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hBaseFit, hBaseQuality, hBaseDistance,
    request, hRequest, hCof, hWindowScale, hWindow, hSupport, hChain⟩ := makeBase cMargin hcMargin
  obtain ⟨S, future, rNext, hFutureQuality, hStateQuality, hZero, hAllFit,
    hDistance, hState, hQuarter, hRequested, hW⟩ := hChain
  obtain ⟨W⟩ := hW
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hBaseFit, hBaseQuality, hBaseDistance, request,
    hRequest, hCof, hWindowScale, hWindow, hSupport, S, future, rNext, hFutureQuality,
    hStateQuality, hZero, hAllFit, hDistance, hState, hQuarter, hRequested, W, ?_⟩
  obtain ⟨F, q, κ, records, hOld, hBirthStage⟩ :=
    S.exists_surgery_with_closed_start_physical_requests_and_birth_pole_stage hDistance
      (fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).1)
      (fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.1)
      (fun n => (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.2.1) W
      (fun n => (hState n).2.2.2.1) (fun n => (hState n).2.2.2.2.1)
      hQuarter a₀ initialControl request rNext
      (fun n => ⟨(hState n).1, (hState n).2.1⟩)
      (fun n => ⟨rfl, rfl, rfl, hRequested n⟩) ha₀ hRequest hWindow hSupport
  refine ⟨F, q, κ, records, ⟨hOld, ?_⟩, hBirthStage⟩
  have hTower : F.tower = S.tower := hOld.1.1.1.1
  have hDiagonal := hOld.1.1.2.1
  have hshift0 : (S.state 0).shift = 0 := by
    rw [hZero]
    exact hShift
  have hradius0 : ∀ s : ℝ,
      (S.state 0).parameters.neckRadius s = (S.state 0).radius := by
    rw [hZero]
    exact hRadiusConstant
  have hshift (n : ℕ) : (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount) :=
    (hState n).2.2.2.1
  have hoffset (n : ℕ) : (S.state (n + 1)).offset = (S.state n).history.eventCount :=
    (hState n).2.2.2.2.1
  intro n H T r hr hT hsmall σ
  have hRadiusDiagonal : q.neckRadius T =
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T :=
    (hDiagonal T T.2.1).2
  have hsmallDiagonal :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius T / 100 < r := by
    rw [← hRadiusDiagonal]
    exact hsmall
  obtain ⟨j, hj⟩ :=
    S.exists_small_test_reserve_in_same_native_class_with_reserve_quality
      hStateQuality hcMargin hAllFit hshift0 hradius0 hshift hr hT hsmallDiagonal
  rw [← hRadiusDiagonal] at hj
  obtain ⟨hQualityj, hσj, hBand, hWindowj, hCapacity, hσpos, hBound, hNumbers⟩ := hj
  refine ⟨j, hQualityj, hσj, hBand, hWindowj, hCapacity, hσpos, hBound, hNumbers, ?_⟩
  change σ = (S.state j).radius at hσj
  change (S.state j).shift < (T : ℝ) - (σ / 100) ^ 2 at hWindowj
  have hshift_nonneg : 0 ≤ (S.state j).shift := (S.state j).affine.shift_nonneg
  have hτpos : 0 < (T : ℝ) - (S.state j).shift := by
    nlinarith [sq_nonneg (σ / 100)]
  have hτtop : (T : ℝ) - (S.state j).shift < (W j).oldNative.horizon := by
    rw [(W j).oldNative_horizon]
    exact sub_lt_sub_right hCapacity _
  let τ : Icc (0 : ℝ) (W j).oldNative.horizon :=
    ⟨(T : ℝ) - (S.state j).shift, hτpos.le, hτtop.le⟩
  have hclock : (T : ℝ) = (τ : ℝ) + (S.state j).shift := by
    dsimp only [τ]
    ring
  have hback : ((S.state j).radius / 100) ^ 2 ≤ (τ : ℝ) := by
    change ((S.state j).radius / 100) ^ 2 ≤ (T : ℝ) - (S.state j).shift
    rw [← hσj]
    linarith
  have hfitMax : (S.state j).radius * Real.sqrt (S.state j).prepared.Qall ≤ 100 * cMax :=
    (hAllFit j).trans (mul_le_mul_of_nonneg_left hMargin (by norm_num))
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
  have hreservej : (S.state j).radius / 100 < r := by
    rw [← hσj]
    exact hsmall
  have hphysical := volumeOf ⟨A, hA⟩ S F hTower j (W j)
    (hshift j) (hoffset j) hshift_nonneg hQualityj.1 hQualityj.2.1
    hQualityj.2.2.1 hQualityj.2.2.2 hfitMax (n : ℝ) (Nat.cast_nonneg n)
  rw [hObservation] at hphysical
  have hresult := hphysical tR τ hclock hτtop hback pR xR r hseedR
    (by rw [hVolumeSeed]; exact hseedVolume) hxRestricted hreservej ρ hρr htestR
  rcases hresult with hvolume | ⟨ρ', hreserve', hρ'r, hρρ', hball', hratio⟩
  · left
    simpa only [κVol, dite_eq_left hA, hVolumeX ρ] using hvolume
  · right
    refine ⟨ρ', ?_, hρ'r, hρρ',
      extended_restricted_controlled_ball H u tR xR x hxR hball', ?_⟩
    · rw [hσj]
      exact hreserve'
    · simpa only [hVolumeX ρ, hVolumeX ρ'] using hratio

set_option maxHeartbeats 400000 in
-- heartbeat exception 400000 (200000 fails, 400000 passes), lead 04:0x ruling A
theorem exists_surgery_with_physical_requests_and_test_volume_or_reserve_at_closed_poles
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
    ∀ cMargin : ℝ, 0 < cMargin → cMargin ≤ cMax →
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
                  (riemannianBallOf (H.stageMetric (H.activeStage T) T) x ρ))
      ) ∧
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.isParabolicallyRmControlledBall t p r →
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x < ENNReal.ofReal (A * r) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest → rhoTest < r →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
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
  obtain ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, makeInitial⟩ :=
    closed_pole_volume_or_reserve_with_saved_window_scale_bound.{u} Dstar hDstar
  refine ⟨εcap, cBG, hεcap, hcBG, Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, hκVol, makeAtMargin⟩ :=
    makeInitial P g
  refine ⟨a₀, ha₀, initialControl, cMax, hcMax, κVol, hκVol, ?_⟩
  intro cMargin hcMargin hMargin
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
      hRadiusConstant, hBaseFit, hBaseQuality, hBaseDistance,
      request, hRequest, _hCof, _hWindowScale, hWindow, hSupport, hChain⟩ :=
    makeAtMargin cMargin hcMargin hMargin
  exact ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hBaseFit, hBaseQuality, hBaseDistance,
    request, hRequest, hWindow, hSupport, hChain⟩

end GC.GeneralFlow
