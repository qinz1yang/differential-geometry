import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalPolicy

/-!
# S-CH11-FIX12 patched-at-path `PreparedSpatialPhysicalPolicyReserveQuality`

来源：donor `PreparedSpatialPhysicalPolicyReserveQuality.lean`（Jui-Hui `chapter11-astra` @
`a73e4bdbfd`）。donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement /
definition / proof idea altered；不加 `set_option`）。patched-at-path：下游
`PreparedSpatialBirthVolumeOrReserve` 对它做 `open private … from` 原路径，故不做 PortC11P + shim
（原路径文本 = 本文件）：
* 6 个陈述里裸名 `volume`（`IntervalIntegrable … volume`）在本树 unknown identifier
  （autoImplicit false；同 `PreparedSpatialPhysicalPolicy`）→ `MeasureTheory.volume`（折行）。
* S-CH11-HCOF（statement 级新增，非 elaboration 修补）：private
  `prepared_spatial_closed_physical_request_chains_with_window_scale_bound` 的 `request` 换成共尾
  request `preparedSpatialCofinalRequest request₀`（`E → ∞` 时 `εcut → 0`、`Dcut → ∞`、`mcut → ∞`），
  ∃ 陈述在 `hRequest` 后多带一个共尾子句 `hCof`；`hWindowScale / hWindow / hSupport` 对更严的
  request 单调（`req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1` 都在前件），逐个提升；
  public `…_at_closed_poles` 只改 obtain 模式（`_hCof`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace GC.GeneralFlow
universe u

/-- S-CH11-HCOF：共尾 request。`request` 换成 `(min ε (E + 1)⁻¹, max D E, max m ⌈E⌉₊, δ)`，
于是 `E → ∞` 时 `εcut → 0`、`Dcut → ∞`、`mcut → ∞`（`δ` 分量不变）；四个子句对更严的 request 单调。 -/
def preparedSpatialCofinalRequest
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ :=
  fun Aact E rTerm qDeriv ρ =>
    (min (request Aact E rTerm qDeriv ρ).1 (E + 1)⁻¹,
      max (request Aact E rTerm qDeriv ρ).2.1 E,
      max (request Aact E rTerm qDeriv ρ).2.2.1 ⌈E⌉₊,
      (request Aact E rTerm qDeriv ρ).2.2.2)

/-- One closed-pole physical request and one genuine chain retain the same class quality and callbacks. -/
private theorem prepared_spatial_closed_physical_request_chains_with_window_scale_bound
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ constants : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ cMax : ℝ, 0 < cMax →
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase constants P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax ∧
      base.prepared.HasReserveQuality Dstar εReserve ∧
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
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j))
        MeasureTheory.volume
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
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j))
        MeasureTheory.volume
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
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
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
      (∀ n, S.accuracy n ≤ (policy n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (policy n (S.state n) (future n) (r n)).1
        (policy n (S.state n) (future n) (r n)).2.1
        (policy n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨Cdist, hCdist, constants, -, makeInitial⟩ :=
    exists_prepared_spatial_quality_chains_from_initial_with_small_test_margin_with_reserve_quality.{u}
      Dstar εReserve hDstar hεReserve
  refine ⟨Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hBaseQuality, hDistance, makeChain⟩ := makeBase cMax hcMax
  have hc : 0 < pBase.recenterConstant := by
    linarith [pBase.recenterConstant_ge_four]
  obtain ⟨request₀, hrequest₀, hWindowScale₀, hcapExclusion₀, hsupport₀⟩ :=
    ObservedHistory.exists_distinct_pole_half_clock_support_with_event_local_cap_exclusion_requests_at_closed_poles_with_window_scale_bound.{u}
      a₀ pBase.recenterConstant (StandardCap.transitionEnd + 10) constants.Ctime
      ha₀ hc (by linarith)
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hBaseQuality, hDistance, preparedSpatialCofinalRequest request₀,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Aact E rTerm qDeriv ρ hE hr hq hρ
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrequest₀ Aact E rTerm qDeriv ρ hE hr hq hρ
    exact ⟨lt_min h1 (inv_pos.2 (by linarith)), (min_le_left _ _).trans h2,
      lt_max_of_lt_left h3, lt_max_of_lt_left h4, h5.trans (le_max_left _ _), h6⟩
  · intro Aact E rTerm qDeriv ρ hE hr hq hρ
    exact ⟨min_le_right _ _, le_max_right _ _,
      (Nat.le_ceil E).trans (Nat.cast_le.2 (le_max_right _ _))⟩
  · intro Aact E rTerm qDeriv ρ hE hr hq hρ _req P' Q' a s event fixed Dbig ζ m hD hm hζ b raw hcan
    exact hWindowScale₀ Aact E rTerm qDeriv ρ hE hr hq hρ event
      (le_trans (le_max_left _ _) hD) (le_trans (le_max_left _ _) hm)
      (hζ.trans (min_le_left _ _)) raw hcan
  · intro Aact E rTerm qDeriv ρ hE hr hq hρ _req H parameters records hI hS t first hle v hv0 hvE
      hdom pole hball gamma hg1 hg2 hg3 hg4 hsum i hf hl hstart hrc hδ hnr hrec hdrv b Dbig ζ m S
      hD hm hζ hcan hscale
    exact hcapExclusion₀ Aact E rTerm qDeriv ρ hE hr hq hρ H parameters records hI hS t first hle v
      hv0 hvE hdom pole hball gamma hg1 hg2 hg3 hg4 hsum i hf hl hstart hrc hδ hnr hrec hdrv b Dbig
      ζ m S (le_trans (le_max_left _ _) hD) (le_trans (le_max_left _ _) hm)
      (hζ.trans (min_le_left _ _)) hcan hscale
  · intro H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
      aSeed hSeedTime hSeedClock seedTrace _C _D a has hat v hv hhalf hclock hmem first last hle O
      nodeA nodeE nodeR nodeQ nodeRho hnodes hDr
    refine hsupport₀ H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
      aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock hmem
      nodeA nodeE nodeR nodeQ nodeRho (fun i hf hl => ?_) hDr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hb⟩ := hnodes i hf hl
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun b => ?_⟩
    obtain ⟨Dbig, ζ, m, S, hD, hm, hζ, hrest⟩ := hb b
    exact ⟨Dbig, ζ, m, S, le_trans (le_max_left _ _) hD, le_trans (le_max_left _ _) hm,
      hζ.trans (min_le_left _ _), hrest⟩
  · apply makeChain (fun n _ _ rNext =>
      preparedSpatialPhysicalQualityRequest (preparedSpatialCofinalRequest request₀) n rNext)
    intro n _ _ rNext hrNext
    obtain ⟨hε, _, hD, _, _, hδ⟩ :=
      hrequest₀
        (preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ n) *
          Real.sqrt (2 * (3 : ℝ) ^ n))
        (Real.sqrt ((3 : ℝ) ^ n)) (rNext / 100) ((rNext ^ 2)⁻¹) 1
        (Real.sqrt_nonneg _) (by positivity) (by positivity) (by norm_num)
    simpa only [preparedSpatialPhysicalQualityRequest, preparedSpatialCofinalRequest,
      ite_eq_left hrNext] using
      (And.intro (lt_min hε (inv_pos.2 (by positivity))) (And.intro (lt_max_of_lt_left hD) hδ))

theorem exists_prepared_spatial_physical_request_chains_with_cap_exclusion_and_reserve_quality_at_closed_poles
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ constants : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ cMax : ℝ, 0 < cMax →
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase constants P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax ∧
      base.prepared.HasReserveQuality Dstar εReserve ∧
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
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j))
        MeasureTheory.volume
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
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j))
        MeasureTheory.volume
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
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
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
      (∀ n, S.accuracy n ≤ (policy n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (policy n (S.state n) (future n) (r n)).1
        (policy n (S.state n) (future n) (r n)).2.1
        (policy n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨Cdist, hCdist, constants, makeInitial⟩ :=
    prepared_spatial_closed_physical_request_chains_with_window_scale_bound.{u}
      Dstar εReserve hDstar hεReserve
  refine ⟨Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
      hRadiusConstant, hFit, hBaseQuality, hDistance, request,
      hrequest, _hCof, _hWindowScale, hcapExclusion, hsupport, hChain⟩ := makeBase cMax hcMax
  exact ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hBaseQuality, hDistance, request,
    hrequest, hcapExclusion, hsupport, hChain⟩

/-- One physical request and one genuine chain retain class quality and both action callbacks. -/
theorem exists_prepared_spatial_physical_request_chains_with_cap_exclusion_and_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ constants : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ cMax : ℝ, 0 < cMax →
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase constants P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax ∧
      base.prepared.HasReserveQuality Dstar εReserve ∧
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
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j))
        MeasureTheory.volume
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
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j))
        MeasureTheory.volume
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
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
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
      (∀ n, S.accuracy n ≤ (policy n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (policy n (S.state n) (future n) (r n)).1
        (policy n (S.state n) (future n) (r n)).2.1
        (policy n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨Cdist, hCdist, constants, makeInitial⟩ :=
    exists_prepared_spatial_physical_request_chains_with_cap_exclusion_and_reserve_quality_at_closed_poles.{u}
      Dstar εReserve hDstar hεReserve
  refine ⟨Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
      hRadiusConstant, hFit, hBaseQuality, hDistance,
      request, hrequest, hcapExclusion, hsupport, hChain⟩ := makeBase cMax hcMax
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hBaseQuality, hDistance, request,
    hrequest, hcapExclusion, ?_, hChain⟩
  intro H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace _C _D a has hat v hv hhalf hclock _hpole
  exact hsupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock

end GC.GeneralFlow
