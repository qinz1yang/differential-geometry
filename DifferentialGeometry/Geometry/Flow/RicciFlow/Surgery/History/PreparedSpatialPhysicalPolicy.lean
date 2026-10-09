import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventLocalWeightedTemporalSupport

/-!
# S-CH11-FIX12 patched-at-path `PreparedSpatialPhysicalPolicy`

来源：donor `PreparedSpatialPhysicalPolicy.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）。patched-at-path：下游 `PreparedSpatialPhysicalRequests`
对它做 `open private … from` 原路径，故不做 PortC11P + shim（原路径文本 = 本文件）：
* `hfactor` 里 `apply add_le_add_right`（本树左右约定相反：`add_le_add_right` 给 `a + b ≤ a + c`，
  而目标是 `X + 1 ≤ Y + 1`）→ `refine add_le_add ?_ le_rfl`；
* `exists_prepared_spatial_physical_request_chains` 的 docstring 写在 `attribute [-instance] … in`
  前面，本树 parser 报 "unexpected token 'attribute'; expected 'lemma'" → 两者对调
  （`attribute … in` 在前，docstring 紧贴 `theorem`）；
* 陈述里裸名 `volume` 在本树 unknown identifier（autoImplicit false）→ `MeasureTheory.volume`。
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

def preparedSpatialPhysicalActionFactor (A : ℝ) : ℝ :=
  Real.exp (DifferentialGeometry.Analysis.SingularBarrier.bound
    (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40) / 2 +
      32 / Real.sqrt 2) + 1

def preparedSpatialPhysicalQualityRequest
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (m : ℕ) (rNext : ℝ) : ℝ × ℝ × ℕ × ℝ :=
  if 0 < rNext then
    request (preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) *
      Real.sqrt (2 * (3 : ℝ) ^ m)) (Real.sqrt ((3 : ℝ) ^ m))
      (rNext / 100) ((rNext ^ 2)⁻¹) 1
  else (1, 1, 0, 1)

private theorem physical_request_box_bounds_of_le_start
    (m : ℕ) (A T s r v rNext sigma rhoTest : ℝ)
    (hA : 1 ≤ A) (hAb : A < 12 * (3 : ℝ) ^ m)
    (hr : 0 < r) (hv : 0 ≤ v) (hhalf : v ^ 2 ≤ r ^ 2 / 2)
    (hsmall : 2 * r ^ 2 < T) (hstart : T - v ^ 2 ≤ s)
    (hsT : s ≤ T) (hsB : s ≤ (3 : ℝ) ^ m)
    (hrNext : 0 < rNext) (hreserve : rNext ≤ sigma)
    (htest : sigma / 100 ≤ rhoTest) :
    0 ≤ Real.sqrt ((3 : ℝ) ^ m) ∧
    0 < rNext / 100 ∧ 0 < (rNext ^ 2)⁻¹ ∧
    T / 2 < s ∧ T ≤ 2 * s ∧ T < (3 : ℝ) ^ (m + 1) ∧
    v ≤ Real.sqrt ((3 : ℝ) ^ m) ∧ r < Real.sqrt (2 * (3 : ℝ) ^ m) ∧
    rNext / 100 ≤ rhoTest ∧
    preparedSpatialPhysicalActionFactor A * r <
      preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) *
        Real.sqrt (2 * (3 : ℝ) ^ m) := by
  have hB : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) m
  have hrecent : T / 2 < s := by nlinarith
  have htwo : T ≤ 2 * s := by linarith
  have hband : T < (3 : ℝ) ^ (m + 1) := by
    rw [pow_succ]
    nlinarith
  have hclock : v ≤ Real.sqrt ((3 : ℝ) ^ m) :=
    (Real.le_sqrt hv hB.le).mpr (by nlinarith)
  have hradius : r < Real.sqrt (2 * (3 : ℝ) ^ m) :=
    (Real.lt_sqrt hr.le).mpr (by nlinarith)
  let zA := 2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40
  let zB := 2 * (12 * (3 : ℝ) ^ m) +
    160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40
  have hzA : 0 ≤ zA := by
    dsimp only [zA]
    nlinarith [sq_nonneg DifferentialGeometry.Analysis.CutoffProfile.derivBound]
  have hzAB : zA ≤ zB := by
    dsimp only [zA, zB]
    linarith
  have hsq : zA ^ 2 ≤ zB ^ 2 := pow_le_pow_left₀ hzA hzAB 2
  have hbound : DifferentialGeometry.Analysis.SingularBarrier.bound zA ≤
      DifferentialGeometry.Analysis.SingularBarrier.bound zB := by
    unfold DifferentialGeometry.Analysis.SingularBarrier.bound
    nlinarith
  have hfactor : preparedSpatialPhysicalActionFactor A ≤
      preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) := by
    change Real.exp (DifferentialGeometry.Analysis.SingularBarrier.bound zA / 2 +
      32 / Real.sqrt 2) + 1 ≤
      Real.exp (DifferentialGeometry.Analysis.SingularBarrier.bound zB / 2 +
        32 / Real.sqrt 2) + 1
    refine add_le_add ?_ le_rfl
    apply Real.exp_le_exp.mpr
    linarith
  have hfactorPos : 0 < preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) := by
    unfold preparedSpatialPhysicalActionFactor
    positivity
  refine ⟨Real.sqrt_nonneg _, by positivity, by positivity, hrecent, htwo, hband,
    hclock, hradius, by linarith, ?_⟩
  exact (mul_le_mul_of_nonneg_right hfactor hr.le).trans_lt
    (mul_lt_mul_of_pos_left hradius hfactorPos)

private theorem physical_request_box_bounds
    (m : ℕ) (A T s r v rNext sigma rhoTest : ℝ)
    (hA : 1 ≤ A) (hAb : A < 12 * (3 : ℝ) ^ m)
    (hr : 0 < r) (hv : 0 ≤ v) (hhalf : v ^ 2 ≤ r ^ 2 / 2)
    (hsmall : 2 * r ^ 2 < T) (hstart : T - v ^ 2 < s)
    (hsT : s ≤ T) (hsB : s ≤ (3 : ℝ) ^ m)
    (hrNext : 0 < rNext) (hreserve : rNext ≤ sigma)
    (htest : sigma / 100 ≤ rhoTest) :
    0 ≤ Real.sqrt ((3 : ℝ) ^ m) ∧
    0 < rNext / 100 ∧ 0 < (rNext ^ 2)⁻¹ ∧
    T / 2 < s ∧ T ≤ 2 * s ∧ T < (3 : ℝ) ^ (m + 1) ∧
    v ≤ Real.sqrt ((3 : ℝ) ^ m) ∧ r < Real.sqrt (2 * (3 : ℝ) ^ m) ∧
    rNext / 100 ≤ rhoTest ∧
    preparedSpatialPhysicalActionFactor A * r <
      preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) *
        Real.sqrt (2 * (3 : ℝ) ^ m) := by
  exact physical_request_box_bounds_of_le_start m A T s r v rNext sigma rhoTest
    hA hAb hr hv hhalf hsmall hstart.le hsT hsB hrNext hreserve htest

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Select the original scalar clock and one physical request before the same
prepared chain. The complete half-clock support callback remains attached to
that request, and each future radius precedes its fine quality choice. -/
theorem exists_prepared_spatial_physical_request_chains :
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
      base.DistanceData Cdist ∧
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        0 < (request Aact E rTerm qDeriv ρ).1 ∧
        0 < (request Aact E rTerm qDeriv ρ).2.1 ∧
        0 < (request Aact E rTerm qDeriv ρ).2.2.2) ∧
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
    exists_prepared_spatial_quality_chains_from_initial_with_small_test_margin.{u}
  refine ⟨Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hDistance, makeChain⟩ := makeBase cMax hcMax
  have hc : 0 < pBase.recenterConstant := by
    linarith [pBase.recenterConstant_ge_four]
  obtain ⟨request, hrequest, hsupport⟩ :=
    ObservedHistory.exists_distinct_pole_half_clock_support_with_event_local_cap_requests.{u}
      a₀ pBase.recenterConstant (StandardCap.transitionEnd + 10) constants.Ctime
      ha₀ hc (by linarith)
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hDistance, request, hrequest, hsupport, ?_⟩
  apply makeChain (fun n _ _ rNext => preparedSpatialPhysicalQualityRequest request n rNext)
  intro n _ _ rNext hrNext
  simpa only [preparedSpatialPhysicalQualityRequest, ite_eq_left hrNext] using
    hrequest
      (preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ n) *
        Real.sqrt (2 * (3 : ℝ) ^ n))
      (Real.sqrt ((3 : ℝ) ^ n)) (rNext / 100) ((rNext ^ 2)⁻¹) 1
      (Real.sqrt_nonneg _) (by positivity) (by positivity) (by norm_num)

end GC.GeneralFlow
