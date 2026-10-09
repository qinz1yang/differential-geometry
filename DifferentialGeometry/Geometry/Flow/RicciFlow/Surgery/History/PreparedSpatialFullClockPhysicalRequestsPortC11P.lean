import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalRequests

/-!
# S-CH11-FIX12 port of astra `PreparedSpatialFullClockPhysicalRequests`（`PortC11P`）

来源：donor `PreparedSpatialFullClockPhysicalRequests.lean`（Jui-Hui `chapter11-astra` @
`a73e4bdbfd`）。donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement /
definition / proof idea altered；不加 `set_option`）。大部分与同作者的 `PreparedSpatialPhysicalRequests`
/ `PreparedSpatialPhysicalPolicy`（FIX12 G2 / G3）里的同一段代码同类、同修法：
* `hD` 里 `exact add_le_add_right (Real.exp_le_exp.mpr hexponent) 1`、`hfactor` 里
  `apply add_le_add_right`（本树左右约定相反：给 `1 + _ ≤ 1 + _`，目标是 `_ + 1 ≤ _ + 1`）→
  `add_le_add … le_rfl` / `refine add_le_add ?_ le_rfl`；
* `hexp4` / `hexp5` 的 `simpa using Real.add_one_le_exp (4 : ℝ)`：simp 不把 `4 + 1` 算成 `5`，
  "Type mismatch: After simplification" → `linarith [Real.add_one_le_exp (4 : ℝ)]`；
* 裸名 `normalizedDatum`（`DifferentialGeometry.Geometry.Neck`）与 `SpatialCanonicalWitness`
  （`…Perelman.CanonicalNeighborhood.FiniteHorn`）在本树 unknown identifier（`open` 不传递）→ 补两行
  `open`；
* `hRadiusZero` 里 `hParameters 0 0 ⟨le_rfl, le_rfl⟩` 的第二分量是 `0 ≤ ((0 : ℕ) : ℝ)` →
  `by norm_num`；
* `hBounds` 里 `rw [← hBirth n i] at hEntry`（`hEntry` 的大合取含依赖于 `s = time + shift` 的
  项，motive 不 type correct）→ 先取出真正用到的两个纯实数分量 `hEntryRadius` / `hEntryAccuracy`，
  再对它们 `rw`，两处用点改名。

原路径 `PreparedSpatialFullClockPhysicalRequests` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace GC.GeneralFlow
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem full_clock_action_factor_lt_sqrt_two
    (A : ℝ) (hA : 1 ≤ A) :
    preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4 <
      Real.sqrt 2 * preparedSpatialPhysicalActionFactor A := by
  let zA := 2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40
  have hzA : 0 ≤ zA := by
    dsimp only [zA]
    nlinarith [sq_nonneg DifferentialGeometry.Analysis.CutoffProfile.derivBound]
  have hbound : 0 ≤ DifferentialGeometry.Analysis.SingularBarrier.bound zA :=
    DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg hzA
  have hsqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLe : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have hfrac : (9 : ℝ) ≤ 32 / Real.sqrt 2 :=
    (le_div_iff₀ hsqrtPos).mpr (by nlinarith)
  have hexponent : (9 : ℝ) ≤
      DifferentialGeometry.Analysis.SingularBarrier.bound zA / 2 + 32 / Real.sqrt 2 := by
    linarith
  have hD : Real.exp (9 : ℝ) + 1 ≤ preparedSpatialPhysicalActionFactor A := by
    change Real.exp (9 : ℝ) + 1 ≤
      Real.exp (DifferentialGeometry.Analysis.SingularBarrier.bound zA / 2 +
        32 / Real.sqrt 2) + 1
    exact add_le_add (Real.exp_le_exp.mpr hexponent) le_rfl
  have hexp4 : (5 : ℝ) ≤ Real.exp 4 := by
    linarith [Real.add_one_le_exp (4 : ℝ)]
  have hexp5 : (6 : ℝ) ≤ Real.exp 5 := by
    linarith [Real.add_one_le_exp (5 : ℝ)]
  have hexp45 : Real.exp (9 / 2 : ℝ) ≤ Real.exp 5 :=
    Real.exp_le_exp.mpr (by norm_num)
  have hexp9 : Real.exp (9 : ℝ) = Real.exp 4 * Real.exp 5 := by
    rw [show (9 : ℝ) = 4 + 5 by norm_num, Real.exp_add]
  have hmul : 5 * Real.exp (5 : ℝ) ≤ Real.exp 4 * Real.exp 5 :=
    mul_le_mul_of_nonneg_right hexp4 (Real.exp_pos _).le
  have hgrowth : 3 * (Real.exp (9 / 2 : ℝ) + 4) ≤ Real.exp 9 := by
    rw [hexp9]
    nlinarith
  have hslack : 3 * (Real.exp (9 / 2 : ℝ) + 4) <
      preparedSpatialPhysicalActionFactor A := by linarith
  have hfactorPos : 0 < preparedSpatialPhysicalActionFactor A := by
    unfold preparedSpatialPhysicalActionFactor
    positivity
  have hratio : (4 / 3 : ℝ) < Real.sqrt 2 := by nlinarith
  have hfirst : preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4 <
      (4 / 3 : ℝ) * preparedSpatialPhysicalActionFactor A := by linarith
  exact hfirst.trans (mul_lt_mul_of_pos_right hratio hfactorPos)

private theorem full_clock_physical_request_box_bounds_of_le_start
    (m : ℕ) (A T s r v rNext sigma rhoTest : ℝ)
    (hA : 1 ≤ A) (hAb : A < 12 * (3 : ℝ) ^ m)
    (hr : 0 < r) (hv : 0 ≤ v) (hfull : v ^ 2 ≤ r ^ 2)
    (hsmall : 2 * r ^ 2 < T) (hstart : T - v ^ 2 ≤ s)
    (_hsT : s ≤ T) (hsB : s ≤ (3 : ℝ) ^ m)
    (hrNext : 0 < rNext) (hreserve : rNext ≤ sigma)
    (htest : sigma / 100 ≤ rhoTest) :
    0 ≤ Real.sqrt ((3 : ℝ) ^ m) ∧
    0 < rNext / 100 ∧ 0 < (rNext ^ 2)⁻¹ ∧
    T / 2 < s ∧ T ≤ 2 * s ∧ T < (3 : ℝ) ^ (m + 1) ∧
    v ≤ Real.sqrt ((3 : ℝ) ^ m) ∧ r < Real.sqrt ((3 : ℝ) ^ m) ∧
    rNext / 100 ≤ rhoTest ∧
    (preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4) * r <
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
  have hradius : r < Real.sqrt ((3 : ℝ) ^ m) :=
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
  have hfactorPos : 0 < preparedSpatialPhysicalActionFactor A := by
    unfold preparedSpatialPhysicalActionFactor
    positivity
  refine ⟨Real.sqrt_nonneg _, by positivity, by positivity, hrecent, htwo, hband,
    hclock, hradius, by linarith, ?_⟩
  calc
    (preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4) * r <
        (Real.sqrt 2 * preparedSpatialPhysicalActionFactor A) * r :=
      mul_lt_mul_of_pos_right (full_clock_action_factor_lt_sqrt_two A hA) hr
    _ < (Real.sqrt 2 * preparedSpatialPhysicalActionFactor A) *
        Real.sqrt ((3 : ℝ) ^ m) :=
      mul_lt_mul_of_pos_left hradius
        (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hfactorPos)
    _ ≤ (Real.sqrt 2 * preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m)) *
        Real.sqrt ((3 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ m) *
        Real.sqrt (2 * (3 : ℝ) ^ m) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- Carry the same selected physical requests through the full reserve clock,
with the complete action budget and unchanged node arrays. -/
theorem PreparedSpatialChain.full_clock_physical_requests_of_saved_data
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (hoffset : ∀ n, (S.state (n + 1)).offset = (S.state n).history.eventCount)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (rNext : ℕ → ℝ)
    (hrNext : ∀ m, 0 < rNext m ∧ (S.state (m + 1)).radius = rNext m)
    (hRequested : ∀ m,
      let req := preparedSpatialPhysicalQualityRequest request m (rNext m)
      εcut m = req.1 ∧ Dcut m = req.2.1 ∧ mcut m = req.2.2.1 ∧
        S.accuracy m ≤ req.2.2.2)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ)
    (hδanti : AntitoneOn q.delta (Ici 0))
    (hRadiusAnti : AntitoneOn q.neckRadius (Ici 0))
    (hParameters : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t)
    (hForward : ∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
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
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z)))
    (hDerivative : ∀ (m n : ℕ) (j : Fin ((F.tower.history n).eventCount + 1)),
        (S.state (m + 1)).offset ≤ j.val →
        ∀ (y : ((F.tower.history n).stage j).Carrier) (s : ℝ),
          s ∈ Ioo ((F.tower.history n).time j)
            ((F.tower.history n).toHistory.stageEndTime j) →
          s < (3 : ℝ) ^ (m + 1) →
          ((S.state (m + 1)).radius ^ 2)⁻¹ <
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun u =>
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j u) y) (Iic s) s| ≤
            C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hRawBlock : ∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
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
      ) :
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier)
        (r A v rhoTest : ℝ),
        0 < r → 1 ≤ A → 0 ≤ v → v ^ 2 ≤ r ^ 2 → 2 * r ^ 2 < t.val →
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
              C.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        (preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4) * r < nodeA i := by
  classical
  choose _hBlock nativeIndex hCountLo _hCountHi _hIndex hBirth hBirthBand
    _hPresentation hDelta hRawRadius hRawOrder hRawAccuracy hCap using hRawBlock
  have hRadiusZero : q.neckRadius 0 ≤ 1 := by
    calc
      q.neckRadius 0 = (S.observation 0).parameters.neckRadius 0 :=
        (hParameters 0 0 ⟨le_rfl, by norm_num⟩).2.1
      _ = (S.state 1).parameters.neckRadius 0 := rfl
      _ = (S.state 0).parameters.neckRadius 0 :=
        ((S.successor 0).parameters_past 0 (by norm_num [preparedSpatialHorizon])).2.1
      _ = (S.state 0).radius :=
        (S.state 0).radius_after 0 (by norm_num [preparedSpatialHorizon])
      _ ≤ 1 := S.initial_radius_le
  intro n H t x r A v rhoTest hr hA hv hfull hsmall hAccuracy hPoleBall hTest
    _first _hle _hpast nodeA nodeE nodeR nodeQ nodeRho
  have hBounds (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
      (hstart : t.val - v ^ 2 ≤ H.time i.succ) :
      0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧
      t.val < (3 : ℝ) ^ (block n i + 1) ∧ v ≤ nodeE i ∧ nodeR i ≤ rhoTest ∧
      (preparedSpatialPhysicalActionFactor A + Real.exp (9 / 2) + 4) * r < nodeA i := by
    have hbirth : H.time i.succ ≤ t.val :=
      (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
    have hrecent : t.val / 2 < H.time i.succ := by
      nlinarith [sq_nonneg r]
    have htwo : t.val ≤ 2 * H.time i.succ := by linarith
    have hEntry := hForward (block n i) (nativeIndex n i)
    dsimp only at hEntry
    have hEntryRadius := hEntry.2.2.2.1
    have hEntryAccuracy := hEntry.2.2.2.2.1
    rw [← hBirth n i] at hEntryRadius hEntryAccuracy
    have hAb : A < 12 * (3 : ℝ) ^ (block n i) :=
      hEntryAccuracy A (by linarith) (hAccuracy _ ⟨hrecent.le, hbirth⟩)
    have hReserve : rNext (block n i) ≤ q.neckRadius t.val := by
      rw [← (hrNext (block n i)).2]
      exact hEntryRadius t.val ⟨hbirth, htwo⟩
    obtain ⟨hE, hR, hQ, _hRecent', _hTwo', hBand, hClock, _hRadius, hRTest, hFit⟩ :=
      full_clock_physical_request_box_bounds_of_le_start (block n i) A t.val (H.time i.succ) r v
        (rNext (block n i)) (q.neckRadius t.val) rhoTest hA hAb hr hv hfull hsmall
        hstart hbirth (hBirthBand n i).2 (hrNext (block n i)).1 hReserve hTest
    exact ⟨hE, hR, hQ, hBand, hClock, hRTest, hFit⟩
  refine ⟨?_, fun i _hf hl hstart => (hBounds i hl hstart).2.2.2.2.2.2⟩
  intro i _hf hl hstart req
  obtain ⟨hE, hR, hQ, hBand, hClock, hRTest, _hFit⟩ := hBounds i hl hstart
  have hReq := hRequested (block n i)
  simp only [preparedSpatialPhysicalQualityRequest,
    ite_eq_left (hrNext (block n i)).1] at hReq
  change εcut (block n i) = req.1 ∧ Dcut (block n i) = req.2.1 ∧
    mcut (block n i) = req.2.2.1 ∧ S.accuracy (block n i) ≤ req.2.2.2 at hReq
  have hδNode : q.delta (H.time i.succ) ≤ req.2.2.2 :=
    (hDelta n i).le.trans hReq.2.2.2
  have hRadius : q.neckRadius (H.time i.succ) ≤ nodeRho i :=
    (hRadiusAnti (by norm_num) (H.time_nonneg i.succ) (H.time_nonneg i.succ)).trans hRadiusZero
  refine ⟨hE, hR, hQ, by norm_num, hClock, hPoleBall.mono_radius H hR hRTest,
    hδNode, hRadius, ?_, ?_, ?_⟩
  · intro j hij _ b
    have htime : H.time i.succ ≤ H.time j.succ :=
      H.time_strictMono.monotone (hij.trans j.castSucc_le_succ)
    exact ((records n j).delta_le b).trans
      ((hδanti (H.time_nonneg i.succ) (H.time_nonneg j.succ) htime).trans hδNode)
  · intro j hij _ y s hs hsT hscalar
    have hOffset : (S.state (block n i + 1)).offset ≤ j.val := by
      rw [hoffset]
      have hcount := hCountLo n i
      have hval : i.succ.val ≤ j.val := hij
      simp only [Fin.val_succ] at hval
      omega
    have hscalar' : ((S.state (block n i + 1)).radius ^ 2)⁻¹ <
        metricScalarAt (H.stageMetric j s) y := by
      rw [(hrNext (block n i)).2]
      exact hscalar
    exact hDerivative (block n i) n j hOffset y s hs (hsT.trans_lt hBand) hscalar'
  · intro b'
    obtain ⟨_b, raw, _hLabel, hCanonical, _hDelta, _hOrder, _hNeck, _hWitness,
      _hOutput, _hMetric, _hInclusion, _hCap, _hRetained, _hCollapse,
      _hWindowMetric, _hWindowPoints, hScale, _hRemaining⟩ := hCap n i b'
    exact ⟨(W (block n i)).fineParameters.modelRadius,
      (W (block n i)).fineParameters.modelAccuracy,
      (W (block n i)).fineParameters.modelOrder, raw,
      hReq.2.1.symm.le.trans (hRawRadius n i),
      hReq.2.2.1.symm.le.trans (hRawOrder n i),
      (hRawAccuracy n i).trans hReq.1.le, hCanonical, hScale⟩

end GC.GeneralFlow
