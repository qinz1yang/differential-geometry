import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedStagePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleBirthWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.NonnegativeEventWindowEndpointPair

/-!
# S-CH11-FIX11 port of astra `DistinctPoleBirthStagePropagation`（`PortC11P`）

来源：donor `DistinctPoleBirthStagePropagation.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `exists_old_seed_and_endpoint_outside_retained_cap_windows_of_nonneg_clock … r 0 Aact rTerm hr
  le_rfl (by positivity) …` 的 `hhalf : 0 ^ 2 ≤ r ^ 2 / 2`：目标是 `0 ^ 2 ≤ …`，positivity 报
  "not a positivity goal" → `(by rw [zero_pow two_ne_zero]; positivity)`；
* 陈述里 `(hf : …) (hl : …)` 在 `∀ i, hf → hl → …` 前缀里不被引用 → `_hf` / `_hl`；
* 1 处命令内空行（`linter.style.emptyLine`）删除。

原路径 `DistinctPoleBirthStagePropagation` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private theorem actual_zero_clock_pair_receives_no_shortcut
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r Aact rTerm : ℝ) (hr : 0 < r)
    (hseed : H.isParabolicallyRmControlledBall t p r)
    (hrTerm : 0 < rTerm) (hrTermLe : rTerm ≤ r)
    (htest : H.isParabolicallyRmControlledBall t x rTerm)
    (hseedBudget : 3 * r ≤ Aact)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (htrace : seedTrace.isRmControlled (hat := hSeedTime) r)
    (i : Fin H.eventCount) (hactive : H.activeStage t = i.succ)
    (hbirth : t.val = H.time i.succ)
    {D ε : ℝ} {m : ℕ}
    (S : ∀ c : (H.event i).RetainedBoundaryIndex,
      (H.event i).PresentedStaticCap parameters.fixed D m ε c)
    (hcanonical : ∀ c, (S c).hasCanonicalWindow)
    (hε : ε ≤ 1 / 2) (hD : StandardCap.transitionEnd + 10 < D)
    (hEndpoint : ∀ (pole : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t pole rTerm →
      ∀ (L : ℝ) (q : (H.stage i.succ).Carrier),
        L ∈ H.regularizedC1ActionValues i.succ (H.activeStage t) hactive.symm.le
          t.val 0 0 pole q →
        L ≤ Aact →
        ∀ c : (H.event i).RetainedBoundaryIndex,
          q ∉ (S c).window ''
            {z : standardCapWindow D | ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) :
    ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
    ∃ O z : (H.event i).old,
      O.val.val = seedTrace.point i.castSucc hfSeed
        (i.castSucc_le_succ.trans hactive.symm.le) ∧
      HEq ((H.event i).oldOutput O) p ∧ HEq ((H.event i).oldOutput z) x ∧
      (∀ c, (H.event i).oldOutput O ∉ (S c).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ c, (H.event i).oldOutput z ∉ (S c).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      riemannianEDistOf (H.event i).terminal.metric
        ((H.event i).oldTerminal O) ((H.event i).oldTerminal z) ≤
      riemannianEDistOf (H.event i).outputMetric
        ((H.event i).oldOutput O) ((H.event i).oldOutput z) := by
  classical
  have hZeroActionAt (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage t)
      (hjl : j ≤ H.activeStage t) :
      ∃ y : (H.stage j).Carrier,
        (0 : ℝ) ∈ H.regularizedC1ActionValues j (H.activeStage t) hjl t.val 0 0 x y := by
    subst j
    refine ⟨x, (H.mem_regularizedC1ActionValues_self (H.activeStage t) x x).mpr ?_⟩
    have hupper : t.val - (0 : ℝ) ^ 2 ∈
        Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) := by
      simpa only [zero_pow two_ne_zero, sub_zero] using
        (show t.val ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) from
          ⟨H.activeStage_time_le t, H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩)
    have hpast : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
      simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t
    exact ⟨le_rfl, le_rfl, hupper, hpast, (fun _ => x), contMDiff_const,
      IntervalIntegrable.refl, rfl, rfl, by
        simp only [stageRegularizedAction, intervalIntegral.integral_same]⟩
  obtain ⟨_y, hZeroAction⟩ := hZeroActionAt i.succ hactive.symm hactive.symm.le
  rcases hZeroAction with ⟨_hu, _hv, _hupper, _hpast, gamma, hC1, hInt,
    hterminal, _hEnd, hNodes, hSum⟩
  have hAact : 0 ≤ Aact := (by positivity : 0 ≤ 3 * r).trans hseedBudget
  have hsmall : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val 0 j.val)) ≤ Aact := hSum.trans_le hAact
  have hevent : t.val - (0 : ℝ) ^ 2 = H.time i.succ := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hbirth
  obtain ⟨hfSeed, O, z, hOin, hOout, hzout, hOoutside, hzoutside⟩ :=
    H.exists_old_seed_and_endpoint_outside_retained_cap_windows_of_nonneg_clock
      parameters records t p x r 0 Aact rTerm hr le_rfl
      (by rw [zero_pow two_ne_zero]; positivity) hseed
      hrTerm hrTermLe htest hseedBudget aSeed hSeedTime hSeedClock seedTrace htrace
      i hactive.symm.le hevent S hcanonical hEndpoint gamma hC1 hInt hterminal hNodes hsmall
  have hSeedEndpoint (j : Fin (H.eventCount + 1))
      (hjf : H.activeStage aSeed ≤ j) (hjl : j ≤ H.activeStage t)
      (hj : j = H.activeStage t) : HEq (seedTrace.point j hjf hjl) p := by
    subst j
    exact heq_of_eq seedTrace.endpoint_eq
  have hO : HEq ((H.event i).oldOutput O) p :=
    (heq_of_eq hOout).trans (hSeedEndpoint i.succ
      (hfSeed.trans i.castSucc_le_succ) hactive.symm.le hactive.symm)
  have hJ : (⟨i.succ, le_rfl, hactive.symm.le⟩ :
      H.StageInterval i.succ (H.activeStage t)) =
      ⟨H.activeStage t, hactive.symm.le, le_rfl⟩ := Subtype.ext hactive.symm
  have hGammaHEq (j k : H.StageInterval i.succ (H.activeStage t)) (hjk : j = k) :
      HEq (gamma j 0) (gamma k 0) := by
    cases hjk
    rfl
  have hz : HEq ((H.event i).oldOutput z) x :=
    (heq_of_eq hzout).trans ((hGammaHEq _ _ hJ).trans (heq_of_eq hterminal))
  exact ⟨hfSeed, O, z, hOin, hO, hz, hOoutside, hzoutside,
    (H.event i).oldTerminal_edist_le_of_outside_canonical_cap_windows S
      (records i).old_eq_retained hcanonical hε hD O z hOoutside hzoutside⟩


/-- The first incoming-stage continuation keeps the selected request, actual birth
cap family, full trace and original weighted infimum. Clock zero is reached by
the genuine right limit; all continuation strips have positive entry clocks. -/
theorem distinct_pole_birth_minimum_receives_first_incoming_stage
    (a₀ c : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hRequest : (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2))
    (hWindow : (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
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
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ req.2.2.2 →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ req.2.2.2) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ (StandardCap.transitionEnd + 10)}
      ))
    (hSupport :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
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
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
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
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hrecenter : parameters.recenterConstant ≤ c)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val)
    (hseed : H.isParabolicallyRmControlledBall t p r)
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r))
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (poleEvent : Fin H.eventCount) (hactive : H.activeStage t = poleEvent.succ)
    (hbirth : t.val = H.time poleEvent.succ)
    (b Aact E rTerm qDeriv radiusCap : ℝ)
    (hb : 0 < b) (hhalf : b ^ 2 ≤ r ^ 2 / 2)
    (hage : H.time poleEvent.castSucc < t.val - b ^ 2)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (hRadiusCap : 0 < radiusCap) (hbE : b ≤ E) (hrTermLe : rTerm ≤ r)
    (hPoleTest : H.isParabolicallyRmControlledBall t x rTerm)
    (hfit : (Real.exp (DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40) / 2 +
        32 / Real.sqrt 2) + 1) * r ≤ Aact)
    (hdelta : parameters.delta (H.time poleEvent.succ) ≤
      (request Aact E rTerm qDeriv radiusCap).2.2.2)
    (hRadius : parameters.neckRadius (H.time poleEvent.succ) ≤ radiusCap)
    {Dcap εcap : ℝ} {mcap : ℕ}
    (caps : ∀ j : (H.event poleEvent).RetainedBoundaryIndex,
      (H.event poleEvent).PresentedStaticCap parameters.fixed Dcap mcap εcap j)
    (hDcap : (request Aact E rTerm qDeriv radiusCap).2.1 ≤ Dcap)
    (hmcap : (request Aact E rTerm qDeriv radiusCap).2.2.1 ≤ mcap)
    (hεcap : εcap ≤ (request Aact E rTerm qDeriv radiusCap).1)
    (hcanonical : ∀ j, (caps j).hasCanonicalWindow)
    (hscale : ∀ j, (caps j).neck.scale = ((records poleEvent).static j).neck.scale) :
    ∃ hfSeed : H.activeStage aSeed ≤ poleEvent.castSucc,
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
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) ∧
    let hle := poleEvent.castSucc_le_succ.trans hactive.symm.le
    let O := seedTrace.point poleEvent.castSucc hfSeed hle
    ∀ w ∈ Ioc (0 : ℝ) b, ∃ y : (H.stage poleEvent.castSucc).Carrier,
      M w = H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
        t.val (3 / a₀) r A w x O y ∧
      ∀ z : (H.stage poleEvent.castSucc).Carrier,
        H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
          t.val (3 / a₀) r A w x O y ≤
        H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
          t.val (3 / a₀) r A w x O z := by
  classical
  let C0 := DifferentialGeometry.Analysis.SingularBarrier.bound
    (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
  have hC0 : 0 ≤ C0 := by
    apply DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg
    nlinarith only [hA, sq_nonneg DifferentialGeometry.Analysis.CutoffProfile.derivBound]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hDiv : (1 : ℝ) ≤ 32 / Real.sqrt 2 := by
    apply (le_div_iff₀ hsqrt).mpr
    nlinarith only [hsqrt2, sq_nonneg (Real.sqrt 2 - 1)]
  have hExponent : 1 ≤ C0 / 2 + 32 / Real.sqrt 2 := by
    linarith only [hC0, hDiv]
  have hD3 : 3 ≤ Real.exp (C0 / 2 + 32 / Real.sqrt 2) + 1 := by
    have hh := Real.add_one_le_exp (C0 / 2 + 32 / Real.sqrt 2)
    linarith only [hExponent, hh]
  have hseedBudget : 3 * r ≤ Aact :=
    (mul_le_mul_of_nonneg_right hD3 hr.le).trans hfit
  obtain ⟨_hεreq, hεhalf, _hRreq, hRbirth, _hmreq, _hδreq⟩ :=
    hRequest Aact E rTerm qDeriv radiusCap hE hrTerm hqDeriv hRadiusCap
  have hε : εcap ≤ 1 / 2 := hεcap.trans hεhalf
  have hD : StandardCap.transitionEnd + 10 < Dcap := hRbirth.trans_le hDcap
  have htrace : seedTrace.isRmControlled (hat := hSeedTime) r := by
    obtain ⟨_hr, aSeed', _hSeedTime', hSeedClock', hSeedTraces⟩ := hseed
    have haSeed : aSeed' = aSeed := Subtype.ext (hSeedClock'.trans hSeedClock.symm)
    subst aSeed'
    have hpball : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
      change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal r
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr
    obtain ⟨trace, hcontrol⟩ := hSeedTraces p hpball
    have heq : trace = seedTrace := Subsingleton.elim _ _
    simpa only [heq] using hcontrol
  have hLater (j : Fin H.eventCount) (hj : poleEvent.succ ≤ j.castSucc)
      (hjt : j.succ ≤ H.activeStage t) : False :=
    (not_lt_of_ge ((hjt.trans hactive.le).trans hj)) j.castSucc_lt_succ
  have hDerivative : ∀ j : Fin (H.eventCount + 1), poleEvent.succ ≤ j → j ≤ H.activeStage t →
      ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
        qDeriv < metricScalarAt (H.stageMetric j s) y →
        |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
          Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2 := by
    intro j hij _hjt _y s hs hsT _hQ
    have htime : t.val ≤ H.time j := by
      rw [hbirth]
      exact H.time_strictMono.monotone hij
    exact ((not_lt_of_ge hsT) (htime.trans_lt hs.1)).elim
  have hEndpoint : ∀ (pole : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t pole rTerm →
      ∀ (L : ℝ) (q : (H.stage poleEvent.succ).Carrier),
        L ∈ H.regularizedC1ActionValues poleEvent.succ (H.activeStage t) hactive.symm.le
          t.val 0 0 pole q → L ≤ Aact →
        ∀ b : (H.event poleEvent).RetainedBoundaryIndex,
          q ∉ (caps b).window ''
            {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
    intro pole hpole L q hAction hSmall b
    rcases hAction with ⟨_hu, _hv, _hupper, hpast, gamma, hC1, hInt,
      hterminal, hEnd, hNodes, hSum⟩
    have hstart : t.val - (0 : ℝ) ^ 2 ≤ H.time poleEvent.succ := by
      simpa only [zero_pow two_ne_zero, sub_zero] using hbirth.le
    have h := hWindow Aact E rTerm qDeriv radiusCap hE hrTerm hqDeriv hRadiusCap
      H parameters records hfixed hscalar t poleEvent.succ hactive.symm.le 0 le_rfl hE hpast
      pole hpole gamma hC1 hInt hterminal hNodes (hSum.trans_le hSmall)
      poleEvent le_rfl hactive.symm.le hstart hrecenter hdelta hRadius
      (by intro j hj hjt; exact (hLater j hj hjt).elim) hDerivative
      b Dcap εcap mcap (caps b) hDcap hmcap hεcap (hcanonical b) (hscale b)
    simpa only [← hbirth, sub_self, Real.sqrt_zero, hEnd] using h
  obtain ⟨hfSeed, Oold, xold, _hOin, hO, hx, hOoutside, hxoutside, _hDistance⟩ :=
    actual_zero_clock_pair_receives_no_shortcut H parameters records t p x r Aact rTerm
      hr hseed hrTerm hrTermLe hPoleTest hseedBudget aSeed hSeedTime hSeedClock seedTrace htrace
      poleEvent hactive hbirth caps hcanonical hε hD hEndpoint
  refine ⟨hfSeed, ?_⟩
  intro C M m f
  let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
  let guard := 2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2)
  let hle := poleEvent.castSucc_le_succ.trans hactive.symm.le
  let O := seedTrace.point poleEvent.castSucc hfSeed hle
  obtain ⟨_hinitialMinima, hfiniteNear, hlimit⟩ :=
    H.exists_distinct_pole_initial_weighted_minimum_and_limit_at_birth parameters records
      ha₀ hfixed hscalar aSeed t hSeedTime p x r rTerm A hr hA hSeedClock seedTrace hPoleTest hT
      poleEvent hactive hbirth caps hcanonical hε hD Oold xold hO hx hOoutside hxoutside hdist
  have hexp : Continuous (fun w : ℝ =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r)) := by fun_prop
  have hexpLimit : Tendsto (fun w : ℝ => Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [zero_pow two_ne_zero, mul_zero, zero_div, sub_zero, Real.exp_zero] using
      (hexp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun w : ℝ => Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-C * (0 : ℝ) ^ 2 / r ^ 2 - 32 * 0 / r))))
  have hfLimit : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
    have hh := hexpLimit.mul hlimit
    convert hh using 1
    · funext w
      dsimp only [f, m, M]
      ring
    · simp only [one_mul]
  have hcancelGuard : Real.exp (C / 2 + 32 / Real.sqrt 2) *
      Real.exp (-C / 2 - 32 / Real.sqrt 2) = 1 := by
    rw [← Real.exp_add,
      show (C / 2 + 32 / Real.sqrt 2) + (-C / 2 - 32 / Real.sqrt 2) = 0 by ring,
      Real.exp_zero]
  have hguard : 2 * r < guard := by
    have hformula : guard = 2 * r + 2 * r * Real.exp (-C / 2 - 32 / Real.sqrt 2) := by
      dsimp only [guard, D]
      calc
        2 * r * (Real.exp (C / 2 + 32 / Real.sqrt 2) + 1) *
            Real.exp (-C / 2 - 32 / Real.sqrt 2) =
            2 * r * (Real.exp (C / 2 + 32 / Real.sqrt 2) *
              Real.exp (-C / 2 - 32 / Real.sqrt 2)) +
              2 * r * Real.exp (-C / 2 - 32 / Real.sqrt 2) := by ring
        _ = 2 * r + 2 * r * Real.exp (-C / 2 - 32 / Real.sqrt 2) := by
          rw [hcancelGuard, mul_one]
    rw [hformula]
    exact lt_add_of_pos_right _ (mul_pos (mul_pos (by norm_num) hr) (Real.exp_pos _))
  have hsmallNear : ∀ᶠ w in 𝓝[>] (0 : ℝ), f w < guard :=
    hfLimit.eventually (Iio_mem_nhds hguard)
  have hnodeIndex (j : Fin H.eventCount)
      (hf : poleEvent.castSucc ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t) :
      j = poleEvent := by
    apply Fin.ext
    have hh := hl.trans hactive.le
    change j.val + 1 ≤ poleEvent.val + 1 at hh
    change poleEvent.val ≤ j.val at hf
    omega
  have hstage (a : ℝ) (ha : 0 < a) (hab : a ≤ b)
      (hfinite : M a ≠ ⊤) (hsmall : f a < guard) :
      (∀ w ∈ Icc a b, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D) ∧
        AntitoneOn f (Icc a b) ∧
        ∀ w ∈ Icc a b, ∃ y : (H.stage poleEvent.castSucc).Carrier,
          M w = H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
            t.val (3 / a₀) r A w x O y ∧
          ∀ z : (H.stage poleEvent.castSucc).Carrier,
            H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
              t.val (3 / a₀) r A w x O y ≤
            H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
              t.val (3 / a₀) r A w x O z := by
    have hclock (w : ℝ) (hw : w ∈ Icc a b) :
        t.val - w ^ 2 ∈ Ioo (H.time poleEvent.castSucc) (H.stageEndTime poleEvent.castSucc) := by
      have hw0 : 0 < w := ha.trans_le hw.1
      have hsq := (sq_le_sq₀ hw0.le hb.le).mpr hw.2
      constructor
      · linarith only [hage, hsq]
      · rw [H.stageEndTime_castSucc, ← hbirth]
        exact sub_lt_self _ (sq_pos_of_pos hw0)
    have hentry : WithTop.map
        (fun z : ℝ => Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * z / a) (M a) <
        (guard : WithTop ℝ) := by
      obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hfinite
      rw [← hvalue, WithTop.map_coe]
      apply WithTop.coe_lt_coe.mpr
      simpa only [f, m, ← hvalue, WithTop.untopD_coe] using hsmall
    have hs := distinct_pole_weighted_infimum_antitone_on_regular_stage_at_closed_poles
      a₀ c Cderiv ha₀ request hSupport H parameters records hrecenter hfixed hscalar
      t p x r A hr hA hT hseed aSeed hSeedTime hSeedClock seedTrace
      poleEvent.castSucc hfSeed hle a b ha hab hhalf hclock
      (fun _ => Aact) (fun _ => E) (fun _ => rTerm) (fun _ => qDeriv) (fun _ => radiusCap)
      (by
        intro j hf hl
        have hj := hnodeIndex j hf hl
        subst j
        exact ⟨hE, hrTerm, hqDeriv, hRadiusCap, hbE, hPoleTest, hdelta, hRadius,
          (by intro j hj hjt; exact (hLater j hj hjt).elim), hDerivative,
          fun z => ⟨Dcap, εcap, mcap, caps z, hDcap, hmcap, hεcap, hcanonical z, hscale z⟩⟩)
      (by intro _j _hf _hl; exact hfit) hentry
    exact ⟨hs.1, hs.2.2.1, hs.2.2.2.2⟩
  have hall (w : ℝ) (hw : w ∈ Ioc (0 : ℝ) b) : M w ≠ ⊤ ∧ 0 ≤ m w := by
    obtain ⟨a, hfinite, hsmall, ha⟩ :=
      (hfiniteNear.and (hsmallNear.and (Ioo_mem_nhdsGT hw.1))).exists
    have hs := hstage a ha.1 (ha.2.le.trans hw.2) hfinite hsmall
    exact ⟨(hs.1 w ⟨ha.2.le, hw.2⟩).1, (hs.1 w ⟨ha.2.le, hw.2⟩).2.1⟩
  have hfanti : AntitoneOn f (Ioc (0 : ℝ) b) := by
    intro u hu v hv huv
    obtain ⟨a, hfinite, hsmall, ha⟩ :=
      (hfiniteNear.and (hsmallNear.and (Ioo_mem_nhdsGT hu.1))).exists
    have hs := hstage a ha.1 (ha.2.le.trans hu.2) hfinite hsmall
    exact hs.2.1 ⟨ha.2.le, hu.2⟩ ⟨ha.2.le.trans huv, hv.2⟩ huv
  have hfBound (w : ℝ) (hw : w ∈ Ioc (0 : ℝ) b) : f w ≤ 2 * r := by
    apply ge_of_tendsto hfLimit
    filter_upwards [hfiniteNear, hsmallNear, Ioo_mem_nhdsGT hw.1]
      with a hfinite hsmall ha
    have hs := hstage a ha.1 (ha.2.le.trans hw.2) hfinite hsmall
    exact hs.2.1 ⟨le_rfl, ha.2.le.trans hw.2⟩ ⟨ha.2.le, hw.2⟩ ha.2.le
  refine ⟨?_, hfanti, hfBound, hlimit, hfLimit, ?_⟩
  · intro w hw
    refine ⟨(hall w hw).1, (hall w hw).2, ?_⟩
    have hh : Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w ≤ 2 * r * w :=
      (div_le_iff₀ hw.1).mp (hfBound w hw)
    have hcancel : Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) *
        Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) = 1 := by
      rw [← Real.exp_add, show (C * w ^ 2 / r ^ 2 + 32 * w / r) +
        (-C * w ^ 2 / r ^ 2 - 32 * w / r) = 0 by ring, Real.exp_zero]
    have hmul := mul_le_mul_of_nonneg_left hh
      (Real.exp_pos (C * w ^ 2 / r ^ 2 + 32 * w / r)).le
    have hm : m w ≤ Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) * (2 * r * w) := by
      simpa only [← mul_assoc, hcancel, one_mul] using hmul
    simpa only [mul_comm] using hm
  · change ∀ w ∈ Ioc (0 : ℝ) b, ∃ y : (H.stage poleEvent.castSucc).Carrier,
        M w = H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
          t.val (3 / a₀) r A w x O y ∧
        ∀ z : (H.stage poleEvent.castSucc).Carrier,
          H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
            t.val (3 / a₀) r A w x O y ≤
          H.physicalWeightedCost poleEvent.castSucc (H.activeStage t) hle
            t.val (3 / a₀) r A w x O z
    intro w hw
    obtain ⟨a, hfinite, hsmall, ha⟩ :=
      (hfiniteNear.and (hsmallNear.and (Ioo_mem_nhdsGT hw.1))).exists
    have hs := hstage a ha.1 (ha.2.le.trans hw.2) hfinite hsmall
    exact hs.2.2 w ⟨ha.2.le, hw.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
