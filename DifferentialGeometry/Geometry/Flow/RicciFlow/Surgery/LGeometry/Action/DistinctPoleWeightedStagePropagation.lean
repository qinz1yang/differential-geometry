import DifferentialGeometry.Analysis.Calculus.UpperSupport.WithTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedStageAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventLocalWeightedTemporalSupport
import DifferentialGeometry.Topology.Order.Semicontinuity

/-!
# S-CH11-FIX11 patched-at-path `DistinctPoleWeightedStagePropagation`

来源：donor `DistinctPoleWeightedStagePropagation.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；下游模块对本路径 `open private … from`，
所以修补文本就放在原路径（patched-at-path）。只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `open private lowerSemicontinuous_variable_positive_affine_map from
  …PhysicalWeightedSemicontinuity` → `…PhysicalWeightedSemicontinuityPortC11P`
  （原路径已是 port + shim，private 名住在 PortC11P）；
* 陈述里的 `ℝ≥0`（`Cderiv`）需要 `open scoped NNReal`（donor 漏开，`LE Type / OfNat Type 0` ×5）→
  在已有的 `open scoped` 行补上 `NNReal`；
* `hStageLsc w hw bound (by rw [← hMstage w hw]; exact hbound)` / `hElsc … (by rw [hEcoe …] …)`：
  `by` 的目标是 β-redex `(fun x1 x2 ↦ … > x2) w bound`，`rw` 找不到 `Mstage w` / `E w` → 先
  `change bound < Mstage w` / `change (bound : WithTop ℝ) < E w`；
* `hElsc`：`convert hh using 1; funext w; …` 的 `funext` 不适用（convert 已逐点化）→ 显式函数等式
  `hfun : (fun w : Icc a b => E w.val) = fun w => WithTop.map (… + 0) (M w.val)`，`change` +
  `rw [hfun]; exact hh`；
* `hEsupport`：`rw [hfirst] at hs` "motive is not type correct"（`hs` 里 `seedTrace.point first ⋯ hle`
  的证明项类型含 `H.activeStage aw`）→ 先让 `aw` 不依赖 `first`（`aw` 的 `Icc` 证明改用
  `aSeed.property.1.trans hsw`），再 `subst hfirst`，`hs := hSupport aw … rfl hpast` 直接匹配，
  删去 `rw [hfirst] at hs` 与 `simpa only [hfirst] using hpast`；
* `mul_le_mul_right … |>.mp`（本树 `mul_le_mul_right` 是单调性引理）→ `le_of_mul_le_mul_right ?_ (mul_pos …)`；
* calc 第一步 `rw [Real.exp_add]; ring`：`rw` 实例化到 LHS 的 `exp (a + b)`，RHS 的
  `exp ((a + b) + c)` 没拆 → 显式
  `Real.exp_add (C * w ^ 2 / r ^ 2 + 32 * w / r) (-C / 2 - 32 / Real.sqrt 2)`；
* 末尾 `field_simp` 已关目标，多余的 `ring` "No goals"（坑 xiii）→ 删；
* 8 个陈述 binder `hf` / `hl` / `hb` 不被引用 → `_hf` / `_hl` / `_hb`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open private lowerSemicontinuous_variable_positive_affine_map from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedSemicontinuityPortC11P

private theorem weighted_infimum_antitone_on_fixed_regular_stage
    (a₀ : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ)
    (hr : 0 < r) (hA : 1 ≤ A) (hT : 2 * r ^ 2 < t.val)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hSupport :
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
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (first : Fin (H.eventCount + 1))
      (hseedfirst : H.activeStage aSeed ≤ first) (hle : first ≤ H.activeStage t)
      (a b : ℝ), 0 < a → a ≤ b → b ^ 2 ≤ r ^ 2 / 2 →
      (∀ w ∈ Icc a b,
        t.val - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) →
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ b ≤ nodeE i ∧
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
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        D * r ≤ nodeA i) →
    let O := seedTrace.point first hseedfirst hle
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    WithTop.map (fun z : ℝ => Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * z / a)
        (M a) < ((2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2) : ℝ) : WithTop ℝ) →
    (∀ w ∈ Icc a b, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D) ∧
    LowerSemicontinuousOn f (Icc a b) ∧ AntitoneOn f (Icc a b) ∧
    (∀ w ∈ Icc a b,
      m w ≤ Real.exp (C * (w ^ 2 - a ^ 2) / r ^ 2 + 32 * (w - a) / r) *
        (w / a) * m a) ∧
    ∀ w ∈ Icc a b, ∃ q : (H.stage first).Carrier,
      M w = H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O q ∧
      ∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O q ≤
          H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O y := by
  classical
  intro C D first hseedfirst hle a b ha hab hb hclock
    nodeA nodeE nodeR nodeQ nodeRho hnode hfit O M m f hentry
  let last := H.activeStage t
  let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
    (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hhalf (w : ℝ) (hw : w ∈ Icc a b) : w ^ 2 ≤ r ^ 2 / 2 :=
    (pow_le_pow_left₀ (ha.le.trans hw.1) hw.2 2).trans hb
  have hC : 0 ≤ C := by
    apply DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg
    nlinarith only [hA, sq_nonneg DifferentialGeometry.Analysis.CutoffProfile.derivBound]
  have hD : 0 < D := by dsimp only [D]; positivity
  have hMstage (w : ℝ) (hw : w ∈ Icc a b) : M w = Mstage w := by
    have hpast := hclock w hw
    let aw : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - w ^ 2, H.stageDomain_subset first (H.mem_stageDomain_of_mem_Ioo hpast)⟩
    have hawt : aw ≤ t := sub_le_self t.val (sq_nonneg w)
    have hsw : (aSeed : ℝ) ≤ t.val - w ^ 2 := by
      rw [hSeedClock]
      nlinarith only [hhalf w hw, hr2]
    have hawseed : aSeed ≤ aw := hsw
    have hstage : H.activeStage aw = first :=
      (H.mem_stageDomain_iff aw first).mp (H.mem_stageDomain_of_mem_Ioo hpast)
    have hwhole (j : Fin (H.eventCount + 1))
        (hjs : H.activeStage aSeed ≤ j) (hjl : j ≤ last) (hj : j = first) :
        sInf (Set.range (H.physicalWeightedCost j last hjl t.val (3 / a₀) r A w x
          (seedTrace.point j hjs hjl))) = Mstage w := by
      subst j
      rfl
    dsimp only [M, tracedPhysicalWeightedMinimum]
    rw [dite_eq_left hsw]
    exact hwhole (H.activeStage aw) (H.activeStage_mono hawseed)
      (H.activeStage_mono hawt) hstage
  obtain ⟨hStageLsc, hStageNonneg⟩ :=
    H.lowerSemicontinuousOn_sInf_physicalWeightedCost_of_cutoff_records
      parameters records ha₀ hfixed hscalar first last hle t.val r A a b hr ha hab hb hT
      (H.activeStage_mem t) hclock x O
  have hMin := H.physicalWeightedCost_minima_on_half_clock_of_cutoff_records
    parameters records ha₀ hfixed hscalar first last hle t.val r A a b hr ha hab hb hT
    (H.activeStage_mem t) hclock x O
  have hMlsc : LowerSemicontinuousOn M (Icc a b) := by
    intro w hw bound hbound
    have hh := hStageLsc w hw bound
      (by change bound < Mstage w; rw [← hMstage w hw]; exact hbound)
    filter_upwards [hh, self_mem_nhdsWithin] with z hz hzab
    rw [hMstage z hzab]
    exact hz
  have hMnonneg (w : ℝ) (hw : w ∈ Icc a b) : (0 : WithTop ℝ) ≤ M w := by
    rw [hMstage w hw]
    exact hStageNonneg w hw
  let E : ℝ → WithTop ℝ := fun w => WithTop.map
    (fun z : ℝ => Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * z / w) (M w)
  let guard := 2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2)
  have hfactor : Continuous (fun w : Icc a b =>
      Real.exp (-C * w.val ^ 2 / r ^ 2 - 32 * w.val / r) / w.val) := by
    apply Continuous.div
    · exact Real.continuous_exp.comp
        (((continuous_const.mul (continuous_subtype_val.pow 2)).div_const _).sub
          ((continuous_const.mul continuous_subtype_val).div_const _))
    · exact continuous_subtype_val
    · intro w
      exact (ha.trans_le w.property.1).ne'
  have hElsc : LowerSemicontinuousOn E (Icc a b) := by
    apply lowerSemicontinuous_restrict_iff.mp
    have hsub : LowerSemicontinuous (fun w : Icc a b => M w.val) :=
      lowerSemicontinuous_restrict_iff.mpr hMlsc
    have hh := lowerSemicontinuous_variable_positive_affine_map
      (fun w : Icc a b => M w.val) hsub
      (fun w : Icc a b => Real.exp (-C * w.val ^ 2 / r ^ 2 - 32 * w.val / r) / w.val)
      (fun _ : Icc a b => (0 : ℝ)) hfactor continuous_const
      (fun w => div_pos (Real.exp_pos _) (ha.trans_le w.property.1))
    have hfun : (fun w : Icc a b => E w.val) = fun w : Icc a b =>
        WithTop.map (fun y : ℝ =>
          Real.exp (-C * w.val ^ 2 / r ^ 2 - 32 * w.val / r) / w.val * y + 0) (M w.val) := by
      funext w
      dsimp only [E]
      congr 1
      funext z
      ring
    change LowerSemicontinuous (fun w : Icc a b => E w.val)
    rw [hfun]
    exact hh
  have hEcoe (w : ℝ) (hfinite : M w ≠ ⊤) : E w = (f w : WithTop ℝ) := by
    obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hfinite
    dsimp only [E, f, m]
    rw [← hvalue, WithTop.map_coe, WithTop.untopD_coe]
  have hbelow (w : ℝ) (hw : w ∈ Icc a b) (hsmall : E w < (guard : WithTop ℝ)) :
      M w ≠ ⊤ ∧ m w < 2 * r * w * D := by
    have hw0 : 0 < w := ha.trans_le hw.1
    have hfinite : M w ≠ ⊤ := by
      intro htop
      have hh : E w = ⊤ := by simp only [E, htop, WithTop.map_top]
      exact (ne_top_of_lt hsmall) hh
    have hreal : Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w < guard := by
      rw [hEcoe w hfinite] at hsmall
      exact WithTop.coe_lt_coe.mp hsmall
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hwr : w / r ≤ 1 / Real.sqrt 2 := by
      apply (div_le_div_iff₀ hr hsqrt).mpr
      have hsq : (w * Real.sqrt 2) ^ 2 ≤ r ^ 2 := by
        rw [mul_pow, hsqrt2]
        nlinarith only [hhalf w hw]
      simpa only [one_mul] using
        (sq_le_sq₀ (mul_nonneg hw0.le hsqrt.le) hr.le).mp hsq
    have hquad : C * w ^ 2 / r ^ 2 ≤ C / 2 := by
      apply (div_le_iff₀ hr2).mpr
      have hh := mul_le_mul_of_nonneg_left (hhalf w hw) hC
      nlinarith only [hh]
    have hlin : 32 * w / r ≤ 32 / Real.sqrt 2 := by
      simpa only [← mul_div_assoc, mul_one] using
        mul_le_mul_of_nonneg_left hwr (by norm_num : (0 : ℝ) ≤ 32)
    have hchi : C * w ^ 2 / r ^ 2 + 32 * w / r ≤ C / 2 + 32 / Real.sqrt 2 :=
      add_le_add hquad hlin
    have hfactorBound :
        Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) * guard ≤ 2 * r * D := by
      dsimp only [guard]
      calc
        Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) *
            (2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2)) =
            (2 * r * D) * Real.exp
              ((C * w ^ 2 / r ^ 2 + 32 * w / r) + (-C / 2 - 32 / Real.sqrt 2)) := by
          rw [Real.exp_add (C * w ^ 2 / r ^ 2 + 32 * w / r) (-C / 2 - 32 / Real.sqrt 2)]
          ring
        _ ≤ (2 * r * D) * Real.exp 0 := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hchi]))
          positivity
        _ = 2 * r * D := by rw [Real.exp_zero, mul_one]
    have hcancel : Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) *
        Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) = 1 := by
      rw [← Real.exp_add, show (C * w ^ 2 / r ^ 2 + 32 * w / r) +
        (-C * w ^ 2 / r ^ 2 - 32 * w / r) = 0 by ring, Real.exp_zero]
    have hmul := mul_lt_mul_of_pos_left ((div_lt_iff₀ hw0).mp hreal)
      (Real.exp_pos (C * w ^ 2 / r ^ 2 + 32 * w / r))
    have hm : m w <
        (Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r) * guard) * w := by
      simpa only [← mul_assoc, hcancel, one_mul] using hmul
    refine ⟨hfinite, hm.trans_le ?_⟩
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hfactorBound hw0.le
  have hEsupport (w : ℝ) (hw : w ∈ Ico a b)
      (hsmall : E w < (guard : WithTop ℝ)) :
      ∃ psi : ℝ → ℝ, ∃ d : ℝ, E w = (psi w : WithTop ℝ) ∧
        (∀ᶠ z in 𝓝[>] w, E z ≤ (psi z : WithTop ℝ)) ∧
        HasDerivAt psi d w ∧ d ≤ 0 := by
    have hwab : w ∈ Icc a b := Ico_subset_Icc_self hw
    have hw0 : 0 < w := ha.trans_le hw.1
    obtain ⟨hfinite, hbudget⟩ := hbelow w hwab hsmall
    obtain ⟨q, hMvalue, hminimum⟩ := hMin w hwab
    have hglobalValue : M w =
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O q :=
      (hMstage w hwab).trans hMvalue
    have hMcoe : (m w : WithTop ℝ) = M w := by
      obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hfinite
      dsimp only [m]
      rw [← hvalue, WithTop.untopD_coe]
    have hbootstrap : H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O q ≤
        ((2 * r * w * D : ℝ) : WithTop ℝ) := by
      rw [← hglobalValue, ← hMcoe]
      exact WithTop.coe_le_coe.mpr hbudget.le
    have hpast := hclock w hwab
    have hsw : (aSeed : ℝ) ≤ t.val - w ^ 2 := by
      rw [hSeedClock]
      nlinarith only [hhalf w hwab, hr2]
    let aw : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - w ^ 2, aSeed.property.1.trans hsw,
        (sub_le_self t.val (sq_nonneg w)).trans t.property.2⟩
    have hawt : aw ≤ t := sub_le_self t.val (sq_nonneg w)
    have haws : aSeed ≤ aw := hsw
    have hfirst : H.activeStage aw = first :=
      (H.mem_stageDomain_iff aw first).mp (H.mem_stageDomain_of_mem_Ioo hpast)
    -- `aw` no longer depends on `first`, so the receiving callback can be moved by `subst`
    -- (its carrier, metric, trace point and every node binder move together).
    subst hfirst
    have hs := hSupport aw haws hawt w hw0 (hhalf w hwab) rfl hpast
    dsimp only at hs
    obtain ⟨_L, _hcost, _hLbound, _hLact, _hinside,
        gamma, _hgamma, _hgammaAC, _hgammaInt, _hstart, hEnd,
        _hnodes, _hattain, _hcross, U, F, _hU, _hqU, _hFC2, _hFcontact,
        _hupper, _hgradient, _hclockJet, _hlap, _hfiniteSupport, _hlocalMin,
        W, _hWcontact, _hWspace, _hWtime, _hWmin, _hWdiff, _hWlap, _hWheat,
        _hStage, _hMv, _hmv, hNear, psi, d, hpsiContact, hpsiUpper, hpsiDeriv, hd⟩ :=
      hs nodeA nodeE nodeR nodeQ nodeRho
        (by
          intro i hf hl
          obtain ⟨hE, hR, hQ, hRho, hbE, hrest⟩ := hnode i hf hl
          exact ⟨hE, hR, hQ, hRho, hw.2.le.trans hbE, hrest⟩)
        hfit q hminimum hbootstrap
    refine ⟨psi, d, ?_, ?_, hpsiDeriv, hd⟩
    · rw [hEcoe w hfinite]
      exact congrArg (fun z : ℝ => (z : WithTop ℝ)) hpsiContact.symm
    · filter_upwards [hNear.filter_mono nhdsWithin_le_nhds, hpsiUpper] with z hz hupper
      rw [hEcoe z hz.1]
      exact WithTop.coe_le_coe.mpr hupper
  obtain ⟨hEanti, hEguard⟩ :=
    WithTop.antitoneOn_of_lowerSemicontinuousOn_of_upper_support_below
      E a b guard hElsc hentry hEsupport
  have hall (w : ℝ) (hw : w ∈ Icc a b) : M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D := by
    obtain ⟨hfinite, hbound⟩ := hbelow w hw (hEguard w hw)
    have hh := hMnonneg w hw
    obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hfinite
    rw [← hvalue] at hh
    refine ⟨hfinite, ?_, hbound⟩
    simpa only [m, ← hvalue, WithTop.untopD_coe] using WithTop.coe_le_coe.mp hh
  have hfLsc : LowerSemicontinuousOn f (Icc a b) := by
    intro w hw bound hbound
    have hh := hElsc w hw (bound : WithTop ℝ) (by
      change (bound : WithTop ℝ) < E w
      rw [hEcoe w (hall w hw).1]
      exact WithTop.coe_lt_coe.mpr hbound)
    filter_upwards [hh, self_mem_nhdsWithin] with z hz hzab
    rw [hEcoe z (hall z hzab).1] at hz
    exact WithTop.coe_lt_coe.mp hz
  have hfanti : AntitoneOn f (Icc a b) := by
    intro u hu v hv huv
    have hh := hEanti hu hv huv
    rw [hEcoe u (hall u hu).1, hEcoe v (hall v hv).1] at hh
    exact WithTop.coe_le_coe.mp hh
  refine ⟨hall, hfLsc, hfanti, ?_, ?_⟩
  · intro w hw
    have hw0 : 0 < w := ha.trans_le hw.1
    have hh := hfanti ⟨le_rfl, hab⟩ hw hw.1
    change Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w ≤
      Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * m a / a at hh
    have hmul := (div_le_div_iff₀ hw0 ha).mp hh
    have hexp : Real.exp (C * (w ^ 2 - a ^ 2) / r ^ 2 + 32 * (w - a) / r) *
        Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) =
        Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    apply le_of_mul_le_mul_right ?_
      (mul_pos (Real.exp_pos (-C * w ^ 2 / r ^ 2 - 32 * w / r)) ha)
    calc
      m w * (Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * a) =
          (Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w) * a := by ring
      _ ≤ (Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * m a) * w := hmul
      _ = (Real.exp (C * (w ^ 2 - a ^ 2) / r ^ 2 + 32 * (w - a) / r) * (w / a) * m a) *
          (Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * a) := by
        rw [← hexp]
        field_simp [ha.ne']
  · intro w hw
    obtain ⟨q, hvalue, hmin⟩ := hMin w hw
    exact ⟨q, (hMstage w hw).trans hvalue, hmin⟩


theorem distinct_pole_weighted_infimum_antitone_on_regular_stage_at_closed_poles
    (a₀ c : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
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
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (first : Fin (H.eventCount + 1))
      (hseedfirst : H.activeStage aSeed ≤ first) (hle : first ≤ H.activeStage t)
      (a b : ℝ), 0 < a → a ≤ b → b ^ 2 ≤ r ^ 2 / 2 →
      (∀ w ∈ Icc a b,
        t.val - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) →
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ b ≤ nodeE i ∧
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
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        D * r ≤ nodeA i) →
    let O := seedTrace.point first hseedfirst hle
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    WithTop.map (fun z : ℝ => Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * z / a)
        (M a) < ((2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2) : ℝ) : WithTop ℝ) →
    (∀ w ∈ Icc a b, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D) ∧
    LowerSemicontinuousOn f (Icc a b) ∧ AntitoneOn f (Icc a b) ∧
    (∀ w ∈ Icc a b,
      m w ≤ Real.exp (C * (w ^ 2 - a ^ 2) / r ^ 2 + 32 * (w - a) / r) *
        (w / a) * m a) ∧
    ∀ w ∈ Icc a b, ∃ q : (H.stage first).Carrier,
      M w = H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O q ∧
      ∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O q ≤
          H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O y := by
  refine weighted_infimum_antitone_on_fixed_regular_stage a₀ Cderiv ha₀ request
    H parameters records hfixed hscalar t p x r A hr hA hT
    aSeed hSeedTime hSeedClock seedTrace ?_
  intro _C _D a has hat v hv hhalf hclock hpast
  exact hSupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock hpast

theorem distinct_pole_weighted_infimum_antitone_on_regular_stage
    (a₀ c : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
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
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hpole : H.time (H.activeStage t) < t.val) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (first : Fin (H.eventCount + 1))
      (hseedfirst : H.activeStage aSeed ≤ first) (hle : first ≤ H.activeStage t)
      (a b : ℝ), 0 < a → a ≤ b → b ^ 2 ≤ r ^ 2 / 2 →
      (∀ w ∈ Icc a b,
        t.val - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) →
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ b ≤ nodeE i ∧
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
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        D * r ≤ nodeA i) →
    let O := seedTrace.point first hseedfirst hle
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    WithTop.map (fun z : ℝ => Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * z / a)
        (M a) < ((2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2) : ℝ) : WithTop ℝ) →
    (∀ w ∈ Icc a b, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D) ∧
    LowerSemicontinuousOn f (Icc a b) ∧ AntitoneOn f (Icc a b) ∧
    (∀ w ∈ Icc a b,
      m w ≤ Real.exp (C * (w ^ 2 - a ^ 2) / r ^ 2 + 32 * (w - a) / r) *
        (w / a) * m a) ∧
    ∀ w ∈ Icc a b, ∃ q : (H.stage first).Carrier,
      M w = H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O q ∧
      ∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O q ≤
          H.physicalWeightedCost first (H.activeStage t) hle t.val (3 / a₀) r A w x O y := by
  refine weighted_infimum_antitone_on_fixed_regular_stage a₀ Cderiv ha₀ request
    H parameters records hfixed hscalar t p x r A hr hA hT
    aSeed hSeedTime hSeedClock seedTrace ?_
  intro _C _D a has hat v hv hhalf hclock hpast
  exact hSupport H parameters records hrecenter hfixed hscalar t p x r A hr hA hT hseed
    aSeed hSeedTime hSeedClock seedTrace a has hat v hv hhalf hclock hpole hpast

theorem distinct_pole_initial_minimum_receives_pole_stage_continuation
    (a₀ c : ℝ) (Cderiv : ℝ≥0) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
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
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (rho b : ℝ) (_hb : 0 < b) (hhalf : b ^ 2 ≤ r ^ 2 / 2)
    (hage : H.time (H.activeStage t) < t.val - b ^ 2)
    (htest : H.isParabolicallyRmControlledBall t x rho)
    (hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x <
      ENNReal.ofReal (A * r)) :
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
    let m : ℝ → ℝ := fun w => (M w).untopD 0
    let f : ℝ → ℝ := fun w =>
      Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
    (∀ w ∈ Ioc (0 : ℝ) b,
      M w ≠ ⊤ ∧ 0 ≤ m w ∧
      m w ≤ 2 * r * w * Real.exp (C * w ^ 2 / r ^ 2 + 32 * w / r)) ∧
    AntitoneOn f (Ioc (0 : ℝ) b) ∧
    (∀ w ∈ Ioc (0 : ℝ) b, f w ≤ 2 * r) ∧
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (2 * r)) := by
  classical
  intro C M m f
  let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
  let guard := 2 * r * D * Real.exp (-C / 2 - 32 / Real.sqrt 2)
  have hpole : H.time (H.activeStage t) < t.val := by
    linarith only [hage, sq_nonneg b]
  obtain ⟨_hinitialMinima, hfiniteNear, hlimit⟩ :=
    H.exists_distinct_pole_initial_weighted_minimum_and_limit parameters records ha₀
      hfixed hscalar aSeed t hSeedTime p x r rho A hr hA hSeedClock seedTrace htest hT hpole hdist
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
  have hstage (a : ℝ) (ha : 0 < a) (hab : a ≤ b)
      (hfinite : M a ≠ ⊤) (hsmall : f a < guard) :
      (∀ w ∈ Icc a b, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w < 2 * r * w * D) ∧
        AntitoneOn f (Icc a b) := by
    have hclock (w : ℝ) (hw : w ∈ Icc a b) :
        t.val - w ^ 2 ∈ Ioo (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) := by
      have hw0 : 0 < w := ha.trans_le hw.1
      have hsq := pow_le_pow_left₀ hw0.le hw.2 2
      have htEnd := H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)
      constructor
      · linarith only [hage, hsq]
      · nlinarith only [htEnd, sq_pos_of_pos hw0]
    have hNoNode (i : Fin H.eventCount)
        (hf : H.activeStage t ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t) : False :=
      (not_lt_of_ge (hl.trans hf)) i.castSucc_lt_succ
    have hentry : WithTop.map
        (fun z : ℝ => Real.exp (-C * a ^ 2 / r ^ 2 - 32 * a / r) * z / a) (M a) <
        (guard : WithTop ℝ) := by
      obtain ⟨value, hvalue⟩ := WithTop.ne_top_iff_exists.mp hfinite
      rw [← hvalue, WithTop.map_coe]
      apply WithTop.coe_lt_coe.mpr
      simpa only [f, m, ← hvalue, WithTop.untopD_coe] using hsmall
    have hs := distinct_pole_weighted_infimum_antitone_on_regular_stage
      a₀ c Cderiv ha₀ request hSupport H parameters records hrecenter hfixed hscalar
      t p x r A hr hA hT hseed aSeed hSeedTime hSeedClock seedTrace hpole
      (H.activeStage t) (H.activeStage_mono hSeedTime) le_rfl a b ha hab hhalf hclock
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (by intro i hf hl; exact (hNoNode i hf hl).elim)
      (by intro i hf hl; exact (hNoNode i hf hl).elim) hentry
    exact ⟨hs.1, hs.2.2.1⟩
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
    exact hs.2 ⟨ha.2.le, hu.2⟩ ⟨ha.2.le.trans huv, hv.2⟩ huv
  have hfBound (w : ℝ) (hw : w ∈ Ioc (0 : ℝ) b) : f w ≤ 2 * r := by
    apply ge_of_tendsto hfLimit
    filter_upwards [hfiniteNear, hsmallNear, Ioo_mem_nhdsGT hw.1]
      with a hfinite hsmall ha
    have hs := hstage a ha.1 (ha.2.le.trans hw.2) hfinite hsmall
    exact hs.2 ⟨le_rfl, ha.2.le.trans hw.2⟩ ⟨ha.2.le, hw.2⟩ ha.2.le
  refine ⟨?_, hfanti, hfBound, hfLimit⟩
  intro w hw
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
