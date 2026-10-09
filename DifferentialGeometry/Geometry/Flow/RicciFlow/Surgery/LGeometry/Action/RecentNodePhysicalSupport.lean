import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AttainedPhysicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedPolePhysicalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionRecentNode
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

/-!
# S-CH11-FIX11 patched-at-path `RecentNodePhysicalSupport`

来源：donor `RecentNodePhysicalSupport.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；下游模块对本路径 `open private … from`，
所以修补文本就放在原路径（patched-at-path）。只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 首个定理 `/-- docstring -/ attribute [-instance] … in theorem` 的顺序对调（docstring 不能放在
  `attribute … in` 前面，l.25 "unexpected token 'attribute'; expected 'lemma'"）；
* 陈述里的 `ℝ≥0`（`Cderiv`）需要 `open scoped NNReal`（donor 漏开，`LE Type / OfNat Type 0`）→
  在已有的 `open scoped` 行补上 `NNReal`（4 个陈述的 synth 失败 + 级联 "Unknown identifier …
  exists_physical_cost_support_…" / `generalize` 失败都由此而来）；
* `hwindowScale`（`choose` 出来、带 `∀ {P Q a s}` 隐式 binder）的 `simpa only [request,
  dite_eq_left h] using hwindowScale …`：simpa 单独 elaborate `using` 项，隐式 binder 被 mvar 吃掉，
  与目标的 `∀ {P Q a s}` 对不上 → `simp only [request, dite_eq_left h]` 之后
  `exact @hwindowScale Aact Ebound rTerm qDeriv ρ h`；
* `obtain ⟨_, …, hcapWindow⟩ := hcanonical`：本树 rcases 会 clear 被解构的 fvar，随后 `exact
  hwindowBarrier … hcanonical …` 报 "Unknown identifier `hcanonical`" → 先 `have hcanonicalCopy :=
  hcanonical` 再解构 copy；
* 4 个陈述里 `(hf : …) (hl : …)` 在 `∀ i, hf → hl → …` 前缀里不被引用 → `_hf` / `_hl`
  （unusedVariables，共 8 处）。
* 1 处命令内空行（`linter.style.emptyLine`：`exact hwindowBarrier …` 与 `refine ⟨gamma, …⟩` 之间）→ 删掉空行。
-/

set_option autoImplicit false
noncomputable section

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Choose the requests before the histories, then keep the one original-cost
minimizer through all node exclusions and physical support constructions.
The initial scalar clock is supplied once and is never reselected. -/
theorem exists_physical_cost_support_with_event_local_cap_exclusion_requests_at_closed_poles_with_window_scale_bound
    (a₀ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (ha₀ : 0 < a₀) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ Rbirth < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2) ∧
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
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth}
      ) ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 < v →
      t.val - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) →
    ∀ (p : (H.stageAt t).Carrier)
      (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t p (nodeR i) ∧
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
    ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ≠ ⊤ →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q <
          (nodeA i : WithTop ℝ)) →
    ∃ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = p ∧
      gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first (H.activeStage t) t.val (3 / a₀) 0 v gamma =
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
    ∀ etaError : ℝ, 0 < etaError →
    let jf : H.StageInterval first (H.activeStage t) := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first (H.activeStage t) := ⟨H.activeStage t, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction x.val t.val (gamma x)
        (H.regularizedStageStart t.val 0 x.val) (H.regularizedStageEnd t.val v x.val);
    let gOriginal := H.stageMetric first (t.val - v ^ 2);
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < t.val ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (t.val - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (t.val - z.2) * F (z.1, Real.sqrt (t.val - z.2));
    IsOpen Omega ∧ (q, t.val - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, t.val - v ^ 2) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 (Real.sqrt (t.val - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (t.val - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0
        (Real.sqrt (t.val - (t.val - v ^ 2))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ 2 * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (t.val - v ^ 2) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (t.val - v ^ 2) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q := by
  classical
  have hboxes := fun (Aact E rTerm qDeriv ρ : ℝ)
      (h : 0 ≤ E ∧ 0 < rTerm ∧ 0 < qDeriv ∧ 0 < ρ) =>
    exists_uniform_cap_window_exclusion_of_raw_cap_requests_with_window_scale_bound.{u}
      Aact E rTerm qDeriv a₀ ρ c Rbirth Cderiv h.1 h.2.1 h.2.2.1 ha₀ h.2.2.2 hc hRbirth
  choose εreq Rreq mreq δreq hεreq hεhalf hRreq hRbirthReq hmreq hδreq hwindowScale hwindowBarrier using hboxes
  let request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ :=
    fun Aact E rTerm qDeriv ρ =>
      if h : 0 ≤ E ∧ 0 < rTerm ∧ 0 < qDeriv ∧ 0 < ρ then
        (εreq Aact E rTerm qDeriv ρ h, Rreq Aact E rTerm qDeriv ρ h,
          mreq Aact E rTerm qDeriv ρ h, δreq Aact E rTerm qDeriv ρ h)
      else (1, 1, 0, 1)
  refine ⟨request, ?_, ?_, ?_, ?_⟩
  · intro Aact E rTerm qDeriv ρ hE hrTerm hqDeriv hρ
    let h : 0 ≤ E ∧ 0 < rTerm ∧ 0 < qDeriv ∧ 0 < ρ := ⟨hE, hrTerm, hqDeriv, hρ⟩
    simpa only [request, dite_eq_left h] using
      And.intro (hεreq Aact E rTerm qDeriv ρ h)
        (And.intro (hεhalf Aact E rTerm qDeriv ρ h)
          (And.intro (hRreq Aact E rTerm qDeriv ρ h)
            (And.intro (hRbirthReq Aact E rTerm qDeriv ρ h)
              (And.intro (hmreq Aact E rTerm qDeriv ρ h)
                (hδreq Aact E rTerm qDeriv ρ h)))))
  · intro Aact Ebound rTerm qDeriv ρ hE hrTerm hqDeriv hρ
    let h : 0 ≤ Ebound ∧ 0 < rTerm ∧ 0 < qDeriv ∧ 0 < ρ := ⟨hE, hrTerm, hqDeriv, hρ⟩
    simp only [request, dite_eq_left h]
    exact @hwindowScale Aact Ebound rTerm qDeriv ρ h
  · intro Aact E rTerm qDeriv ρ hE hrTerm hqDeriv hρ
    let h : 0 ≤ E ∧ 0 < rTerm ∧ 0 < qDeriv ∧ 0 < ρ := ⟨hE, hrTerm, hqDeriv, hρ⟩
    simpa only [request, dite_eq_left h] using
      hwindowBarrier Aact E rTerm qDeriv ρ h
  intro H parameters records hpc hfixed hscalarInitial t first hle v hv hpast
    p nodeA nodeE nodeR nodeQ nodeRho hdata q hfinite hsmall
  have hpreserve :=
    H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hscalar : ∀ j (s : ℝ), s ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier,
        -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) x := by
    intro j s hs x
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    have hneg : -(3 / a₀) ≤ -3 / (a₀ + s) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve.1 j s hs x).2
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hupperSupport : t.val ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hupperIcc
  have hpastDomain : t.val - v ^ 2 ∈ H.stageDomain first :=
    H.mem_stageDomain_of_mem_Ioo hpast
  have hscalarClock (j : H.StageInterval first (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x :=
    hscalar j.val _ (H.mapsTo_regularizedStage_Ioo t.val 0 v j.val hr) x
  have hcost := H.regularizedCost_eq_regularizedC1Cost first (H.activeStage t) hle
    t.val (3 / a₀) 0 v hupper hscalarClock p q
  have hfiniteC1 : H.regularizedC1Cost first (H.activeStage t) hle
      t.val 0 v p q ≠ ⊤ := by
    rw [← hcost]
    exact hfinite
  obtain ⟨gamma, hC1, hInt, hp, hq, hNodes, hSumC1⟩ :=
    H.exists_regularizedC1Cost_minimizer_of_ne_top first (H.activeStage t) hle
      t.val (3 / a₀) 0 v hupper hscalarClock p q hfiniteC1
  have hAC (j : H.StageInterval first (H.activeStage t)) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hC1 j).contMDiffOn
  have hSumCost : (((∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) : ℝ) : WithTop ℝ) =
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q :=
    hSumC1.trans hcost.symm
  have hmin : H.regularizedExtendedAction first (H.activeStage t)
      t.val (3 / a₀) 0 v gamma =
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q := by
    have hext := H.regularizedExtendedAction_eq_sum_action first (H.activeStage t)
      (le_refl 0) hv.le hupperIcc hpastDomain gamma hInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalarClock j r hr (gamma j r))
    exact hext.trans hSumCost
  have hcrossAll (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t) :
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) := by
    obtain ⟨hE, hrTerm, hqDeriv, hρ, hvE, hball, hδnode, hρnode, hlater, hderiv, hraw⟩ :=
      hdata i hf hl
    let hbox : 0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i :=
      ⟨hE, hrTerm, hqDeriv, hρ⟩
    simp only [request, dite_eq_left hbox] at hδnode hlater hraw
    have hsmallAction : (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val)
          (H.regularizedStageEnd t.val v j.val)) < nodeA i := by
      have hh := hsmall i hf hl
      rw [← hSumCost] at hh
      exact WithTop.coe_lt_coe.mp hh
    by_contra hbad
    obtain ⟨b, z, hcap⟩ :=
      ((H.event i).regularCrossing_or_cap_of_admissible_node
        (records i).old_eq_retained (hNodes i hf hl)).resolve_left hbad
    obtain ⟨Dbig, ζ, m, S, hRadius, hm, hζ, hcanonical, hscaleEq⟩ := hraw b
    have hpoint : gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
        (Real.sqrt (t.val - H.time i.succ)) = S.inclusion (S.witness.cap z) :=
      Sum.inl_injective (hcap.symm.trans (S.cap_eq z))
    have hstart : t.val - v ^ 2 < H.time i.succ := by
      let start : Icc (0 : ℝ) H.horizon :=
        ⟨t.val - v ^ 2, H.stageDomain_subset first hpastDomain⟩
      have hactive : H.activeStage start = first :=
        (H.mem_stageDomain_iff start first).mp hpastDomain
      by_contra hn
      have hi : i.succ ≤ first := by
        simpa only [hactive] using H.le_activeStage start i.succ (not_lt.mp hn)
      exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hi
    have hcanonicalCopy := hcanonical
    obtain ⟨_, _, _, _, _, _, _, hcapWindow⟩ := hcanonicalCopy
    obtain ⟨xPast, hxPast, hwindowPoint⟩ := hcapWindow z
    exact hwindowBarrier (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i) hbox
      H parameters records hfixed hscalarInitial t first hle v hv.le hvE hpastDomain
      p hball gamma hC1 hInt hp hNodes hsmallAction.le i
      (hf.trans i.castSucc_le_succ) hl hstart.le hpc hδnode hρnode hlater hderiv
      b Dbig ζ m S hRadius hm hζ hcanonical hscaleEq
      ⟨xPast, hxPast.trans hRbirth, hwindowPoint.trans hpoint.symm⟩
  refine ⟨gamma, hC1, hAC, hInt, hp, hq, hNodes, hmin, hcrossAll, ?_⟩
  intro etaError hetaError
  exact H.exists_physical_cost_upper_support_of_attained_action_at_closed_pole first (H.activeStage t) hle
    hv hupperSupport hpast hscalar gamma hAC hInt hNodes
    (by simpa only [hp, hq] using hmin)
    (hC1 ⟨first, le_rfl, hle⟩).contMDiffAt hcrossAll hetaError

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_physical_cost_support_with_event_local_cap_exclusion_requests_at_closed_poles
    (a₀ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (ha₀ : 0 < a₀) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ Rbirth < req.2.1 ∧
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
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth}
      ) ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 < v →
      t.val - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) →
    ∀ (p : (H.stageAt t).Carrier)
      (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t p (nodeR i) ∧
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
    ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ≠ ⊤ →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q <
          (nodeA i : WithTop ℝ)) →
    ∃ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = p ∧
      gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first (H.activeStage t) t.val (3 / a₀) 0 v gamma =
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
    ∀ etaError : ℝ, 0 < etaError →
    let jf : H.StageInterval first (H.activeStage t) := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first (H.activeStage t) := ⟨H.activeStage t, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction x.val t.val (gamma x)
        (H.regularizedStageStart t.val 0 x.val) (H.regularizedStageEnd t.val v x.val);
    let gOriginal := H.stageMetric first (t.val - v ^ 2);
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < t.val ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (t.val - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (t.val - z.2) * F (z.1, Real.sqrt (t.val - z.2));
    IsOpen Omega ∧ (q, t.val - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, t.val - v ^ 2) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 (Real.sqrt (t.val - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (t.val - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0
        (Real.sqrt (t.val - (t.val - v ^ 2))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ 2 * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (t.val - v ^ 2) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (t.val - v ^ 2) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q := by
  obtain ⟨request, hmargin, _hwindowScale, hwindow, hsupport⟩ :=
    exists_physical_cost_support_with_event_local_cap_exclusion_requests_at_closed_poles_with_window_scale_bound.{u}
      a₀ c Rbirth Cderiv ha₀ hc hRbirth
  exact ⟨request, hmargin, hwindow, hsupport⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_physical_cost_support_with_event_local_cap_exclusion_requests
    (a₀ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (ha₀ : 0 < a₀) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ Rbirth < req.2.1 ∧
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
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth}
      ) ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 < v → H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) →
    ∀ (p : (H.stageAt t).Carrier)
      (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t p (nodeR i) ∧
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
    ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ≠ ⊤ →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q <
          (nodeA i : WithTop ℝ)) →
    ∃ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = p ∧
      gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first (H.activeStage t) t.val (3 / a₀) 0 v gamma =
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
    ∀ etaError : ℝ, 0 < etaError →
    let jf : H.StageInterval first (H.activeStage t) := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first (H.activeStage t) := ⟨H.activeStage t, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction x.val t.val (gamma x)
        (H.regularizedStageStart t.val 0 x.val) (H.regularizedStageEnd t.val v x.val);
    let gOriginal := H.stageMetric first (t.val - v ^ 2);
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < t.val ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (t.val - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (t.val - z.2) * F (z.1, Real.sqrt (t.val - z.2));
    IsOpen Omega ∧ (q, t.val - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, t.val - v ^ 2) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 (Real.sqrt (t.val - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (t.val - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0
        (Real.sqrt (t.val - (t.val - v ^ 2))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ 2 * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (t.val - v ^ 2) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (t.val - v ^ 2) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q := by
  obtain ⟨request, hrequest, hwindow, hSupport⟩ :=
    exists_physical_cost_support_with_event_local_cap_exclusion_requests_at_closed_poles
      a₀ c Rbirth Cderiv ha₀ hc hRbirth
  refine ⟨request, hrequest, hwindow, ?_⟩
  intro H parameters records hpc hfixed hscalarInitial t first hle v hv _hpole
  exact hSupport H parameters records hpc hfixed hscalarInitial t first hle v hv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_physical_cost_support_with_event_local_cap_requests
    (a₀ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (ha₀ : 0 < a₀) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        0 < (request Aact E rTerm qDeriv ρ).1 ∧
        0 < (request Aact E rTerm qDeriv ρ).2.1 ∧
        0 < (request Aact E rTerm qDeriv ρ).2.2.2) ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ c →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 < v → H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) →
    ∀ (p : (H.stageAt t).Carrier)
      (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t p (nodeR i) ∧
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
    ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ≠ ⊤ →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q <
          (nodeA i : WithTop ℝ)) →
    ∃ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = p ∧
      gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first (H.activeStage t) t.val (3 / a₀) 0 v gamma =
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v p q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
    ∀ etaError : ℝ, 0 < etaError →
    let jf : H.StageInterval first (H.activeStage t) := ⟨first, le_rfl, hle⟩;
    let jl : H.StageInterval first (H.activeStage t) := ⟨H.activeStage t, hle, le_rfl⟩;
    let q := gamma jf v;
    let Loriginal := ∑ x : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction x.val t.val (gamma x)
        (H.regularizedStageStart t.val 0 x.val) (H.regularizedStageEnd t.val v x.val);
    let gOriginal := H.stageMetric first (t.val - v ^ 2);
    let Vorig : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v;
    let Roriginal := metricScalarAt gOriginal q;
    ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      F (q, v) = Loriginal ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 v (gamma jl 0) q = (F (q, v) : WithTop ℝ) ∧
      (∀ z ∈ U, H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 z.2 (gamma jl 0) z.1 ≤
        (F z : WithTop ℝ)) ∧
      gradientFun gOriginal (fun y => F (y, v)) q = Vorig ∧
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * Roriginal - (1 / 2 : ℝ) * gOriginal.inner q Vorig Vorig) v ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q <
        3 / v - v * Roriginal - Loriginal / (2 * v ^ 2) +
          gOriginal.inner q Vorig Vorig / (4 * v) + etaError / (2 * v) ∧
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < t.val ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (t.val - z.2)) ∈ U};
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (t.val - z.2) * F (z.1, Real.sqrt (t.val - z.2));
    IsOpen Omega ∧ (q, t.val - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, t.val - v ^ 2) = 2 * v * Loriginal ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0 (Real.sqrt (t.val - z.2))
          (gamma jl 0) z.1 = (cost : WithTop ℝ) ∧
        2 * Real.sqrt (t.val - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first (H.activeStage t) hle t.val (3 / a₀) 0
        (Real.sqrt (t.val - (t.val - v ^ 2))) (gamma jl 0) q = (Loriginal : WithTop ℝ) ∧
      gradientFun gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q = (2 * v) • Vorig ∧
      HasDerivAt (fun t => Aphys (q, t))
        (-Loriginal / v - 2 * v ^ 2 * Roriginal + gOriginal.inner q Vorig Vorig / 2)
        (t.val - v ^ 2) ∧
      laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q =
        2 * v * laplacian (LeviCivita gOriginal) gOriginal (fun y => F (y, v)) q ∧
      -6 - etaError < deriv (fun t => Aphys (q, t)) (t.val - v ^ 2) -
        laplacian (LeviCivita gOriginal) gOriginal (fun y => Aphys (y, t.val - v ^ 2)) q := by
  obtain ⟨request, hmargin, _hwindow, hsupport⟩ :=
    exists_physical_cost_support_with_event_local_cap_exclusion_requests.{u}
      a₀ c Rbirth Cderiv ha₀ hc hRbirth
  refine ⟨request, ?_, hsupport⟩
  intro Aact E rTerm qDeriv ρ hE hrTerm hqDeriv hρ
  obtain ⟨hε, _hεhalf, hR, _hRbirthR, _hm, hδ⟩ :=
    hmargin Aact E rTerm qDeriv ρ hE hrTerm hqDeriv hρ
  exact ⟨hε, hR, hδ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
