import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRescalingRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward

/-!
# G3（AD-age，R-C11-1 9.1）：`RetainedCoreHistory` 的抛物重标度对象（`_P6N`）

树内只有 `ObservedHistory.rescale`（`ST/HistoryRescaling`：time ↦ time/r、metric ↦ r⁻¹·g、
`MetricCutCapEvent.rescale`、`ClosedSlab.rescale`）。本文件补 retained-core 层：
* `RetainedCoreEvent.rescale_P6N`（照 `MetricCutCapEvent.rescale`：`oldTerminal` 沿
  `IncomingSlab.rescale_terminalRegularOpen` cast；`old_metric_eq` 同 cast 引理）；
  `toMetricCutCapEvent_rescale_P6N`：`(E.rescale_P6N r).toMetricCutCapEvent =
  E.toMetricCutCapEvent.rescale r`（`rfl`）。
* `RetainedCoreHistory.rescale_P6N`；**`toHistory_rescale_P6N : (H.rescale_P6N r).toHistory =
  H.toHistory.rescale r`（`rfl`）**——于是树内 `ObservedHistory.rescale_activeStage` /
  `rescale_stageMetric` / `rescale_stageDomain` 直接可用。
* backward trace 双向 transport（stage、event 的 `old`/`oldOutput`/charts 不变 ⇒ `RegularCrossing` 定义等）；
  终端 incoming slab `G ↦ G.rescale r`、`hend`/`hG` transport；`Λ ≤ R'·t' ⇔ Λ ≤ R·t`
  （`R' = r·R(r ·)`、`t' = t/r`）。
records（`GeometricCutoffRecord`）的 transport 在 `AdapterAgeObject_P6N`。
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreEvent

variable {P Q : OrientedThreeStage.{u}} {a b : ℝ}

private theorem cast_continuousMap_val_P6N {X : Type*} [TopologicalSpace X]
    {U V : TopologicalSpace.Opens P.Carrier} (h : U = V) (f : C(X, U)) (x : X) :
    ((h ▸ f) x).1 = (f x).1 := by
  cases h
  rfl

private theorem cast_metric_inner_P6N {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 3) X]
    {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    (q : ∀ U : TopologicalSpace.Opens P.Carrier, SmoothRiemannianMetric ThreeModel U → Prop)
    (g : {g : SmoothRiemannianMetric ThreeModel U // q U g}) (f : C(X, U))
    (x : X) (v w : TangentSpace (𝓡∂ 3) x) :
    (h ▸ g).1.inner ((h ▸ f) x)
        (mfderiv (𝓡∂ 3) ThreeModel (h ▸ f) x v)
        (mfderiv (𝓡∂ 3) ThreeModel (h ▸ f) x w) =
      g.1.inner (f x) (mfderiv (𝓡∂ 3) ThreeModel f x v)
        (mfderiv (𝓡∂ 3) ThreeModel f x w) := by
  cases h
  rfl

/-- **`_P6N`**：retained-core event 的抛物重标度（time ↦ time/r、metric ↦ r⁻¹·g）；照
`MetricCutCapEvent.rescale`。 -/
def rescale_P6N (E : RetainedCoreEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    RetainedCoreEvent P Q (a / r) (b / r) where
  discarded := E.discarded
  capped := E.capped
  transition := E.transition
  incoming := E.incoming.rescale r hr
  terminal := E.terminal.rescale r hr
  outputMetric := scaleMetric r⁻¹ (inv_pos.mpr hr) E.outputMetric
  oldTerminal := (E.incoming.rescale_terminalRegularOpen r hr).symm ▸ E.oldTerminal
  oldTerminal_eq := by
    intro x
    exact (cast_continuousMap_val_P6N _ E.oldTerminal x).trans (E.oldTerminal_eq x)
  oldOutput := E.oldOutput
  oldOutput_eq := E.oldOutput_eq
  old_metric_eq := by
    let _ := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    intro x v w
    let q (U : TopologicalSpace.Opens P.Carrier) (gbar : SmoothRiemannianMetric ThreeModel U) :=
      ∀ K : Set U, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ d ∈ Ico (a / r) (b / r), ∀ t ∈ Ioo d (b / r), ∀ y ∈ K,
          DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm j
            (((E.incoming.rescale r hr).flow.base.metric t).restrictOpen U) gbar gbar y < ε
    let old : {gbar : SmoothRiemannianMetric ThreeModel E.incoming.terminalRegularOpen //
        q E.incoming.terminalRegularOpen gbar} :=
      ⟨scaleMetric r⁻¹ (inv_pos.mpr hr) E.terminal.metric, E.terminal.rescale_converges r hr⟩
    have ht := cast_metric_inner_P6N (E.incoming.rescale_terminalRegularOpen r hr).symm
      q old E.oldTerminal x v w
    apply ht.trans
    simpa only [old, scaleMetric_inner] using
      congrArg (fun z : ℝ => r⁻¹ * z) (E.old_metric_eq x v w)
  every_child_meets_old := E.every_child_meets_old

theorem toMetricCutCapEvent_rescale_P6N (E : RetainedCoreEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale_P6N r hr).toMetricCutCapEvent = E.toMetricCutCapEvent.rescale r hr :=
  rfl

end RetainedCoreEvent

namespace RetainedCoreHistory

/-- **`_P6N`**：retained-core history 的抛物重标度；`toHistory` 与树内 `ObservedHistory.rescale` 定义等。 -/
def rescale_P6N (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r) : RetainedCoreHistory.{u} where
  horizon := H.horizon / r
  horizon_nonneg := div_nonneg H.horizon_nonneg hr.le
  eventCount := H.eventCount
  time := fun j => H.time j / r
  time_strictMono := fun _ _ hij => div_lt_div_of_pos_right (H.time_strictMono hij) hr
  time_zero := by rw [H.time_zero, zero_div]
  time_le_horizon := (div_le_div_iff_of_pos_right hr).mpr H.time_le_horizon
  stage := H.stage
  initialMetric := fun j => scaleMetric r⁻¹ (inv_pos.mpr hr) (H.initialMetric j)
  coreEvent := fun i => (H.coreEvent i).rescale_P6N r hr
  event_initial := (H.toHistory.rescale r hr).event_initial
  event_output := (H.toHistory.rescale r hr).event_output
  finalSlab := fun h =>
    (H.finalSlab ((div_lt_div_iff_of_pos_right hr).mp h)).rescale r hr
  final_initial := (H.toHistory.rescale r hr).final_initial

theorem toHistory_rescale_P6N (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r) :
    (H.rescale_P6N r hr).toHistory = H.toHistory.rescale r hr :=
  rfl

@[simp] theorem rescale_P6N_time (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) : (H.rescale_P6N r hr).time j = H.time j / r := rfl

@[simp] theorem rescale_P6N_horizon (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r) :
    (H.rescale_P6N r hr).horizon = H.horizon / r := rfl

/-- trace transport（重标度 → 原）：点、端点、crossing 逐字（event 的 `old`/`oldOutput` 不变）。 -/
def traceOfRescale_P6N (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r)
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace (H.rescale_P6N r hr).toHistory first last hle x) :
    BackwardPointTrace H.toHistory first last hle x :=
  ⟨A.point, A.endpoint_eq, A.crossing⟩

/-- trace transport（原 → 重标度）。 -/
def traceToRescale_P6N (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r)
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace H.toHistory first last hle x) :
    BackwardPointTrace (H.rescale_P6N r hr).toHistory first last hle x :=
  ⟨A.point, A.endpoint_eq, A.crossing⟩

theorem nonempty_trace_rescale_iff_P6N {H : RetainedCoreHistory.{u}} (r : ℝ) (hr : 0 < r)
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier} :
    Nonempty (BackwardPointTrace (H.rescale_P6N r hr).toHistory first last hle x) ↔
      Nonempty (BackwardPointTrace H.toHistory first last hle x) :=
  ⟨fun ⟨A⟩ => ⟨H.traceOfRescale_P6N r hr A⟩, fun ⟨A⟩ => ⟨H.traceToRescale_P6N r hr A⟩⟩

/-- 重标度 stage 度量（经 `toHistory_rescale_P6N` 落到树内 `ObservedHistory.rescale_stageMetric`）。 -/
theorem rescale_P6N_stageMetric (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) (t : ℝ) :
    (H.rescale_P6N r hr).toHistory.stageMetric j t =
      scaleMetric r⁻¹ (inv_pos.mpr hr) (H.toHistory.stageMetric j (r * t)) :=
  H.toHistory.rescale_stageMetric r hr j t

/-- 终端 incoming slab 的 transport：`G ↦ G.rescale r`，`hG` 照搬（`r · (time/r) = time`）。 -/
theorem rescale_P6N_incoming_initial (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (G.rescale r hr).flow.base.metric ((H.rescale_P6N r hr).time
        (Fin.last (H.rescale_P6N r hr).eventCount)) =
      (H.rescale_P6N r hr).initialMetric (Fin.last (H.rescale_P6N r hr).eventCount) := by
  change (G.rescale r hr).flow.base.metric (H.time (Fin.last H.eventCount) / r) =
    scaleMetric r⁻¹ (inv_pos.mpr hr) (H.initialMetric (Fin.last H.eventCount))
  rw [OrientedThreeStage.IncomingSlab.rescale_metric, mul_div_cancel₀ _ hr.ne', hG]

theorem rescale_P6N_hend (H : RetainedCoreHistory.{u}) (r : ℝ) (hr : 0 < r)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) :
    (H.rescale_P6N r hr).time (Fin.last (H.rescale_P6N r hr).eventCount) =
      (H.rescale_P6N r hr).horizon := by
  change H.time (Fin.last H.eventCount) / r = H.horizon / r
  rw [hend]

/-- 重标度后 incoming slab 的标量：`R'(t', x) = r · R(r t', x)`。 -/
theorem rescale_scalar_P6N {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (x : P.Carrier) :
    (G.rescale r hr).flow.scalar t x = r * G.flow.scalar (r * t) x := by
  change DifferentialGeometry.Geometry.Curvature.metricScalarAt
      ((G.rescale r hr).flow.base.metric t) x = _
  rw [OrientedThreeStage.IncomingSlab.rescale_metric,
    DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, inv_inv]
  rfl

/-- `R'·t' = R·t`（`t' = t/r`），故 `Λ ≤ R·t` 原样 transport；`R' = r·R` 给 `Λ ≤ R'` 的来源
（`r = a₀ + s_n` 时由 `AdapterAge_P6L.tendsto_age_mul_of_selection_P6L`）。 -/
theorem rescale_scalar_mul_time_P6N {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (r : ℝ) (hr : 0 < r) (t : ℝ) (x : P.Carrier) :
    (G.rescale r hr).flow.scalar (t / r) x * (t / r) = G.flow.scalar t x * t := by
  rw [rescale_scalar_P6N, mul_div_cancel₀ _ hr.ne']
  field_simp

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
