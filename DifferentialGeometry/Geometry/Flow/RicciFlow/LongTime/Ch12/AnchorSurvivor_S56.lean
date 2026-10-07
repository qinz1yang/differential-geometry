import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutoffThreshold_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

set_option autoImplicit false

/-!
# CH12-S56 / G1: the forward-survival anchor (W-A of `hLTF04`)

`GeometricCutoffRecord.exists_survivor_partialDiffeomorph_of_scalar_upper_bound` needs one
`RegularCrossing` point inside the low-scalar connected set `K`.  The record field
`protected_interior` supplies it for free: every terminal-regular point whose terminal scalar is
`≤ (protectedRadius²)⁻¹` (in particular every point with terminal scalar `≤ 0`, e.g. the
hyperbolic window where `2 s Ric ≈ -g`) lies in the interior of the retained core, hence is a
regular crossing.  So a thick ball of the (almost hyperbolic) slice is never in a discarded
component or in a removed band.  The terminal scalar is the `t ↑ τ` limit of the flow scalar
(`TerminalLimitMetric.eventually_scalar_close_on_compact`).
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- A terminal-regular point with terminal scalar `≤ (protectedRadius²)⁻¹` is a regular
crossing of the event (anchor lemma, protected-region form). -/
theorem exists_regularCrossing_of_protected_S56
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hanchor : metricScalarAt (H.event i).terminal.metric x ≤
      ((p.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ q : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val q := by
  have hx : x.val ∈ interior (Subtype.val '' (H.event i).old) := by
    rw [hOld]
    exact R.protected_interior x hanchor
  let W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen :=
    ⟨{y | y.val ∈ interior (Subtype.val '' (H.event i).old)},
      isOpen_interior.preimage continuous_subtype_val⟩
  obtain ⟨F, _, hcross, _⟩ :=
    (H.event i).exists_survivor_partialDiffeomorph W ⟨x, hx⟩ (fun _ hy => hy)
  exact ⟨F x, hcross x hx⟩

/-- The terminal scalar is bounded by any eventual upper bound of the flow scalar at `x`. -/
theorem terminal_scalar_le_of_eventually_S56
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (T : G.TerminalLimitMetric) (x : G.terminalRegularOpen) {L : ℝ}
    (h : ∀ᶠ t in 𝓝[<] s, metricScalarAt (G.flow.base.metric t) x.val ≤ L) :
    metricScalarAt T.metric x ≤ L := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hclose := T.eventually_scalar_close_on_compact (K := {x}) isCompact_singleton hε
  obtain ⟨t, ht1, ht2⟩ := (h.and hclose).exists
  have := ht2 x rfl
  rw [abs_lt] at this
  linarith [this.1]

/-- Anchor lemma (flow form): a point whose flow scalar is eventually `≤ 0` before the event is a
regular crossing (it is protected, since `0 ≤ (protectedRadius²)⁻¹`). -/
theorem exists_regularCrossing_of_flow_nonpos_S56
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    (hOld : (H.event i).old = (H.event i).transition.trace.retainedCore)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hflow : ∀ᶠ t in 𝓝[<] (H.time i.succ),
      metricScalarAt ((H.event i).incoming.flow.base.metric t) x.val ≤ 0) :
    ∃ q : (H.stage i.succ).Carrier, (H.event i).RegularCrossing x.val q :=
  exists_regularCrossing_of_protected_S56 R hOld x
    ((terminal_scalar_le_of_eventually_S56 (H.event i).terminal x hflow).trans
      (inv_nonneg.mpr (sq_nonneg _)))

/-- Anchored forward survival of a connected low-scalar set through one event; the anchor is a
protected point (terminal scalar `≤ (protectedRadius²)⁻¹`), no `RegularCrossing` is assumed. -/
theorem survivor_chart_of_protected_anchor_S56
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * K < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    {U : Set (H.event i).incoming.terminalRegularOpen} (hU : IsPreconnected U)
    (hscalar : ∀ x ∈ U, metricScalarAt (H.event i).terminal.metric x ≤ K / r ^ 2)
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ U)
    (hanchor : metricScalarAt (H.event i).terminal.metric x ≤
      ((p.protectedRadius (H.time i.succ)) ^ 2)⁻¹) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      U ⊆ E.source ∧
      (∀ z ∈ E.source, (H.event i).RegularCrossing z.val (E z)) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (H.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (H.event i).terminal.metric.inner z v w := by
  obtain ⟨q, hq⟩ := exists_regularCrossing_of_protected_S56 R R.old_eq_retained x hanchor
  obtain ⟨E, hUE, _, hcrossE, hmetric⟩ :=
    survivor_chart_of_nominal_threshold_CX2 R hr hΛ hKΛ hδ hnom hU hscalar hx hq
  exact ⟨E, hUE, hcrossE, hmetric⟩

/-- Flow form of the anchored survival (the form consumed by the first-failure induction):
a preconnected `U` of terminal-regular points whose flow scalar is eventually `≤ K / r²` before the
event, containing one point whose flow scalar is eventually `≤ 0`, survives the event with a
metric-preserving partial diffeomorphism.  The nominal-radius hypothesis `hnom` is the
`recent_cutoff_smallness` consequence. -/
theorem survivor_chart_of_flow_scalar_S56
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * K < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    {U : Set (H.event i).incoming.terminalRegularOpen} (hU : IsPreconnected U)
    (hflowU : ∀ y ∈ U, ∀ᶠ t in 𝓝[<] (H.time i.succ),
      metricScalarAt ((H.event i).incoming.flow.base.metric t) y.val ≤ K / r ^ 2)
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ U)
    (hflowx : ∀ᶠ t in 𝓝[<] (H.time i.succ),
      metricScalarAt ((H.event i).incoming.flow.base.metric t) x.val ≤ 0) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      U ⊆ E.source ∧
      (∀ z ∈ E.source, (H.event i).RegularCrossing z.val (E z)) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (H.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (H.event i).terminal.metric.inner z v w :=
  survivor_chart_of_protected_anchor_S56 R hr hΛ hKΛ hδ hnom hU
    (fun y hy => terminal_scalar_le_of_eventually_S56 (H.event i).terminal y (hflowU y hy)) hx
    ((terminal_scalar_le_of_eventually_S56 (H.event i).terminal x hflowx).trans
      (inv_nonneg.mpr (sq_nonneg _)))

end GC.LongTime.Ch12
