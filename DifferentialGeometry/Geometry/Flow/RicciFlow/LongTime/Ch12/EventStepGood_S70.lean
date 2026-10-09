import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeStages_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ScalarNegDefect_S56

set_option autoImplicit false

/-!
# CH12-S70 / G1e: `hclosed` at an event time from the pointwise Weak bounds

`tracked_survives_event_of_good_S70` is the event-time half of `hclosed_S70`.  Its hypotheses are exactly
what `Weak(r)`, `r ∈ [a', τ)` provides at the tracked set `Y` of the stage before the event:
the flow bound `riemannNorm ≤ K0 / r` and the LTF03 defect `≤ η ≤ 1` at one tracked point.
The scale `√a'` converts `K0 / r ≤ K0 / (√a')²` (`r ≥ a'`) to the form of `survivor_chart_of_rm_bound_S56`;
the defect `≤ 1` gives flow scalar `≤ 0` (`scalar_nonpos_of_quad_defect_S56`), the anchor.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

/-- LTF03 defect `≤ η ≤ 1` on the flow of the stage before an event, at one point, for times in
`[a', τ)`, gives flow scalar `≤ 0` eventually before `τ` (the anchor hypothesis `hflowx`). -/
theorem flow_scalar_nonpos_of_defect_S70 (K : ObservedHistory.{u}) (i : Fin K.eventCount)
    {z : (K.stage i.castSucc).Carrier} {a' η : ℝ} (ha' : a' ∈ Ico (K.time i.castSucc) (K.time i.succ))
    (ha0 : 0 < a') (hη : η ≤ 1)
    (hdef : ∀ t ∈ Ico a' (K.time i.succ), ∀ V : TangentSpace ThreeModel z,
      |2 * t * ricciTensor ((K.event i).incoming.flow.base.metric t) z V V +
          ((K.event i).incoming.flow.base.metric t).inner z V V| ≤
        η * ((K.event i).incoming.flow.base.metric t).inner z V V) :
    ∀ᶠ t in 𝓝[<] (K.time i.succ),
      metricScalarAt ((K.event i).incoming.flow.base.metric t) z ≤ 0 := by
  filter_upwards [Ico_mem_nhdsLT ha'.2] with t ht
  exact scalar_nonpos_of_quad_defect_S56 _ z (lt_of_lt_of_le ha0 ht.1) hη (hdef t ht)

/-- Closed step at an event time from the Weak bounds `|Rm| ≤ K0 / r`, defect `≤ η ≤ 1`. -/
theorem tracked_survives_event_of_good_S70 (K : ObservedHistory.{u}) {i : Fin K.eventCount}
    {pr : CutoffParameters} (R : GeometricCutoffRecord K i pr) {Λ K0 η : ℝ}
    (hΛ : 1 ≤ Λ) {a' : ℝ} (ha' : a' ∈ Ico (K.time i.castSucc) (K.time i.succ)) (ha0 : 0 < a')
    (hK0 : 0 ≤ K0) (hKΛ : 2 * (9 * K0) < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646) (hnom : ∀ h, Λ * R.nominalRadius h ≤ Real.sqrt a')
    {j0 : Fin (K.eventCount + 1)} (hle : j0 ≤ i.castSucc) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X)
    (hY : IsPreconnected {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z})
    (hV : IsOpen {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z})
    (hB : ∀ z ∈ {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z}, ∀ t ∈ Ico a' (K.time i.succ),
      (K.event i).incoming.riemannNorm t z ≤ K0 / t)
    {x₀ : X} (hx₀ : x₀ ∈ B) {z₀ : (K.stage i.castSucc).Carrier}
    (hz₀ : TrackedAt_S70 K hle J x₀ z₀) (hη : η ≤ 1)
    (hdef : ∀ t ∈ Ico a' (K.time i.succ), ∀ V : TangentSpace ThreeModel z₀,
      |2 * t * ricciTensor ((K.event i).incoming.flow.base.metric t) z₀ V V +
          ((K.event i).incoming.flow.base.metric t).inner z₀ V V| ≤
        η * ((K.event i).incoming.flow.base.metric t).inner z₀ V V) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (K.event i).incoming.terminalRegularOpen (K.stage i.succ).Carrier ∞,
      (∀ x ∈ B, ∀ z, TrackedAt_S70 K hle J x z →
        ∃ h : z ∈ (K.event i).incoming.terminalRegularRegion,
          (⟨z, h⟩ : (K.event i).incoming.terminalRegularOpen) ∈ E.source ∧
          TrackedAt_S70 K (hle.trans i.castSucc_lt_succ.le) J x (E ⟨z, h⟩)) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (K.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (K.event i).terminal.metric.inner z v w := by
  have hsq : Real.sqrt a' ^ 2 = a' := Real.sq_sqrt ha0.le
  refine tracked_survives_event_S70 K R (Real.sqrt_pos.mpr ha0) hΛ hKΛ hδ hnom hle J B hY hV ha'
    (fun z hz t ht => ?_) hx₀ hz₀ (flow_scalar_nonpos_of_defect_S70 K i ha' ha0 hη hdef)
  rw [hsq]
  exact (hB z hz t ht).trans (div_le_div_of_nonneg_left hK0 ha0 ht.1)

end GC.LongTime.Ch12
