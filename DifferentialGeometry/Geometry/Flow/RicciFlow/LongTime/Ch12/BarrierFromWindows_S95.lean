import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBarrier_S88
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap

/-!
# CH12-S95, groups 2/3 (interface part): frontier windows, hFront from collar clauses, and the
event-level located barrier from "no CAP"

* `hFront_of_collar_S95`: the S88 `hFront` (frontier of the retained image lies in a cap window
  `‖x‖ < Dc + 1`) follows from two record-level clauses, (RFC-a) frontier localisation in the retained
  collar `z ≤ 1` of a static cap and (RFC-b) the collar `z ≤ 1` lies in the window `‖x‖ < Dc + 1`.
  Neither clause is derivable from the fields of `GeometricCutoffRecord` / `PresentedStaticCap` alone
  (see DELIVERIES, `[FROZEN] CH12-S95 G2`); both are the ch11 record-compat candidates.
* `barrier_of_frontier_windows_S95`: hFront + "no window point of `U`" gives the event barrier for `U`
  (`barrier_of_no_frontier_S88`).
* `located_barrier_of_noCAP_S95`: the located barrier clause of `traced_of_seeds_ball_S95`/
  `record_seed_tracedRegion_ball_S88` at every event of a history, from hFront (young events), the
  absorption clause `hAbs` (a window point in a low-scalar set `U` in the 20r-ball of the centre's trace
  point forces the cap predicate for the centre) and `¬ CAP`; old events by the hypothesis `hold`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- hFront from the two collar clauses (RFC-a), (RFC-b). -/
theorem hFront_of_collar_S95 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    {i : Fin H.eventCount} (R : GeometricCutoffRecord H i pp) {Dc : ℝ}
    (hlocal : ∀ y ∈ frontier (range (H.event i).oldOutput),
      ∃ (b : (H.event i).RetainedBoundaryIndex)
        (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
          (R.static b).inclusion ((R.static b).witness.retained c) = y)
    (hwin : ∀ (b : (H.event i).RetainedBoundaryIndex)
        (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 →
      ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dc + 1 ∧
        (R.static b).window x = (R.static b).inclusion ((R.static b).witness.retained c)) :
    ∀ y ∈ frontier (range (H.event i).oldOutput),
      ∃ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        (R.static b).window x = y ∧ ‖x.val‖ < Dc + 1 := by
  intro y hy
  obtain ⟨b, c, hc, rfl⟩ := hlocal y hy
  obtain ⟨x, hx, hxe⟩ := hwin b c hc
  exact ⟨b, x, hxe, hx⟩

/-- hFront + "no cap-window point of `U`" ⇒ the event barrier for `U`. -/
theorem barrier_of_frontier_windows_S95 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    {i : Fin H.eventCount} (R : GeometricCutoffRecord H i pp) {Dc : ℝ}
    (hFront : ∀ y ∈ frontier (range (H.event i).oldOutput),
      ∃ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        (R.static b).window x = y ∧ ‖x.val‖ < Dc + 1)
    {U : Set (H.stage i.succ).Carrier} (hU : IsPreconnected U)
    (hfree : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < Dc + 1 → (R.static b).window x ∉ U)
    {x : (H.event i).incoming.terminalRegularOpen} {y : (H.stage i.succ).Carrier}
    (hy : y ∈ U) (hcross : (H.event i).RegularCrossing x.val y) :
    U ⊆ interior (range (H.event i).oldOutput) := by
  refine barrier_of_no_frontier_S88 hU hy hcross (Set.disjoint_left.mpr fun q hqU hqF => ?_)
  obtain ⟨b, w, hw, hn⟩ := hFront q hqF
  exact hfree b w hn (hw ▸ hqU)

/-- The located barrier clause at every window event `i` (`W i`, e.g. `H.time i.succ ∈ Ioc (s.time - τ r²)
s.time`), from `¬ CAP`.  `CAPat i` is the cap predicate of the centre at event `i` (instantiated by the S64
clause: the centre's trace point at event `i` lies in a window `‖x‖ < Dcap' + 1` of a retained boundary of
event `i`, with the age clause).  `hAbs` is the analytic absorption step (norm transfer + cap scalar lower
bound, which also forces the age clause when `9 K τ < c₀ θ`; not proved here), `hold` supplies the barrier
at window events without a record (events older than `T₀ - θ`: the CX2 `hnom` route). -/
theorem located_barrier_of_noCAP_S95 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    (T₀ θ Dc r K : ℝ) (W : Fin H.eventCount → Prop)
    (records : ∀ i : Fin H.eventCount, T₀ - θ ≤ H.time i.succ → GeometricCutoffRecord H i pp)
    (hFront : ∀ (j : Fin H.eventCount) (hj : T₀ - θ ≤ H.time j.succ),
      ∀ y ∈ frontier (range (H.event j).oldOutput),
        ∃ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
          ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dc + 1)
    (c : ∀ i : Fin H.eventCount, W i → (H.stage i.succ).Carrier)
    (CAPat : Fin H.eventCount → Prop) (hno : ∀ i, ¬ CAPat i)
    (hAbs : ∀ (i : Fin H.eventCount) (hi : T₀ - θ ≤ H.time i.succ),
      ∀ (hW : W i) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric (c i hW) (20 * r) →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      (∃ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        ‖x.val‖ < Dc + 1 ∧ ((records i hi).static b).window x ∈ U) → CAPat i)
    (hold : ∀ (i : Fin H.eventCount) (hW : W i), ¬ (T₀ - θ ≤ H.time i.succ) →
      ∀ U : Set (H.stage i.succ).Carrier,
      U ⊆ riemannianBallOf (H.event i).outputMetric (c i hW) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y →
        U ⊆ interior (range (H.event i).oldOutput)) :
    ∀ (i : Fin H.eventCount) (hW : W i) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric (c i hW) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y →
        U ⊆ interior (range (H.event i).oldOutput) := by
  intro i hW U hUb hU hs x y hy hc
  by_cases hi : T₀ - θ ≤ H.time i.succ
  · refine barrier_of_frontier_windows_S95 (records i hi) (hFront i hi) hU ?_ hy hc
    intro b w hw hmem
    exact hno i (hAbs i hi hW U hUb hs ⟨b, w, hw, hmem⟩)
  · exact hold i hW hi U hUb hU hs x y hy hc

/-- The same when every window event is young (`T₀ - θ ≤ time`; e.g. `T₀ := s.time`, `τ r² ≤ θ`): no `hold`
clause and no per-neck split. -/
theorem located_barrier_of_noCAP_young_S95 {H : ObservedHistory.{u}} {pp : CutoffParameters}
    (T₀ θ Dc r K : ℝ) (W : Fin H.eventCount → Prop)
    (hyoung : ∀ i, W i → T₀ - θ ≤ H.time i.succ)
    (records : ∀ i : Fin H.eventCount, T₀ - θ ≤ H.time i.succ → GeometricCutoffRecord H i pp)
    (hFront : ∀ (j : Fin H.eventCount) (hj : T₀ - θ ≤ H.time j.succ),
      ∀ y ∈ frontier (range (H.event j).oldOutput),
        ∃ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
          ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dc + 1)
    (c : ∀ i : Fin H.eventCount, W i → (H.stage i.succ).Carrier)
    (CAPat : Fin H.eventCount → Prop) (hno : ∀ i, ¬ CAPat i)
    (hAbs : ∀ (i : Fin H.eventCount) (hi : T₀ - θ ≤ H.time i.succ),
      ∀ (hW : W i) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric (c i hW) (20 * r) →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      (∃ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        ‖x.val‖ < Dc + 1 ∧ ((records i hi).static b).window x ∈ U) → CAPat i) :
    ∀ (i : Fin H.eventCount) (hW : W i) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric (c i hW) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y →
        U ⊆ interior (range (H.event i).oldOutput) :=
  located_barrier_of_noCAP_S95 T₀ θ Dc r K W records hFront c CAPat hno hAbs
    (fun i hW hi => absurd (hyoung i hW) hi)

/-- Arithmetic of the age split: a window event of age `a < τ r²` whose cap window carries a point of scalar
`S ∈ [c₀ q, 9 K / r²]` (`q` = the cap scale, `c₀` the cap scalar lower bound on the window) satisfies the
age clause `a ≤ θ / q` of CAP as soon as `9 K τ ≤ c₀ θ`.  So the age clause of CAP is automatic for window
points of low-scalar sets, and no `hnom`-type per-neck split is needed for young events. -/
theorem age_le_of_scalar_S95 {q a S c₀ θ τ r K : ℝ} (hq : 0 < q) (hc : 0 < c₀) (hr : 0 < r)
    (hτ : 0 < τ) (ha : a < τ * r ^ 2) (hS1 : c₀ * q ≤ S) (hS2 : S ≤ 9 * K / r ^ 2)
    (hτK : 9 * K * τ ≤ c₀ * θ) : a ≤ θ * q⁻¹ := by
  by_contra h
  rw [not_le] at h
  have h1 : θ < a * q := by
    have := mul_lt_mul_of_pos_right h hq
    rwa [mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] at this
  have hr2 : 0 < r ^ 2 := by positivity
  have h2 : c₀ * q * r ^ 2 ≤ 9 * K := by
    have := (hS1.trans hS2)
    rw [le_div_iff₀ hr2] at this
    exact this
  have h3 : θ < τ * r ^ 2 * q := by
    have : a * q < τ * r ^ 2 * q := mul_lt_mul_of_pos_right ha hq
    linarith only [h1, this]
  have h4 : c₀ * θ < c₀ * (τ * r ^ 2 * q) := mul_lt_mul_of_pos_left h3 hc
  have h5 : c₀ * q * r ^ 2 * τ ≤ 9 * K * τ := mul_le_mul_of_nonneg_right h2 hτ.le
  nlinarith only [h4, h5, hτK]

end GC.LongTime.Ch12
