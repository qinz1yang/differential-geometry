import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedLift_S70

set_option autoImplicit false

/-!
# CH12-S70 / G1b: tracked points across stages and the closed step at an event

`TrackedAt_S70 K hle J p z` : `z ∈ stage j` is the forward image of `J p ∈ stage j0` along the
events between `j0` and `j` (a survivor point `x` of `[j0, j]` with `x.val = z` and
`backwardSurvivorMap j0 j hle j0 x = J p`).  The position is unique (`tracked_unique_S70`), and
extends across an event by a `RegularCrossing` (`tracked_succ_S70`).  `tracked_survives_event_S70` is the
closed step of the first-failure induction at an event time: flow Riemann norm `≤ Kc / r²` on the
tracked set up to the event plus one tracked point with eventually nonpositive scalar gives a survivor
chart `E` sending every tracked point to its tracked position at the next stage.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

/-- A time clamped into the horizon interval (so that `activeStage` can be applied to any real). -/
def clampT_S70 (K : ObservedHistory.{u}) (r : ℝ) : Icc (0 : ℝ) K.horizon :=
  ⟨max 0 (min r K.horizon), le_max_left _ _, max_le K.horizon_nonneg (min_le_right _ _)⟩

theorem clampT_val_S70 (K : ObservedHistory.{u}) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) K.horizon) :
    (clampT_S70 K r : ℝ) = r := by
  change max 0 (min r K.horizon) = r
  rw [min_eq_left hr.2, max_eq_right hr.1]

/-- The active stage at a real time (clamped). -/
def actS_S70 (K : ObservedHistory.{u}) (r : ℝ) : Fin (K.eventCount + 1) :=
  K.activeStage (clampT_S70 K r)

/-- `z ∈ stage j` is the forward image of `J p ∈ stage j0` (forward survivor trace). -/
def TrackedAt_S70 (K : ObservedHistory.{u}) {j0 j : Fin (K.eventCount + 1)} (hle : j0 ≤ j)
    {X : Type v} (J : X → (K.stage j0).Carrier) (p : X) (z : (K.stage j).Carrier) : Prop :=
  ∃ x : K.backwardSurvivorDomain j0 j hle, x.val = z ∧
    K.backwardSurvivorMap j0 j hle j0 le_rfl hle x = J p

theorem tracked_unique_S70 (K : ObservedHistory.{u}) {j0 j : Fin (K.eventCount + 1)}
    (hle : j0 ≤ j) {X : Type v} (J : X → (K.stage j0).Carrier) (p : X)
    {z z' : (K.stage j).Carrier} (h : TrackedAt_S70 K hle J p z) (h' : TrackedAt_S70 K hle J p z') :
    z = z' := by
  obtain ⟨x, rfl, hx⟩ := h
  obtain ⟨x', rfl, hx'⟩ := h'
  rw [K.backwardSurvivorMap_injective j0 j hle j0 le_rfl hle (hx.trans hx'.symm)]

/-- A tracked point crossing an event stays tracked at the next stage. -/
theorem tracked_succ_S70 (K : ObservedHistory.{u}) {j0 : Fin (K.eventCount + 1)}
    {i : Fin K.eventCount} (hle : j0 ≤ i.castSucc) {X : Type v}
    (J : X → (K.stage j0).Carrier) (p : X) {z : (K.stage i.castSucc).Carrier}
    {q : (K.stage i.succ).Carrier} (hz : TrackedAt_S70 K hle J p z)
    (hcross : (K.event i).RegularCrossing z q) :
    TrackedAt_S70 K (hle.trans i.castSucc_lt_succ.le) J p q := by
  obtain ⟨x, rfl, hx⟩ := hz
  let A := Classical.choice x.property
  have hA : BackwardPointTrace K j0 i.castSucc hle x.val := A
  refine ⟨⟨q, ⟨hA.append q hcross⟩⟩, rfl, ?_⟩
  rw [K.backwardSurvivorMap_eq_point j0 i.succ _ j0 le_rfl _ ⟨q, ⟨hA.append q hcross⟩⟩
    (hA.append q hcross), BackwardPointTrace.append_point_before hA q hcross j0 le_rfl hle,
    ← hx, K.backwardSurvivorMap_eq_point j0 i.castSucc hle j0 le_rfl hle x hA]

/-- Closed step at an event time: a connected open set `Y` of tracked points with flow
`riemannNorm ≤ Kc / r²` up to the event, one tracked point with eventually nonpositive flow scalar,
survives the event; the survivor chart `E` sends every tracked point to its tracked position at the
next stage, and is an isometry from the terminal metric to the output metric. -/
theorem tracked_survives_event_S70 (K : ObservedHistory.{u}) {i : Fin K.eventCount}
    {pr : CutoffParameters} (R : GeometricCutoffRecord K i pr) {r Λ Kc : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * (9 * Kc) < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646) (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    {j0 : Fin (K.eventCount + 1)} (hle : j0 ≤ i.castSucc) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X)
    (hY : IsPreconnected {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z})
    (hV : IsOpen {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z})
    {a' : ℝ} (ha' : a' ∈ Ico (K.time i.castSucc) (K.time i.succ))
    (hB : ∀ z ∈ {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z}, ∀ t ∈ Ico a' (K.time i.succ),
      (K.event i).incoming.riemannNorm t z ≤ Kc / r ^ 2)
    {x₀ : X} (hx₀ : x₀ ∈ B) {z₀ : (K.stage i.castSucc).Carrier}
    (hz₀ : TrackedAt_S70 K hle J x₀ z₀)
    (hflow : ∀ᶠ t in 𝓝[<] (K.time i.succ),
      metricScalarAt ((K.event i).incoming.flow.base.metric t) z₀ ≤ 0) :
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
  obtain ⟨E, hEY, hcross, hmetric⟩ := survivor_chart_of_rm_bound_S56 R hr hΛ hKΛ hδ hnom hY hV
    (fun z hz => hz) ha' hB (x := z₀) ⟨x₀, hx₀, hz₀⟩ hflow
  refine ⟨E, fun x hx z hz => ?_, hmetric⟩
  obtain ⟨h, hsrc⟩ := hEY z ⟨x, hx, hz⟩
  exact ⟨h, hsrc, tracked_succ_S70 K hle J x hz (hcross _ hsrc)⟩

end GC.LongTime.Ch12
