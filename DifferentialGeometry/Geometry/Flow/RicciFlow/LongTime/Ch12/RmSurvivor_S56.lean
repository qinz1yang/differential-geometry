import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.AnchorSurvivor_S56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RecentProtection_CX2

set_option autoImplicit false

/-!
# CH12-S56 / G2b: the closed step of the first-failure induction in flow (`riemannNorm`) form

A set `Y` of the stage before an event whose physical Riemann norm is `≤ K / r²` on an open
neighbourhood for all times in `[a', τ)` is terminal regular, has terminal scalar `≤ 9K/r²`, and,
if one point of `Y` has eventually nonpositive scalar, survives the event
(`survivor_chart_of_rm_bound_S56`).  This is the "closed" hypothesis `hclosed` of
`first_failure_bootstrap_S56` at an event time.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- Uniform Riemann bound on a neighbourhood up to the event time makes the point terminal regular. -/
theorem mem_terminalRegularRegion_of_bound_S56 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) {x : P.Carrier} {V : Set P.Carrier} (hV : IsOpen V) (hxV : x ∈ V)
    {a' : ℝ} (ha' : a' ∈ Ico a s) {B : ℝ}
    (hB : ∀ y ∈ V, ∀ t ∈ Ico a' s, G.riemannNorm t y ≤ B) :
    x ∈ G.terminalRegularRegion :=
  ⟨V, hV, hxV, a', ha', max B 0, le_max_right _ _,
    fun y hy t ht => (hB y hy t ht).trans (le_max_left _ _)⟩

/-- Flow scalar bound from the flow Riemann norm (dimension three). -/
theorem flow_scalar_le_of_riemannNorm_S56 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (t : ℝ) (y : P.Carrier) {K r : ℝ}
    (h : G.riemannNorm t y ≤ K / r ^ 2) :
    metricScalarAt (G.flow.base.metric t) y ≤ (9 * K) / r ^ 2 :=
  scalar_le_nine_rm_bound_CX2 P (G.flow.base.metric t) y h

/-- Preconnectedness transfers from `Y ⊆ P.Carrier` to the preimage in the terminal regular open. -/
theorem isPreconnected_preimage_terminalRegularOpen_S56 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) {Y : Set P.Carrier} (hY : IsPreconnected Y)
    (hsub : Y ⊆ G.terminalRegularRegion) :
    IsPreconnected {y : G.terminalRegularOpen | y.val ∈ Y} := by
  have himg : Subtype.val '' {y : G.terminalRegularOpen | y.val ∈ Y} = Y := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, hsub hz⟩, hz, rfl⟩
  have hind : Topology.IsInducing (Subtype.val : G.terminalRegularOpen → P.Carrier) :=
    Topology.IsInducing.subtypeVal
  rw [← hind.isPreconnected_image, himg]
  exact hY

/-- Closed step at an event time, Riemann-norm form. -/
theorem survivor_chart_of_rm_bound_S56
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * (9 * K) < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    {Y : Set (H.stage i.castSucc).Carrier} (hY : IsPreconnected Y)
    {V : Set (H.stage i.castSucc).Carrier} (hV : IsOpen V) (hYV : Y ⊆ V)
    {a' : ℝ} (ha' : a' ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hB : ∀ y ∈ V, ∀ t ∈ Ico a' (H.time i.succ),
      (H.event i).incoming.riemannNorm t y ≤ K / r ^ 2)
    {x : (H.stage i.castSucc).Carrier} (hx : x ∈ Y)
    (hflowx : ∀ᶠ t in 𝓝[<] (H.time i.succ),
      metricScalarAt ((H.event i).incoming.flow.base.metric t) x ≤ 0) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      (∀ y ∈ Y, ∃ h : y ∈ (H.event i).incoming.terminalRegularRegion,
        (⟨y, h⟩ : (H.event i).incoming.terminalRegularOpen) ∈ E.source) ∧
      (∀ z ∈ E.source, (H.event i).RegularCrossing z.val (E z)) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (H.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (H.event i).terminal.metric.inner z v w := by
  have hreg : Y ⊆ (H.event i).incoming.terminalRegularRegion := fun y hy =>
    mem_terminalRegularRegion_of_bound_S56 (H.event i).incoming hV (hYV hy) ha' hB
  have hU := isPreconnected_preimage_terminalRegularOpen_S56 (H.event i).incoming hY hreg
  obtain ⟨E, hUE, hcross, hmetric⟩ := survivor_chart_of_flow_scalar_S56 R hr hΛ
    (K := 9 * K) hKΛ hδ hnom hU
    (fun y hy => by
      have hyV := hYV hy
      filter_upwards [Ico_mem_nhdsLT ha'.2] with t ht
      have := hB y.val hyV t ht
      exact flow_scalar_le_of_riemannNorm_S56 (H.event i).incoming t y.val this)
    (x := ⟨x, hreg hx⟩) hx hflowx
  exact ⟨E, fun y hy => ⟨hreg hy, hUE hy⟩, hcross, hmetric⟩

end GC.LongTime.Ch12
