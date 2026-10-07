import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventProtectedBalls
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceConcat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

/-!
# CH12-O77 G1: the region invariant `Reg (R⁺)` of KL §82 (R6 dispositions D-R6-1 / D-R6-4)

`[FROZEN] CH12-O77 Reg`.  The moving-ball **region** of KL §82, pp. 161–162 (not the material
`isTracedRegion` of KL §68):

* the centre is one same-history trace `X` on `[a, u]` (a `BackwardPointTrace`); the slice of the
  region at `v ∈ [a, u]` is the metric ball `B_v(X v, r)` of `stageMetric (activeStage v) v`
  (`activeStage` is right-continuous: at an event time this is the **outgoing** slice);
* `SectionalBoundedBelowAt (-r⁻²)` on every slice ball (sectional, not scalar; the only copy);
* finite curvature `∃ K, R ≤ K` on every slice ball (the analytic shadow of compact containment of
  the region in the smooth part; = `[FROZEN] CH12-O78` (Reg-fin K) under `∃ K`; no size control);
* at every event `i` with event time in `(a, u]` (`activeStage a ≤ i.castSucc`,
  `i.succ ≤ activeStage u`) the **incoming** `r`-ball (terminal limit metric on the regular open
  set, centred at the incoming centre `X(i.castSucc)`) lies in the common retained open set
  `interior (val '' old)` and corresponds through the regular identification (`RegularCrossing`)
  to the outgoing ball `B_out(X(i.succ), r) ⊆ interior (range oldOutput)`: for every `0 < ρ ≤ r`
  the crossing is a bijection `B_term(p, ρ) ↔ B_out(q, ρ)` (`RegEvent_O77`, KL p.161 (3));
* strict-interior compact containment: the closed incoming balls of radius `ρ < r` are compact.
  (Local smooth continuation: within a stage static curves are the identity of the carrier; across
  an event a point of the region continues exactly through the bijective crossing above.)

There is **no** clause "every `q ∈ B_v(X v, r)` traces back to `a`" and no `r₊ > r` field.
Event convention: the outgoing slice is used at every event time of `[a, u]`; the incoming
correspondence is imposed at every event time of `(a, u]` (so the bottom slice at an event time is
outgoing only, the top one carries both readings).  `reg_top_O77` is the depth-0 inhabitant.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- `[FROZEN] CH12-O77 Reg`, event clause (KL p.161 (3)): the incoming `r`-ball about `p`
(terminal metric, centre `p' : terminalRegularOpen`, `p'.val = p`) lies in the retained open set
and corresponds through the regular identification to the outgoing ball `B_out(q, r)`, which lies in
`interior (range oldOutput)`; the correspondence is radius-preserving for every `0 < ρ ≤ r`; the
closed incoming balls of radius `ρ < r` are compact. -/
def RegEvent_O77 {P Q : OrientedThreeStage.{u}} {s₀ s₁ : ℝ} (E : MetricCutCapEvent P Q s₀ s₁)
    (p : P.Carrier) (q : Q.Carrier) (r : ℝ) : Prop :=
  ∃ p' : E.incoming.terminalRegularOpen, p'.val = p ∧
    riemannianBallOf E.outputMetric q r ⊆ interior (range E.oldOutput) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      (∀ z ∈ riemannianBallOf E.terminal.metric p' ρ,
        z.val ∈ interior (Subtype.val '' E.old) ∧
          ∃ y ∈ riemannianBallOf E.outputMetric q ρ, E.RegularCrossing z.val y) ∧
      (∀ y ∈ riemannianBallOf E.outputMetric q ρ,
        ∃ z ∈ riemannianBallOf E.terminal.metric p' ρ, E.RegularCrossing z.val y)) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ρ < r → IsCompact (riemannianClosedBallOf E.terminal.metric p' ρ))

/-- `[FROZEN] CH12-O77 Reg` = `(R⁺)`: `Reg(N, X; a, u; r)` (sectional lower bound on every slice
ball; finite scalar bound on the region; the incoming/outgoing event clause at every event time of
`(a, u]`). -/
def Reg_O77 (N : ObservedHistory.{u}) {a u : Icc (0 : ℝ) N.horizon} (hau : a ≤ u)
    {x : (N.stageAt u).Carrier}
    (X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x)
    (r : ℝ) : Prop :=
  (∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
    ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
        (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
      SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) ∧
  (∃ K : ℝ, ∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
    ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
        (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
      metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ K) ∧
  ∀ (i : Fin N.eventCount) (hf : N.activeStage a ≤ i.castSucc) (hl : i.succ ≤ N.activeStage u),
    RegEvent_O77 (N.event i)
      (X.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))
      (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) r

/-- Depth-`0` inhabitant: the singleton trace at `u` is a region of radius `r` on `[u, u]` as soon
as the top slice ball carries the sectional bound (compact top stage: finite scalar bound; no event
time lies in `(u, u]`). -/
theorem reg_top_O77 (N : ObservedHistory.{u}) (u : Icc (0 : ℝ) N.horizon)
    (x : (N.stageAt u).Carrier) {r : ℝ}
    (hsec0 : ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage u) u) x r,
      SectionalBoundedBelowAt (N.stageMetric (N.activeStage u) u) q (-(r ^ 2)⁻¹)) :
    Reg_O77 N (le_refl u) (BackwardPointTrace.singleton N (N.activeStage u) x) r := by
  obtain ⟨K, hK⟩ := (isCompact_univ.image
    (metricScalar_smooth (N.stageMetric (N.activeStage u) u)).continuous).bddAbove
  refine ⟨fun v hav hvu q hq => ?_, ⟨K, fun v hav hvu q _ => ?_⟩, fun i hf hl => ?_⟩
  · obtain rfl : v = u := le_antisymm hvu hav
    exact hsec0 q hq
  · obtain rfl : v = u := le_antisymm hvu hav
    exact hK ⟨q, mem_univ _, rfl⟩
  · exact absurd (hl.trans hf) (not_le_of_gt (Fin.castSucc_lt_succ (i := i)))

end GC.LongTime.Ch12
