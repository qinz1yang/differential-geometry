import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D

/-!
# CX-SPINE G8: a strict left window across a protected surgery crossing

The geometric input is exactly `ObservedHistory.surgery_no_shortcut_C11D`
(`Dist/SurgeryNoShortcutC11D.lean`, lines 80–109), together with a strict
post-surgery distance budget. Source SHA-256:
`ade65ab095132cccee5b96b21b284d03b5847594438f89e0d46dc2ee346dc197`.

An ENNReal positive margin converts the existing eventual no-shortcut estimate
to an eventual strict bound. The left-neighborhood basis then supplies one
interval on which every incoming time satisfies that bound. The incoming
metric is only evaluated strictly before the surgery time; at the surgery
time the hypothesis uses the actual post-stage metric. No trace is created.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Protected regular crossings and a strict post-stage distance budget give
an entire incoming left window with the same strict budget. -/
theorem ObservedHistory.exists_left_window_of_protected_crossing_CXSP
    (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    {pm qm : (H.stage e.castSucc).Carrier} {pp qp : (H.stage e.succ).Carrier}
    (hp : (H.event e).RegularCrossing pm pp) (hq : (H.event e).RegularCrossing qm qp)
    (hpprot : ∀ b, pp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hqprot : ∀ b, qp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    {X : ℝ≥0∞}
    (hpost : riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp < X) :
    ∃ d ∈ Ico (H.time e.castSucc) (H.time e.succ), ∀ u ∈ Ioo d (H.time e.succ),
      riemannianEDistOf (H.stageMetric e.castSucc u) pm qm < X := by
  obtain ⟨η, hη, hmargin⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hpost
  have hηreal : 0 < (η : ℝ) := by exact_mod_cast hη
  have hnear := H.surgery_no_shortcut_C11D e S hOld hcanonical hε hD hp hq
    hpprot hqprot hηreal
  have hstrict : ∀ᶠ u in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc u) pm qm < X := by
    filter_upwards [hnear] with u hu
    exact hu.trans_lt (by simpa only [ENNReal.ofReal_coe_nnreal] using hmargin)
  exact (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset
    (H.time_strictMono e.castSucc_lt_succ)).mp hstrict

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
