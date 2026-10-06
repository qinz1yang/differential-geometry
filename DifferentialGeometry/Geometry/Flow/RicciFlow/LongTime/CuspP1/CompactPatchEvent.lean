import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelHistory

set_option autoImplicit false

/-!
# CP1-D6 (1): regular crossings are transported along `SamePresentation` of events
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

theorem regularCrossing_samePresentation_CPD6 {P Q P' Q' : OrientedThreeStage.{u}}
    {a s a' s' : ℝ} {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F) {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    F.RegularCrossing (carrierHomeo_CPD2 R.incomingStage_eq p)
      (carrierHomeo_CPD2 R.outgoingStage_eq q) := by
  obtain ⟨hP, hQ, ha, hs, hd, hc, ht, -, -, -, -, hold, hch, -, hout⟩ := R
  subst hP hQ ha hs
  cases E
  cases F
  dsimp only at hd hc ht hold hch hout
  subst hd hc
  have ht' := eq_of_heq ht
  subst ht'
  have hold' := eq_of_heq hold
  subst hold'
  have hout' := eq_of_heq hout
  subst hout'
  have hch' := eq_of_heq hch
  subst hch'
  exact h

end GC.LongTime.CuspP1
