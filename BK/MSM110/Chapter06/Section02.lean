/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.Uhlenbeck

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# MSM110 Chapter 6.2

Book companion for Uhlenbeck's trick.  The mathematical statement interfaces
live in `RicciFlower.RicciFlow.Evolution.Uhlenbeck`; this module only preserves
the book labels and naming.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section02

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- MSM110 Chapter 6.2, subequations `eq:e_a_evolution_equation`. -/
theorem eq_e_a_evolution_equation
    {D : RicciFlower.Realized.RealTimeInterval}
    (frameComp ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (h : FrameRicciODEInFrameOn (D := D) frameComp ricciOneUp) :
    FrameRicciODEInFrameOn (D := D) frameComp ricciOneUp :=
  h

/-- MSM110 Chapter 6.2, Lemma `lem:evolving_frame_calculation`. -/
theorem lem_evolving_frame_calculation
    {D : RicciFlower.Realized.RealTimeInterval}
    (metricComp Ric frameComp ricciOneUp :
      Real -> M -> Idx -> Idx -> Real)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hframe : FrameRicciODEInFrameOn (D := D) frameComp ricciOneUp)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp) :
    MovingFrameGramConstantOn (D := D) metricComp frameComp :=
  RicciFlower.RicciFlow.evolvingFrameGram_constant_of_ricciFlow
    (D := D) metricComp Ric frameComp ricciOneUp hmetric hframe hcompat

/-- MSM110 Chapter 6.2, corollary that an initially orthonormal evolving frame
remains orthonormal once the Gram matrix has been propagated from the initial
time.  The ODE/FTC step producing `MovingFrameGramValueConstantOn` lives below
the BK wrapper layer. -/
theorem cor_evolving_frame_orthonormal
    {D : RicciFlower.Realized.RealTimeInterval}
    (metricComp frameComp : Real -> M -> Idx -> Idx -> Real)
    (hconst : MovingFrameGramValueConstantOn (D := D) metricComp frameComp)
    (hinit : forall x : M,
      MovingFrameOrthonormalInFrame metricComp frameComp D.initial x) :
    forall (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      MovingFrameOrthonormalInFrame metricComp frameComp (t : Real) x :=
  RicciFlower.RicciFlow.evolvingFrame_orthonormal_of_initial
    (D := D) metricComp frameComp hconst hinit

/-- MSM110 Chapter 6.2, subequations `eq:ode_for_bundle_isomorphism`. -/
theorem eq_ode_for_bundle_isomorphism
    {D : RicciFlower.Realized.RealTimeInterval}
    (iota ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (h : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp) :
    BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp :=
  h

/-- MSM110 Chapter 6.2, Uhlenbeck isometry claim in component form. -/
theorem claim_uhlenbeck_bundle_isometry
    {D : RicciFlower.Realized.RealTimeInterval}
    (metricComp Ric iota ricciOneUp :
      Real -> M -> Idx -> Idx -> Real)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hiota : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp) :
    MovingFrameGramConstantOn (D := D) metricComp iota :=
  RicciFlower.RicciFlow.uhlenbeck_pullbackMetric_constant_of_ricciFlow
    (D := D) metricComp Ric iota ricciOneUp hmetric hiota hcompat

/-- MSM110 Chapter 6.2, equation `eq:uhlenbeck_pullback_of_riemann`. -/
theorem eq_uhlenbeck_pullback_of_riemann
    (iota : Real -> M -> Idx -> Idx -> Real)
    (Rm04 pulledRm : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h : UhlenbeckPullbackRmComponents iota Rm04 pulledRm) :
    UhlenbeckPullbackRmComponents iota Rm04 pulledRm :=
  h

/-- MSM110 Chapter 6.2, Lemma `lem:uhlenbeck_curvature_evolution_one`. -/
theorem lem_uhlenbeck_curvature_evolution_one
    {D : RicciFlower.Realized.RealTimeInterval}
    (iota : Real -> M -> Idx -> Idx -> Real)
    (Rm04 pulledRm roughLapRm04 roughLapD Borig Bpull :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (hiota : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp)
    (hpull : UhlenbeckPullbackRmComponents iota Rm04 pulledRm)
    (hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD)
    (hB : UhlenbeckPullbackBComponents iota Borig Bpull)
    (hrm : Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := D) Rm04 roughLapRm04 Borig ricciOneUp) :
    UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD Bpull :=
  RicciFlower.RicciFlow.uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow
    (D := D) iota Rm04 pulledRm roughLapRm04 roughLapD Borig Bpull ricciOneUp
    hiota hpull hlap hB hrm

/-- MSM110 Chapter 6.2, equation
`eq:rm_minus_evolution_minus_uhlenbeck_trick`. -/
theorem eq_rm_evolution_uhlenbeck_trick
    {D : RicciFlower.Realized.RealTimeInterval}
    (pulledRm roughLapD B :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h : UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD B) :
    UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD B :=
  h

end

end Section02
end Chapter06
end MSM110
end BK
