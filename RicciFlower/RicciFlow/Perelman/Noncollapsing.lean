/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Perelman.Entropy

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Perelman no-local-collapsing statement interfaces

This file records the MSM135 Chapter 6 noncollapsing vocabulary without
asserting the hard global analytic theorem.  The metric-ball, curvature-control,
volume, and singularity-model data are kept as explicit fields or hypotheses so
later passes can connect them to the geometric and measure APIs.
-/

namespace RicciFlower
namespace RicciFlow
namespace Perelman

noncomputable section

variable {M : Type*}

/-- A ball at a time whose curvature has been controlled at the relevant scale. -/
structure ScaleControlledBall (M : Type*) where
  center : M
  time : Real
  radius : Real
  volume : Real
  curvatureControlled : Prop

namespace ScaleControlledBall

/-- The small scale-controlled ball is contained in the large one at the
level currently expressible by this abstract interface: same center and time,
and no larger radius.  A later Riemannian ball API should turn this predicate
into actual set inclusion. -/
def Nested (small large : ScaleControlledBall M) : Prop :=
  large.center = small.center /\ large.time = small.time /\
    small.radius <= large.radius

end ScaleControlledBall

/-- A single scale-controlled ball is `kappa`-noncollapsed in dimension `n`. -/
def KappaNoncollapsedAtBall (n : Nat) (kappa : Real)
    (B : ScaleControlledBall M) : Prop :=
  0 < kappa ∧ 0 < B.radius ∧
    (B.curvatureControlled -> kappa * B.radius ^ n ≤ B.volume)

/-- `kappa`-noncollapsing on a chosen family of scale-controlled balls. -/
def KappaNoncollapsedOnBalls (n : Nat) (kappa : Real)
    (balls : Set (ScaleControlledBall M)) : Prop :=
  ∀ B : ScaleControlledBall M, B ∈ balls -> KappaNoncollapsedAtBall n kappa B

/-- Noncollapsing at all scales below `rho`, matching the book's scale-restricted
definition in labels `lbl647` and `lbl652`. -/
def RicciFlowKappaNoncollapsedBelowScale (n : Nat) (kappa rho : Real)
    (balls : Set (ScaleControlledBall M)) : Prop :=
  0 < rho ∧
    KappaNoncollapsedOnBalls n kappa {B : ScaleControlledBall M | B ∈ balls ∧ B.radius ≤ rho}

/-- Statement interface for preservation of noncollapsing under pointed limits,
label `lbl648`. -/
def KappaNoncollapsedPreservedUnderLimits (sourceLimit targetLimit : Prop) : Prop :=
  sourceLimit -> targetLimit

/-- Statement interface connecting noncollapsing to injectivity radius lower
bounds, labels `lbl650`-`lbl651`. -/
def KappaNoncollapsedImpliesInjectivityRadiusLowerBound
    (noncollapsed injectivityLowerBound : Prop) : Prop :=
  noncollapsed -> injectivityLowerBound

/-- Locally collapsing solution interface, label `lbl653`. -/
def LocallyCollapsingAtTime (_n : Nat) (_time : Real) (collapseWitness : Prop) : Prop :=
  collapseWitness

/-- No local collapsing, version A, label `lbl655`. -/
def NoLocalCollapsingTheoremA (n : Nat) (T rho : Real)
    (balls : Set (ScaleControlledBall M)) : Prop :=
  0 < T -> 0 < rho ->
    ∃ kappa : Real, 0 < kappa ∧ RicciFlowKappaNoncollapsedBelowScale n kappa rho balls

/-- No local collapsing, version B, label `lbl656`. -/
def NoLocalCollapsingTheoremB (n : Nat) (time : Real) (collapseWitness : Prop) : Prop :=
  ¬ LocallyCollapsingAtTime n time collapseWitness

/-- Equivalence of no local collapsing and the little-loop formulation,
label `lbl657`. -/
def NoLocalCollapsingLittleLoopEquivalent (nlc littleLoop : Prop) : Prop :=
  nlc ↔ littleLoop

/-- `mu`-lower-bounds-control-volume-ratios interface, labels `lbl661`-`lbl673`. -/
def MuControlsVolumeRatios (muLower volumeRatioLower : Real) : Prop :=
  muLower ≤ volumeRatioLower

/-- Singularity-model existence interface, labels `lbl674`-`lbl676`. -/
def FiniteTimeSingularityModelExists (hypothesis conclusion : Prop) : Prop :=
  hypothesis -> conclusion

/-- Improved no-local-collapsing theorem, labels `lbl677`-`lbl682`. -/
def ImprovedNoLocalCollapsingTheorem (n : Nat) (T rho : Real)
    (balls : Set (ScaleControlledBall M)) : Prop :=
  0 < T -> 0 < rho ->
    ∃ kappa : Real, 0 < kappa ∧ RicciFlowKappaNoncollapsedBelowScale n kappa rho balls

/-- Topping diameter-control style estimate, labels `lbl683`-`lbl686`. -/
def ToppingDiameterControl (diameterBound curvatureScaleBound : Real) : Prop :=
  diameterBound ≤ curvatureScaleBound

/-- Cheng eigenvalue comparison interface, labels `lbl690`-`lbl692`. -/
def ChengEigenvalueComparison (lowerBound eigenvalueEstimate : Real) : Prop :=
  lowerBound ≤ eigenvalueEstimate

/-- Weaker heat-equation version of the no-local-collapsing argument,
labels `lbl693`-`lbl696`. -/
def HeatEquationNoLocalCollapsingVariant (hypothesis conclusion : Prop) : Prop :=
  hypothesis -> conclusion

end

end Perelman
end RicciFlow
end RicciFlower
