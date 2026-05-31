import RicciFlower.Coordinates.Normal.InjectivityRadius
import RicciFlower.HCGCompactness.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Injectivity-Radius Inputs

This file contains theorem-facing injectivity-radius predicates for the
Hamilton--Cheeger--Gromov compactness interface.  The pointwise predicate is
the HCG wrapper around the normal-coordinate injectivity-radius backend.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The normal-coordinate injectivity radius of `X` at `x` is at least `rho`.

This is the HCG-facing wrapper around
`Coordinates.Normal.injRadAtLeast`; uniform sequence lower bounds are still
recorded by `BaseInjBound`. -/
def HasInjRadiusAt
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  RicciFlower.Coordinates.Normal.injRadAtLeast (I := I) X.metric x rho

/-- The HCG pointwise injectivity-radius predicate is definitionally the
normal-coordinate lower-bound predicate. -/
theorem hasInjRadiusAt_iff
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) :
    HasInjRadiusAt (I := I) X x rho ↔
      (letI : TopologicalSpace X.M := X.topology
       letI : ChartedSpace H X.M := X.charted
       letI : IsManifold I ∞ X.M := X.smooth
       letI : SigmaCompactSpace X.M := X.sigmaCompact
       letI : T2Space X.M := X.t2
       RicciFlower.Coordinates.Normal.injRadAtLeast (I := I) X.metric x rho) := by
  rfl

/-- An admissible normal-coordinate radius gives the HCG pointwise
injectivity-radius lower bound. -/
theorem hasInjRadiusAt_of_admissible
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real}
    (h :
      letI : TopologicalSpace X.M := X.topology
      letI : ChartedSpace H X.M := X.charted
      letI : IsManifold I ∞ X.M := X.smooth
      letI : SigmaCompactSpace X.M := X.sigmaCompact
      letI : T2Space X.M := X.t2
      RicciFlower.Coordinates.Normal.injRadAdmissible (I := I) X.metric x rho) :
    HasInjRadiusAt (I := I) X x rho := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  exact RicciFlower.Coordinates.Normal.injRadAtLeast_of_admissible (I := I) h

/-- Uniform injectivity-radius lower bound at the basepoints of a pointed
metric sequence. -/
structure BaseInjBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  ρ : Real
  pos : 0 < ρ
  bound : forall i : Nat, HasInjRadiusAt (I := I) (X.obj i) (X.obj i).basepoint ρ

/-- Time-zero basepoint injectivity-radius input for a pointed flow sequence. -/
abbrev FlowBaseInjBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :=
  BaseInjBound (I := I) (X.atZero (I := I))

end HCGCompactness
end RicciFlower
