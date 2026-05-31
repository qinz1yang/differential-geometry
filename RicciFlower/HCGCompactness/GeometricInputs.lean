import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import RicciFlower.Coordinates.Normal.Frontier.SmoothChart
import RicciFlower.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Chapter 4 Geometric Inputs For HCG Compactness

This file pins down the theorem-facing black-box boundary for the deep
geometric inputs used in MSM135 Chapter 4's proof of Hamilton--Cheeger--Gromov
compactness.  The records below contain constants and estimate fields only; the
hard geometry is intentionally carried as a field to be produced later.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- Distance data for a pointed Riemannian sequence.

This is intended to be the Riemannian distance associated to each stored metric.
It is kept as theorem-facing input here because `PointedRiemannianManifold`
does not store the emetric/vector-bundle instances needed to make `dist`
available globally. -/
abbrev PointedSeqDistance
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Type _ :=
  forall k : Nat, (X.obj k).M -> (X.obj k).M -> Real

/-- Normal-chart data for one pointed Riemannian manifold, with the local
instances unpacked from the stored HCG object. -/
structure NormalChartFor
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M) :
    Type _ where
  vb :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
    VectorBundle Real E (TangentSpace I : X.M -> Type _)
  data :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    letI : VectorBundle Real E (TangentSpace I : X.M -> Type _) := vb
    RicciFlower.Coordinates.NormalChartData (I := I) X.metric x

/-- The model-coordinate transition map
`normal_y ∘ exp_x`, i.e. the form of `exp_y⁻¹ ∘ exp_x` consumed by the
Step B/C approximate-isometry estimates. -/
noncomputable def normalTransitionMap
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {x y : X.M}
    (Nx : NormalChartFor (I := I) X x)
    (Ny : NormalChartFor (I := I) X y) :
    E -> E :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : VectorBundle Real E (TangentSpace I : X.M -> Type _) := Nx.vb
  fun z : E =>
    Ny.data.localChart.ext
      (Nx.data.exp ((RicciFlower.Coordinates.normalCoordLinearEquiv (I := I) x).symm z))

/-- Derivative bound for one normal-coordinate transition map. -/
def NormalTransitionDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {x y : X.M}
    (Nx : NormalChartFor (I := I) X x)
    (Ny : NormalChartFor (I := I) X y)
    (p : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : VectorBundle Real E (TangentSpace I : X.M -> Type _) := Nx.vb
  forall z : E,
    z ∈ Metric.ball (0 : E) Nx.data.radius ->
      Nx.data.exp ((RicciFlower.Coordinates.normalCoordLinearEquiv (I := I) x).symm z) ∈
          Ny.data.localChart.source ->
        ‖iteratedFDeriv Real p (normalTransitionMap (I := I) X Nx Ny) z‖ <= C

/-- MSM135 Chapter 4, Proposition `lbl384`:
Cheeger--Gromov--Taylor injectivity-radius decay from basepoint injectivity
and curvature control.

The field `decay` is the deep external theorem.  It is consumed by Step A
covering and good-ball constructions. -/
structure InjRadiusDecayInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  baseInj : BaseInjBound (I := I) X
  dist : PointedSeqDistance (I := I) X
  a : Real
  C : Real
  a_pos : 0 < a
  C_nonneg : 0 <= C
  decay :
    forall k : Nat, forall x : (X.obj k).M,
      HasInjRadiusAt (I := I) (X.obj k) x
        (a * (min baseInj.ρ 1) ^ Module.finrank Real E *
          Real.exp (-C * dist k x (X.obj k).basepoint))

/-- MSM135 Chapter 4 volume-comparison input, used after Proposition `lbl384`:
the Bishop--Gromov comparison estimate gives a bounded intersection
multiplicity `I(n,C₀)`.

Mathlib may eventually provide a Bishop--Gromov theorem directly; until then,
`ballMult` is the weakest bounded-overlap form consumed by Step A. -/
structure VolumeComparisonInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedSeqDistance (I := I) X
  Imult : Nat
  /-- Consumed by Step A: in any `r`-separated finite center family, at most
  `Imult` centers can lie in a fixed controlled ball. -/
  ballMult :
    forall k : Nat, forall {α : Type u}, [Fintype α] -> [DecidableEq α] ->
      forall centers : α -> (X.obj k).M, forall r : Real, 0 < r ->
        (forall i j : α, i ≠ j ->
          r <= dist k (centers i) (centers j)) ->
        forall z : (X.obj k).M, forall J : Finset α,
          (forall j : α, j ∈ J ->
            dist k (centers j) z <= 4 * r) ->
          J.card <= Imult

/-- MSM135 Chapter 4, section `lbl-2103`:
Jacobi/Rauch comparison bounds for derivatives of normal-coordinate transition
maps `exp_y⁻¹ ∘ exp_x`.

The field `exp_inv_deriv` is the deep external theorem.  It is phrased in model
coordinates using `NormalChartData`, matching the Step B/C maps built from
local exponential charts. -/
structure ExpInverseDerivBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  derivC : Nat -> Real
  derivC_nonneg : forall p : Nat, 0 <= derivC p
  /-- Consumed by Steps B/C: uniform `C^p` bounds for the normal-coordinate
  transition map on the overlap of two injectivity charts. -/
  exp_inv_deriv :
    forall k p : Nat,
      forall x y : (X.obj k).M,
        forall Nx : NormalChartFor (I := I) (X.obj k) x,
          forall Ny : NormalChartFor (I := I) (X.obj k) y,
            NormalTransitionDerivBound (I := I) (X.obj k) Nx Ny p (derivC p)

end HCGCompactness
end RicciFlower
