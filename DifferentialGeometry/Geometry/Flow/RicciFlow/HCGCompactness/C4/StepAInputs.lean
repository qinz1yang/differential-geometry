import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step A honest inputs (A0 / A0')

These three structures are the self-contained Step A honest inputs of MSM135
Chapter 4 (the proof of `metricCompactness`, Theorem 3.9):

* `PointedSeqDistance` — the supplied Riemannian distance per sequence term;
* `InjRadiusDecayInput` — the Cheeger--Gromov--Taylor injectivity-radius decay
  estimate (Proposition `lbl384`, Step A input A0);
* `VolumeComparisonInput` — the Bishop--Gromov bounded intersection multiplicity
  (Step A input A0').

They were relocated here from `GeometricInputs.lean`, whose S6 exp⁻¹-derivative
machinery (`NormalChartFor`, `normalTransitionMap`, `ExpInverseDerivBoundInput`)
currently does not compile because of a dangling
`RicciFlower.Coordinates.NormalChartData` reference.  These Step A inputs do not
depend on that machinery, so they live in their own building module.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
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

namespace InjRadiusDecayInput

/-- Reindex the injectivity-radius decay input along a subsequence. -/
def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (f : Nat -> Nat) :
    InjRadiusDecayInput (I := I) (X.subseq f) where
  baseInj := hd.baseInj.subseq f
  dist := fun k x y => hd.dist (f k) x y
  a := hd.a
  C := hd.C
  a_pos := hd.a_pos
  C_nonneg := hd.C_nonneg
  decay := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using hd.decay (f k) x

end InjRadiusDecayInput

/-- MSM135 Chapter 4 volume-comparison input, used after Proposition `lbl384`:
the Bishop--Gromov comparison estimate gives a bounded intersection
multiplicity `I(n,C₀)`.

Mathlib may eventually provide a Bishop--Gromov theorem directly; until then,
`ballMult` is the weakest bounded-overlap form consumed by Step A.  The
containment-to-separation ratio `m` is a parameter (with multiplicity `Imult m`):
the Zorn-net multiplicity uses `m = 4`, while the `lbl383` item-5 intersecting-ball
count needs a larger `λ`-ratio-dependent constant.

The bound is capped at the containing scale `m * r ≤ r0`, not merely at the
separation scale `r ≤ r0`.  The joint cap is mathematically necessary, not a
convenience: with only `Ric ≥ -(n-1)C₀` the comparison ratio `V(m·r)/V(r/2)`
grows like `e^{(n-1)(m-1/2)√C₀·r}`, so allowing `m * r` to be unbounded would
again make a fixed multiplicity bound false on hyperbolic-like members.  Step A
only ever uses fixed ratios, so its producers instantiate `r0` above the
largest ratio times `λ[0]`. -/
structure VolumeComparisonInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedSeqDistance (I := I) X
  /-- The separation-scale cap below which the packing bound applies. -/
  r0 : Real
  r0_pos : 0 < r0
  Imult : Real -> Nat
  /-- Consumed by Step A: in any `r`-separated finite center family with
  `m * r ≤ r0`, at most `Imult m` centers can lie within `m·r` of a fixed
  point. -/
  ballMult :
    forall (m : Real), forall k : Nat, forall {α : Type u}, [Fintype α] -> [DecidableEq α] ->
      forall centers : α -> (X.obj k).M, forall r : Real, 0 < r -> m * r <= r0 ->
        (forall i j : α, i ≠ j ->
          r <= dist k (centers i) (centers j)) ->
        forall z : (X.obj k).M, forall J : Finset α,
          (forall j : α, j ∈ J ->
            dist k (centers j) z <= m * r) ->
          J.card <= Imult m

namespace VolumeComparisonInput

/-- Reindex the volume-comparison input along a subsequence. -/
def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (vc : VolumeComparisonInput (I := I) X) (f : Nat -> Nat) :
    VolumeComparisonInput (I := I) (X.subseq f) where
  dist := fun k x y => vc.dist (f k) x y
  r0 := vc.r0
  r0_pos := vc.r0_pos
  Imult := vc.Imult
  ballMult := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    exact vc.ballMult m (f k) centers r hr hcap hsep z J hJz

end VolumeComparisonInput

end HCGCompactness
end DifferentialGeometry
