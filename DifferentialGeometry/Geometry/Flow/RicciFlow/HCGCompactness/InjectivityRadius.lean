import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Basic

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

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The injectivity radius of `X` at `x` is at least `rho`.

This is the HCG-facing wrapper around the geometric injectivity radius
`DifferentialGeometry.Geometry.Riemannian.injRadius`.  (In the source
RicciFlower development this wrapped the normal-coordinate predicate
`Coordinates.Normal.injRadAtLeast`; on the DifferentialGeometry side the backend
is the exponential-map injectivity radius developed under
`Geometry.Comparison`.)  Uniform sequence lower bounds are recorded by
`BaseInjBound`. -/
def HasInjRadiusAt
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  0 < rho ∧
    ENNReal.ofReal rho ≤ Geometry.Riemannian.injRadius (I := I) X.metric x

/-- The HCG pointwise injectivity-radius predicate unfolds to a positive lower
bound on the geometric injectivity radius. -/
theorem hasInjRadiusAt_iff
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) :
    HasInjRadiusAt (I := I) X x rho ↔
      (letI : TopologicalSpace X.M := X.topology
       letI : ChartedSpace H X.M := X.charted
       letI : IsManifold I ∞ X.M := X.smooth
       letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
       0 < rho ∧
         ENNReal.ofReal rho ≤ Geometry.Riemannian.injRadius (I := I) X.metric x) :=
  Iff.rfl

/-- A positive radius bounded by the geometric injectivity radius gives the HCG
pointwise injectivity-radius lower bound. -/
theorem hasInjRadiusAt_of_le_injRadius
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real} (hpos : 0 < rho)
    (h :
      letI : TopologicalSpace X.M := X.topology
      letI : ChartedSpace H X.M := X.charted
      letI : IsManifold I ∞ X.M := X.smooth
      letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
      ENNReal.ofReal rho ≤ Geometry.Riemannian.injRadius (I := I) X.metric x) :
    HasInjRadiusAt (I := I) X x rho :=
  ⟨hpos, h⟩

/-- A smaller positive radius inherits an injectivity-radius lower bound. -/
theorem HasInjRadiusAt.mono
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho rho' : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hpos : 0 < rho') (hle : rho' <= rho) :
    HasInjRadiusAt (I := I) X x rho' := by
  rw [hasInjRadiusAt_iff] at h ⊢
  exact ⟨hpos, (ENNReal.ofReal_le_ofReal hle).trans h.2⟩

/-- Uniform injectivity-radius lower bound at the basepoints of a pointed
metric sequence. -/
structure BaseInjBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  ρ : Real
  pos : 0 < ρ
  bound : forall i : Nat, HasInjRadiusAt (I := I) (X.obj i) (X.obj i).basepoint ρ

namespace BaseInjBound

/-- Reindex a basepoint injectivity-radius lower bound along a subsequence. -/
def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : BaseInjBound (I := I) X) (f : Nat -> Nat) :
    BaseInjBound (I := I) (X.subseq f) where
  ρ := h.ρ
  pos := h.pos
  bound := by
    intro i
    simpa [PointedRiemannianSeq.subseq] using h.bound (f i)

end BaseInjBound

/-- Time-zero basepoint injectivity-radius input for a pointed flow sequence. -/
abbrev FlowBaseInjBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :=
  BaseInjBound (I := I) (X.atZero (I := I))

end HCGCompactness
end DifferentialGeometry
