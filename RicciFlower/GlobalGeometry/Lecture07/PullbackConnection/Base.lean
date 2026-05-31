import RicciFlower.GlobalGeometry.Lecture07.Geodesics
import RicciFlower.VectorBundle.LocalFrameRegularity
import RicciFlower.VectorBundle.PartialMfderiv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: pullback connection interface

Mathlib already provides pullback vector bundles: for a smooth map `f : N -> M`
and a vector bundle `V` over `M`, the bundle `f *ᵖ V` is a vector bundle over
`N`.

This file adds the first RicciFlower-native connection layer over that
pullback bundle.  It is intentionally relation-valued: a derivative of a
pullback section is realized by an ambient section of `V`.  This is the
general version of the global-extension technology used earlier for geodesics,
but the public object now lives on the pullback bundle.

The file does not claim to construct a bundled
`CovariantDerivative I' F (f *ᵖ V)`.  That stronger construction requires a
well-definedness theorem for arbitrary pullback sections, or a genuine
pullback-connection API.  The goal here is the canonical interface that later
curve, geodesic, and Jacobi-field proofs should consume.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']
variable {H' : Type*} [TopologicalSpace H']
variable {I' : ModelWithCorners Real E' H'}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {V : M -> Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x : M, AddCommGroup (V x)] [∀ x : M, Module Real (V x)]
variable [∀ x : M, TopologicalSpace (V x)]
variable [∀ x : M, IsTopologicalAddGroup (V x)]
variable [∀ x : M, ContinuousSMul Real (V x)]
variable [FiberBundle F V] [VectorBundle Real F V]

/-! ## General pullback sections -/

/-- A section of the pullback bundle `f *ᵖ V`.

Mathlib's pullback bundle is a type synonym for `V ∘ f`; using the explicit
dependent function type here keeps later formulas stable and avoids asking type
class search to recover the model fiber from the notation. -/
abbrev PullbackSection (f : N -> M) (V : M -> Type*) :=
  (y : N) -> V (f y)

/-- Pull an ambient section of `V` back along `f`. -/
def pullbackSectionOf (f : N -> M) (σ : (x : M) -> V x) :
    PullbackSection f V :=
  fun y => σ (f y)

@[simp] theorem pullbackSectionOf_apply
    (f : N -> M) (σ : (x : M) -> V x) (y : N) :
    pullbackSectionOf (V := V) f σ y = σ (f y) :=
  rfl

/-- A section is differentiable at a point, written using the explicit total
space map.  This avoids typeclass inference problems around the notation
`T% σ` for arbitrary vector bundles. -/
def MDiffSectionAt (σ : (x : M) -> V x) (x : M) : Prop :=
  MDiffAt (fun y : M => (⟨y, σ y⟩ : TotalSpace F V)) x

/-- Convert the explicit total-space formulation of section differentiability
back to mathlib's `T%` notation when an API expects it. -/
theorem mdiffSectionAt_tPercent
    {σ : (x : M) -> V x} {x : M}
    (hσ : MDiffSectionAt (I := I) (F := F) (V := V) σ x) :
    MDiffAt (T% σ) x := by
  simpa [MDiffSectionAt] using hσ

/-- Convert mathlib's `T%` notation for section differentiability into the
explicit total-space formulation used by the pullback-connection API. -/
theorem mdiffSectionAt_of_tPercent
    {σ : (x : M) -> V x} {x : M}
    (hσ : MDiffAt (T% σ) x) :
    MDiffSectionAt (I := I) (F := F) (V := V) σ x := by
  simpa [MDiffSectionAt] using hσ

/-- An ambient section `σ` realizes a pullback section `S` near `y`.

This is agreement as sections of `f *ᵖ V`, i.e. after restricting `σ` along
`f`. -/
def PullbackSectionRealizedByAt
    (f : N -> M) (S : PullbackSection f V)
    (σ : (x : M) -> V x) (y : N) : Prop :=
  ∀ᶠ z in 𝓝 y, S z = σ (f z)

/-- A smooth ambient representative for a pullback section near `y`. -/
def IsPullbackSectionRepresentativeAt
    (f : N -> M) (S : PullbackSection f V)
    (σ : (x : M) -> V x) (y : N) : Prop :=
  MDiffSectionAt (I := I) (F := F) (V := V) σ (f y) ∧
    PullbackSectionRealizedByAt (V := V) f S σ y

/-- The value of the pullback connection on one ambient representative.

On paper this is `(f^*∇)_u S`, computed using a representative `σ` with
`S = σ ∘ f` near `y`:

`(f^*∇)_u S = ∇_{df_y u} σ`.
-/
def pullbackCovDerivOfRepresentativeAt
    (cov : CovariantDerivative I F V) (f : N -> M)
    (σ : (x : M) -> V x) (y : N) (u : TangentSpace I' y) :
    V (f y) :=
  (cov σ (f y)) ((mfderiv I' I f y) u)

/-- If two ambient representatives agree near the target point, then the
representative formula for the pullback covariant derivative is independent of
that choice.

This is the direct high-level congruence lemma coming from mathlib's
`CovariantDerivative` locality.  The stronger pullback-representative theorem
below only assumes agreement after restriction along `f`. -/
theorem pullbackCovDerivOfRepresentativeAt_eq_of_eventuallyEq_target
    {cov : CovariantDerivative I F V} {f : N -> M}
    {σ τ : (x : M) -> V x} {y : N} {u : TangentSpace I' y}
    (hσ : MDiffSectionAt (I := I) (F := F) (V := V) σ (f y))
    (hτ : MDiffSectionAt (I := I) (F := F) (V := V) τ (f y))
    (hστ : ∀ᶠ x in 𝓝 (f y), σ x = τ x) :
    pullbackCovDerivOfRepresentativeAt (I' := I') cov f σ y u =
      pullbackCovDerivOfRepresentativeAt (I' := I') cov f τ y u := by
  have hcov :
      cov σ (f y) = cov τ (f y) :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (x := f y)
      (mdiffSectionAt_tPercent (I := I) (F := F) (V := V) hσ)
      (mdiffSectionAt_tPercent (I := I) (F := F) (V := V) hτ)
      (by simp) hστ
  simp [pullbackCovDerivOfRepresentativeAt, hcov]

/-- Relation-valued pullback covariant derivative at a point.

The relation includes differentiability of `f` at `y`, an ambient smooth
representative of the pullback section near `y`, and the representative formula
for the derivative.  It is deliberately relation-valued until we have the
well-definedness theorem for arbitrary pullback sections. -/
def HasPullbackCovariantDerivativeAt
    (cov : CovariantDerivative I F V) (f : N -> M)
    (S : PullbackSection f V) (y : N) (u : TangentSpace I' y)
    (A : V (f y)) : Prop :=
  MDifferentiableAt I' I f y ∧
    ∃ σ : (x : M) -> V x,
      IsPullbackSectionRepresentativeAt (I := I) (F := F) (V := V) f S σ y ∧
        A = pullbackCovDerivOfRepresentativeAt (I' := I') cov f σ y u

/-- The pulled-back ambient section has the expected pullback covariant
derivative. -/
theorem hasPullbackCovariantDerivativeAt_pullbackSectionOf
    {cov : CovariantDerivative I F V} {f : N -> M}
    {σ : (x : M) -> V x} {y : N} {u : TangentSpace I' y}
    (hf : MDifferentiableAt I' I f y)
    (hσ : MDiffSectionAt (I := I) (F := F) (V := V) σ (f y)) :
    HasPullbackCovariantDerivativeAt (I := I) (I' := I') cov f
      (pullbackSectionOf (V := V) f σ) y u
      (pullbackCovDerivOfRepresentativeAt (I' := I') cov f σ y u) := by
  exact ⟨hf, σ, ⟨hσ, Filter.Eventually.of_forall fun _z => rfl⟩, rfl⟩

/-! ## Local-frame pullback derivative candidate -/


end Lecture07
end GlobalGeometry
end RicciFlower
