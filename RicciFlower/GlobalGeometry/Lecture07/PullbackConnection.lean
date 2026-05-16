import RicciFlower.GlobalGeometry.Lecture07.Geodesics
import RicciFlower.VectorBundle.LocalFrameRegularity
import RicciFlower.VectorBundle.PartialMfderiv
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

/-! ## Tangent-bundle representative well-definedness -/

section TangentWellDefinedness

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- Scalar chain-rule helper for pullback representative comparisons.

If two scalar functions agree after composition with `f` near `y`, then their
exterior derivatives at `f y` agree on the tangent vector `df_y u`. -/
private theorem extDerivFun_comp_eq_of_eventuallyEq
    {φ ψ : M -> Real} {f : N -> M} {y : N} {u : TangentSpace I' y}
    (hf : MDifferentiableAt I' I f y)
    (hφ : MDifferentiableAt I 𝓘(Real, Real) φ (f y))
    (hψ : MDifferentiableAt I 𝓘(Real, Real) ψ (f y))
    (hφψ : ∀ᶠ z in 𝓝 y, φ (f z) = ψ (f z)) :
    extDerivFun (I := I) φ (f y) ((mfderiv I' I f y) u) =
      extDerivFun (I := I) ψ (f y) ((mfderiv I' I f y) u) := by
  have hmf :
      mfderiv I' 𝓘(Real, Real) (fun z : N => φ (f z)) y =
        mfderiv I' 𝓘(Real, Real) (fun z : N => ψ (f z)) y :=
    Filter.EventuallyEq.mfderiv_eq (I := I') (I' := 𝓘(Real, Real)) hφψ
  have hmf_apply :
      mfderiv I' 𝓘(Real, Real) (fun z : N => φ (f z)) y u =
        mfderiv I' 𝓘(Real, Real) (fun z : N => ψ (f z)) y u :=
    congrArg (fun L => L u) hmf
  have hφcomp :
      mfderiv I' 𝓘(Real, Real) (fun z : N => φ (f z)) y u =
        mfderiv I 𝓘(Real, Real) φ (f y) ((mfderiv I' I f y) u) := by
    simpa [Function.comp_def] using
      (mfderiv_comp_apply
        (I := I') (I' := I) (I'' := 𝓘(Real, Real))
        (g := φ) (f := f) (x := y) hφ hf u)
  have hψcomp :
      mfderiv I' 𝓘(Real, Real) (fun z : N => ψ (f z)) y u =
        mfderiv I 𝓘(Real, Real) ψ (f y) ((mfderiv I' I f y) u) := by
    simpa [Function.comp_def] using
      (mfderiv_comp_apply
        (I := I') (I' := I) (I'' := 𝓘(Real, Real))
        (g := ψ) (f := f) (x := y) hψ hf u)
  rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
  change
    (mfderiv I 𝓘(Real, Real) φ (f y) ((mfderiv I' I f y) u) : Real) =
      (mfderiv I 𝓘(Real, Real) ψ (f y) ((mfderiv I' I f y) u) : Real)
  rw [← hφcomp, ← hψcomp]
  exact hmf_apply

/-- A local-frame coefficient of a tangent vector is the corresponding
coordinate in the pointwise basis. -/
private theorem localFrame_coeff_eq_basis_repr
    {ι : Type*}
    (e : Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (k : ι)
    (v : TangentSpace I x) :
    e.localFrame_coeff I b k x v = (e.basisAt b hx).repr v k := by
  classical
  let s : (p : M) -> TangentSpace I p :=
    fun p => if h : p = x then h ▸ v else 0
  have hsx : s x = v := by simp [s]
  have hcoeff := e.localFrame_coeff_apply_of_mem_baseSet (I := I) b hx s k
  simpa [hsx] using hcoeff

/-- Pullback covariant derivatives of tangent-bundle representatives are
well-defined: two smooth ambient vector fields that realize the same pullback
section near `y` give the same derivative in direction `u`. -/
theorem pullbackCovDerivOfRepresentativeAt_eq_of_tangent_realizes_same
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {X Y : (x : M) -> TangentSpace I x} {y : N} {u : TangentSpace I' y}
    (hf : MDifferentiableAt I' I f y)
    (hX : IsPullbackSectionRepresentativeAt (I := I) (F := E)
      (V := TangentSpace I) f S X y)
    (hY : IsPullbackSectionRepresentativeAt (I := I) (F := E)
      (V := TangentSpace I) f S Y y) :
    pullbackCovDerivOfRepresentativeAt (I' := I') cov f X y u =
      pullbackCovDerivOfRepresentativeAt (I' := I') cov f Y y u := by
  classical
  let x : M := f y
  let w : TangentSpace I x := (mfderiv I' I f y) u
  let e := trivializationAt E (TangentSpace I : M -> Type _) x
  let b := Module.finBasis Real E
  have hx : x ∈ e.baseSet := by simp [e]
  have hXdiff : MDiffAt (T% X) x :=
    mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hX.1
  have hYdiff : MDiffAt (T% Y) x :=
    mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hY.1
  have hXY_pull :
      ∀ᶠ z in 𝓝 y, X (f z) = Y (f z) := by
    filter_upwards [hX.2, hY.2] with z hXz hYz
    exact hXz.symm.trans hYz
  have hXY_at : X x = Y x := by
    simpa [x] using hXY_pull.self_of_nhds
  have hcoeff_eq :
      ∀ k : Fin (Module.finrank Real E),
        e.localFrame_coeff I b k x
            ((cov X x) w) =
          e.localFrame_coeff I b k x
            ((cov Y x) w) := by
    intro k
    let φX : M -> Real := fun p => e.localFrame_coeff I b k p (X p)
    let φY : M -> Real := fun p => e.localFrame_coeff I b k p (Y p)
    have hφX : MDifferentiableAt I 𝓘(Real, Real) φX x := by
      simpa [φX] using
        (mdifferentiableAt_localFrame_coeff
          (I := I) (e := e) (b := b) hx hXdiff k)
    have hφY : MDifferentiableAt I 𝓘(Real, Real) φY x := by
      simpa [φY] using
        (mdifferentiableAt_localFrame_coeff
          (I := I) (e := e) (b := b) hx hYdiff k)
    have hφXY :
        ∀ᶠ z in 𝓝 y, φX (f z) = φY (f z) := by
      filter_upwards [hXY_pull] with z hz
      simp [φX, φY, hz]
    have hderiv :
        extDerivFun (I := I) φX x w =
          extDerivFun (I := I) φY x w := by
      simpa [x, w, φX, φY] using
        extDerivFun_comp_eq_of_eventuallyEq
          (I := I) (I' := I') (f := f) (y := y) (u := u)
          hf hφX hφY hφXY
    have hlocalX :=
      covariantDerivative_localFrame_coeff_eq_along
        (I := I) cov e b hx hXdiff w k
    have hlocalY :=
      covariantDerivative_localFrame_coeff_eq_along
        (I := I) cov e b hx hYdiff w k
    have hsum :
        (∑ j : Fin (Module.finrank Real E),
            e.localFrame_coeff I b j x (X x) *
              e.localFrame_coeff I b k x
                ((cov (e.localFrame b j) x) w)) =
          ∑ j : Fin (Module.finrank Real E),
            e.localFrame_coeff I b j x (Y x) *
              e.localFrame_coeff I b k x
                ((cov (e.localFrame b j) x) w) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hXY_at]
    calc
      e.localFrame_coeff I b k x ((cov X x) w)
          = extDerivFun (I := I) φX x w +
              ∑ j : Fin (Module.finrank Real E),
                e.localFrame_coeff I b j x (X x) *
                  e.localFrame_coeff I b k x
                    ((cov (e.localFrame b j) x) w) := by
            simpa [φX] using hlocalX
      _ = extDerivFun (I := I) φY x w +
              ∑ j : Fin (Module.finrank Real E),
                e.localFrame_coeff I b j x (Y x) *
                  e.localFrame_coeff I b k x
                    ((cov (e.localFrame b j) x) w) := by
            rw [hderiv, hsum]
      _ = e.localFrame_coeff I b k x ((cov Y x) w) := by
            simpa [φY] using hlocalY.symm
  change (cov X x) w = (cov Y x) w
  apply (e.basisAt b hx).ext_elem
  intro k
  rw [← localFrame_coeff_eq_basis_repr (I := I) e b hx k ((cov X x) w)]
  rw [← localFrame_coeff_eq_basis_repr (I := I) e b hx k ((cov Y x) w)]
  exact hcoeff_eq k

/-- Uniqueness of the tangent-bundle pullback covariant derivative relation. -/
theorem HasPullbackCovariantDerivativeAt.unique_tangent
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y}
    {A B : TangentSpace I (f y)}
    (hA : HasPullbackCovariantDerivativeAt
      (I := I) (I' := I') (F := E) (V := TangentSpace I) cov f S y u A)
    (hB : HasPullbackCovariantDerivativeAt
      (I := I) (I' := I') (F := E) (V := TangentSpace I) cov f S y u B) :
    A = B := by
  rcases hA with ⟨hf, X, hX, hAeq⟩
  rcases hB with ⟨_, Y, hY, hBeq⟩
  rw [hAeq, hBeq]
  exact pullbackCovDerivOfRepresentativeAt_eq_of_tangent_realizes_same
    (I := I) (I' := I') hf hX hY

end TangentWellDefinedness

/-! ## Curves as pullback bundles -/

section Curves

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- A global field realizes the velocity near one parameter value.

This is the local version of `RealizesVelocity`, used as a compatibility
producer for the pullback-bundle acceleration relation. -/
def RealizesVelocityEventuallyAt (gamma : Curve M) (X : GlobalVectorField I M)
    (t : Real) : Prop :=
  Filter.Eventually
    (fun s : Real => X (gamma s) = curveVelocity I gamma s) (𝓝 t)

/-- A smooth local velocity extension at one parameter value.

This is legacy/global-extension data.  Public geodesic-equation predicates
should use `HasPullbackCovariantAccelerationAt`; this predicate remains as a
producer until along-curve fields are handled directly. -/
def IsVelocityExtensionAt (gamma : Curve M) (t : Real)
    (X : GlobalVectorField I M) : Prop :=
  MDiffAt (T% X) (gamma t) ∧
    RealizesVelocityEventuallyAt (I := I) gamma X t

/-- The pullback-connection derivative along a real curve.

This is the pullback-bundle version of differentiating a vector field along
`gamma`.  The direction is the canonical vector `1` on the parameter line. -/
def HasPullbackCovariantDerivativeAlongCurveAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (S : VectorFieldAlong I gamma)
    (t : Real) (A : TangentSpace I (gamma t)) : Prop :=
  HasPullbackCovariantDerivativeAt
    (I := I) (I' := 𝓘(Real, Real))
    (F := E) (V := TangentSpace I)
    cov gamma S t (1 : TangentSpace 𝓘(Real, Real) t) A

/-- Pullback-bundle covariant acceleration of a curve.

This is the intended replacement target for the older global-extension
acceleration relation. -/
def HasPullbackCovariantAccelerationAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (A : TangentSpace I (gamma t)) : Prop :=
  HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov gamma
    (velocityAlong I gamma) t A

/-- A local velocity extension produces the pullback-bundle covariant
acceleration value at the parameter. -/
theorem hasPullbackCovariantAccelerationAt_of_velocityExtensionAt
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {X : GlobalVectorField I M} {t : Real}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hX : IsVelocityExtensionAt (I := I) gamma t X) :
    HasPullbackCovariantAccelerationAt (I := I) cov gamma t
      ((cov X (gamma t)) (curveVelocity I gamma t)) := by
  refine ⟨hgamma, X, ?_, rfl⟩
  refine ⟨mdiffSectionAt_of_tPercent (I := I) (F := E)
    (V := TangentSpace I) hX.1, ?_⟩
  filter_upwards [hX.2] with s hs
  simpa [velocityAlong] using hs.symm

/-- A global ambient representative of an along-field gives a pullback
covariant derivative along the curve. -/
theorem hasPullbackCovariantDerivativeAlongCurveAt_of_global
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {S : VectorFieldAlong I gamma}
    {X : GlobalVectorField I M} {t : Real}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (gamma t))
    (hXS : RealizesAlong (I := I) gamma X S) :
    HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov gamma S t
      ((cov X (gamma t)) (curveVelocity I gamma t)) := by
  exact ⟨hgamma, X, ⟨hX, Filter.Eventually.of_forall fun s => (hXS s).symm⟩, rfl⟩

/-- A global velocity field representative gives pullback-bundle covariant
acceleration. -/
theorem hasPullbackCovariantAccelerationAt_of_global_velocity
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {X : GlobalVectorField I M} {t : Real}
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hX : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) X (gamma t))
    (hvel : RealizesVelocity (I := I) gamma X) :
    HasPullbackCovariantAccelerationAt (I := I) cov gamma t
      ((cov X (gamma t)) (curveVelocity I gamma t)) :=
  hasPullbackCovariantDerivativeAlongCurveAt_of_global
    (I := I) hgamma hX hvel

/-- Uniqueness of the pullback-bundle covariant derivative along a real
curve. -/
theorem HasPullbackCovariantDerivativeAlongCurveAt.unique
    [FiniteDimensional Real E] [CompleteSpace E]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {S : VectorFieldAlong I gamma}
    {t : Real} {A B : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov gamma S t A)
    (hB : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov gamma S t B) :
    A = B :=
  HasPullbackCovariantDerivativeAt.unique_tangent
    (I := I) (I' := 𝓘(Real, Real))
    (cov := cov) (f := gamma) (S := S) (y := t)
    (u := (1 : TangentSpace 𝓘(Real, Real) t)) hA hB

/-- Uniqueness of pullback-bundle covariant acceleration. -/
theorem HasPullbackCovariantAccelerationAt.unique
    [FiniteDimensional Real E] [CompleteSpace E]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {A B : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantAccelerationAt (I := I) cov gamma t A)
    (hB : HasPullbackCovariantAccelerationAt (I := I) cov gamma t B) :
    A = B :=
  HasPullbackCovariantDerivativeAlongCurveAt.unique
    (I := I) (cov := cov) (gamma := gamma)
    (S := velocityAlong I gamma) (t := t) hA hB

end Curves

end Lecture07
end GlobalGeometry
end RicciFlower
