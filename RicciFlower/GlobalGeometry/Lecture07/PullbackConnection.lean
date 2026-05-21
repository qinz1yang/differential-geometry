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

section FramePullback

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A tangent-bundle local trivialization used as a local frame. -/
abbrev TangentTriv :=
  Trivialization E
    (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M)

/-- The Christoffel coefficient of a connection in a chosen tangent local frame,
with the first slot left as an arbitrary tangent vector. -/
def frameGamma
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (x : M) (v : TangentSpace I x)
    (j k : ι) : Real :=
  e.localFrame_coeff I b k x ((cov (e.localFrame b j) x) v)

/-- Transition coefficient from one tangent local frame to another. -/
def frameTrans
    {κ : Type*}
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E) (x : M) (i : ι) (k : κ) : Real :=
  e'.localFrame_coeff I b' k x (e.localFrame b i x)

/-- Directional derivative, on the source, of one local-frame coefficient of a
pullback tangent section. -/
def frameCoeffDeriv
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (f : N -> M)
    (S : PullbackSection f (TangentSpace I)) (y : N)
    (u : TangentSpace I' y) (k : ι) : Real :=
  extDerivFun (I := I')
    (fun z : N => e.localFrame_coeff I b k (f z) (S z)) y u

/-- Local-frame formula for the covariant derivative of a pullback tangent
section.

This is the first genuine pullback-connection candidate: `S` is only a section
along `f`, and the derivative is defined by differentiating the scalar
local-frame coefficients of `S` on the source.  It does not require an ambient
vector-field representative.  The predicate is explicitly tied to the chosen
local frame; frame-independence is the next mathematical bridge. -/
def HasFrameDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (f : N -> M)
    (S : PullbackSection f (TangentSpace I)) (y : N)
    (u : TangentSpace I' y) (A : TangentSpace I (f y)) : Prop :=
  f y ∈ e.baseSet ∧
    MDifferentiableAt I' I f y ∧
      ∀ k : ι,
        MDifferentiableAt I' 𝓘(Real, Real)
            (fun z : N => e.localFrame_coeff I b k (f z) (S z)) y ∧
          e.localFrame_coeff I b k (f y) A =
            frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u k +
              ∑ j : ι,
                e.localFrame_coeff I b j (f y) (S y) *
                  frameGamma (I := I) (M := M) cov e b (f y)
                    ((mfderiv I' I f y) u) j k

/-- Curve specialization of `HasFrameDerivAt`. -/
def HasFrameAlongAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (gamma : Curve M)
    (S : VectorFieldAlong I gamma) (t : Real)
    (A : TangentSpace I (gamma t)) : Prop :=
  HasFrameDerivAt (I := I) (I' := 𝓘(Real, Real)) cov e b gamma S t
    (1 : TangentSpace 𝓘(Real, Real) t) A

/-- Coordinate-local covariant acceleration of a curve, defined without a
global velocity extension. -/
def HasFrameAccelAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (gamma : Curve M) (t : Real)
    (A : TangentSpace I (gamma t)) : Prop :=
  HasFrameAlongAt (I := I) cov e b gamma (velocityAlong I gamma) t A

end FramePullback

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
theorem localFrame_coeff_eq_basis_repr
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

private theorem mdiffAt_sum_real
    {ι : Type*} (t : Finset ι) (φ : ι -> N -> Real)
    {y : N}
    (hφ : ∀ i ∈ t, MDifferentiableAt I' 𝓘(Real, Real) (φ i) y) :
    MDifferentiableAt I' 𝓘(Real, Real) (t.sum φ) y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I') (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := y))
  | insert i t hit ih =>
      have hi : MDifferentiableAt I' 𝓘(Real, Real) (φ i) y := hφ i (by simp [hit])
      have ht : ∀ j ∈ t, MDifferentiableAt I' 𝓘(Real, Real) (φ j) y := by
        intro j hj
        exact hφ j (by simp [hj])
      have hsum : MDifferentiableAt I' 𝓘(Real, Real) (t.sum φ) y := ih ht
      have hadd : MDifferentiableAt I' 𝓘(Real, Real) (φ i + t.sum φ) y := hi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

private theorem extDerivFun_sum_real
    {ι : Type*} (t : Finset ι) (φ : ι -> N -> Real)
    {y : N} (u : TangentSpace I' y)
    (hφ : ∀ i ∈ t, MDifferentiableAt I' 𝓘(Real, Real) (φ i) y) :
    extDerivFun (I := I') (t.sum φ) y u =
      t.sum (fun i => extDerivFun (I := I') (φ i) y u) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hi : MDifferentiableAt I' 𝓘(Real, Real) (φ i) y := hφ i (by simp [hit])
      have ht : ∀ j ∈ t, MDifferentiableAt I' 𝓘(Real, Real) (φ j) y := by
        intro j hj
        exact hφ j (by simp [hj])
      have hsum : MDifferentiableAt I' 𝓘(Real, Real) (t.sum φ) y :=
        mdiffAt_sum_real (I' := I') t φ ht
      calc
        extDerivFun (I := I') ((insert i t).sum φ) y u
            = extDerivFun (I := I') (φ i + t.sum φ) y u := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I') (φ i) y u +
              extDerivFun (I := I') (t.sum φ) y u := by
              have hadd := congr($(extDerivFun_add
                (I := I') (g := φ i) (g' := t.sum φ)
                (x := y) hi hsum) u)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I') (φ j) y u) := by
              rw [ih ht]
              simp [Finset.sum_insert, hit]

private theorem extDerivFun_mul_real
    {φ ψ : N -> Real} {y : N} (u : TangentSpace I' y)
    (hφ : MDifferentiableAt I' 𝓘(Real, Real) φ y)
    (hψ : MDifferentiableAt I' 𝓘(Real, Real) ψ y) :
    extDerivFun (I := I') (fun z : N => φ z * ψ z) y u =
      φ y * extDerivFun (I := I') ψ y u +
        extDerivFun (I := I') φ y u * ψ y := by
  change extDerivFun (I := I') (φ • ψ) y u =
      φ y * extDerivFun (I := I') ψ y u +
        extDerivFun (I := I') φ y u * ψ y
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I') (f := φ) (g := ψ) hφ hψ u
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

/-- Coefficients of one tangent vector in two tangent local frames are related
by the transition coefficients. -/
theorem frameCoeff_change
    {ι κ : Type} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {x : M} (hx : x ∈ e.baseSet) (k : κ)
    (V : TangentSpace I x) :
    e'.localFrame_coeff I b' k x V =
      ∑ i : ι,
        e.localFrame_coeff I b i x V *
          frameTrans (I := I) (M := M) e b e' b' x i k := by
  classical
  let s : (p : M) -> TangentSpace I p :=
    fun p => if h : p = x then h ▸ V else 0
  have hsx : s x = V := by simp [s]
  have hsum := e.eq_sum_localFrame_coeff_smul (I := I) (b := b) (s := s) hx
  calc
    e'.localFrame_coeff I b' k x V =
        e'.localFrame_coeff I b' k x (s x) := by simp [hsx]
    _ = e'.localFrame_coeff I b' k x
          (∑ i : ι, e.localFrame_coeff I b i x (s x) • e.localFrame b i x) := by
        exact congrArg (fun W => e'.localFrame_coeff I b' k x W) hsum
    _ = ∑ i : ι,
          e.localFrame_coeff I b i x (s x) *
            frameTrans (I := I) (M := M) e b e' b' x i k := by
        simp [frameTrans, map_sum, map_smul, smul_eq_mul]
    _ = ∑ i : ι,
          e.localFrame_coeff I b i x V *
            frameTrans (I := I) (M := M) e b e' b' x i k := by
        simp [hsx]

/-- Transition coefficients between tangent local frames are differentiable on
the overlap. -/
theorem frameTrans_mdiffAt
    {ι κ : Type}
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    (i : ι) (k : κ) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => frameTrans (I := I) (M := M) e b e' b' p i k) x := by
  have hframe : MDiffAt (T% (e.localFrame b i)) x := by
    simpa using
      ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
        e.open_baseSet hx i).mdifferentiableAt (by simp)
  simpa [frameTrans] using
    (mdifferentiableAt_localFrame_coeff
      (I := I) (e := e') (b := b') hx' hframe k)

/-- Christoffel transition formula with the first connection slot left as an
arbitrary tangent vector. -/
theorem frameGamma_change
    {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    (w : TangentSpace I x) (i : ι) (k : κ) :
    e'.localFrame_coeff I b' k x ((cov (e.localFrame b i) x) w) =
      extDerivFun (I := I)
        (fun p : M => frameTrans (I := I) (M := M) e b e' b' p i k) x w +
        ∑ l : κ,
          frameTrans (I := I) (M := M) e b e' b' x i l *
            frameGamma (I := I) (M := M) cov e' b' x w l k := by
  have hframe : MDiffAt (T% (e.localFrame b i)) x := by
    simpa using
      ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
        e.open_baseSet hx i).mdifferentiableAt (by simp)
  have hlocal :=
    covariantDerivative_localFrame_coeff_eq_along
      (I := I) cov e' b' hx' hframe w k
  simpa [frameTrans, frameGamma] using hlocal

/-- Sum form of `frameGamma_change`, with the old-frame coefficient of
`∇_w e_i` expanded before changing frame. -/
theorem frameGamma_sum
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    (w : TangentSpace I x) (j : ι) (k : κ) :
    (∑ i : ι,
        frameGamma (I := I) (M := M) cov e b x w j i *
          frameTrans (I := I) (M := M) e b e' b' x i k) =
      extDerivFun (I := I)
        (fun p : M => frameTrans (I := I) (M := M) e b e' b' p j k) x w +
        ∑ l : κ,
          frameTrans (I := I) (M := M) e b e' b' x j l *
            frameGamma (I := I) (M := M) cov e' b' x w l k := by
  calc
    (∑ i : ι,
        frameGamma (I := I) (M := M) cov e b x w j i *
          frameTrans (I := I) (M := M) e b e' b' x i k)
        = e'.localFrame_coeff I b' k x ((cov (e.localFrame b j) x) w) := by
          simpa [frameGamma] using
            (frameCoeff_change (I := I) (M := M) e b e' b' hx k
              ((cov (e.localFrame b j) x) w)).symm
    _ = extDerivFun (I := I)
          (fun p : M => frameTrans (I := I) (M := M) e b e' b' p j k) x w +
        ∑ l : κ,
          frameTrans (I := I) (M := M) e b e' b' x j l *
            frameGamma (I := I) (M := M) cov e' b' x w l k := by
          exact frameGamma_change (I := I) (M := M) cov e b e' b' hx hx' w j k

/-- If the pullback section has differentiable coefficients in one frame, then
its coefficients in any overlapping frame are differentiable. -/
theorem frameCoeff_mdiffAt
    {ι κ : Type} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E}
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A)
    (hx' : f y ∈ e'.baseSet) (k : κ) :
    MDifferentiableAt I' 𝓘(Real, Real)
      (fun z : N => e'.localFrame_coeff I b' k (f z) (S z)) y := by
  classical
  rcases hA with ⟨hx, hf, hcoeff⟩
  have hchange :
      (fun z : N => e'.localFrame_coeff I b' k (f z) (S z)) =ᶠ[𝓝 y]
        fun z : N =>
          ∑ i : ι,
            e.localFrame_coeff I b i (f z) (S z) *
              frameTrans (I := I) (M := M) e b e' b' (f z) i k := by
    have hfe : ∀ᶠ z in 𝓝 y, f z ∈ e.baseSet :=
      hf.continuousAt.eventually_mem (e.open_baseSet.mem_nhds hx)
    filter_upwards [hfe] with z hz
    exact frameCoeff_change (I := I) (M := M) e b e' b' hz k (S z)
  have hsum :
      MDifferentiableAt I' 𝓘(Real, Real)
        (fun z : N =>
          ∑ i : ι,
            e.localFrame_coeff I b i (f z) (S z) *
              frameTrans (I := I) (M := M) e b e' b' (f z) i k) y := by
    have hraw :=
      MDifferentiableAt.sum
        (𝕜 := Real) (I := I')
        (t := (Finset.univ : Finset ι))
        (f := fun i : ι => fun z : N =>
          e.localFrame_coeff I b i (f z) (S z) *
            frameTrans (I := I) (M := M) e b e' b' (f z) i k)
        (fun i _hi => by
          have hSi :
              MDifferentiableAt I' 𝓘(Real, Real)
                (fun z : N => e.localFrame_coeff I b i (f z) (S z)) y :=
            (hcoeff i).1
          have hTi :
              MDifferentiableAt I' 𝓘(Real, Real)
                (fun z : N => frameTrans (I := I) (M := M) e b e' b' (f z) i k) y :=
            (frameTrans_mdiffAt (I := I) (M := M) e b e' b' hx hx' i k).comp y hf
          exact hSi.mul hTi)
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp)
  exact hsum.congr_of_eventuallyEq hchange

/-- Directional derivative of frame coefficients under a change of tangent
local frame. -/
theorem frameCoeffDeriv_change
    {ι κ : Type} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y}
    (hf : MDifferentiableAt I' I f y)
    (hcoeff : ∀ i : ι,
      MDifferentiableAt I' 𝓘(Real, Real)
        (fun z : N => e.localFrame_coeff I b i (f z) (S z)) y)
    (hx : f y ∈ e.baseSet) (hx' : f y ∈ e'.baseSet) (k : κ) :
    frameCoeffDeriv (I := I) (I' := I') (M := M) e' b' f S y u k =
      ∑ i : ι,
        (frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u i *
            frameTrans (I := I) (M := M) e b e' b' (f y) i k +
          e.localFrame_coeff I b i (f y) (S y) *
            extDerivFun (I := I)
              (fun p : M => frameTrans (I := I) (M := M) e b e' b' p i k)
              (f y) ((mfderiv I' I f y) u)) := by
  classical
  let newCoeff : N -> Real :=
    fun z => e'.localFrame_coeff I b' k (f z) (S z)
  let term : ι -> N -> Real := fun i z =>
    e.localFrame_coeff I b i (f z) (S z) *
      frameTrans (I := I) (M := M) e b e' b' (f z) i k
  have hchange : newCoeff =ᶠ[𝓝 y] (Finset.univ : Finset ι).sum term := by
    have hfe : ∀ᶠ z in 𝓝 y, f z ∈ e.baseSet :=
      hf.continuousAt.eventually_mem (e.open_baseSet.mem_nhds hx)
    filter_upwards [hfe] with z hz
    simp [newCoeff, term, frameCoeff_change (I := I) (M := M) e b e' b' hz k (S z)]
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      MDifferentiableAt I' 𝓘(Real, Real) (term i) y := by
    intro i _hi
    have hTi :
        MDifferentiableAt I' 𝓘(Real, Real)
          (fun z : N => frameTrans (I := I) (M := M) e b e' b' (f z) i k) y :=
      (frameTrans_mdiffAt (I := I) (M := M) e b e' b' hx hx' i k).comp y hf
    exact (hcoeff i).mul hTi
  have hderiv_change :
      frameCoeffDeriv (I := I) (I' := I') (M := M) e' b' f S y u k =
        extDerivFun (I := I') ((Finset.univ : Finset ι).sum term) y u := by
    rw [frameCoeffDeriv, extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
    change (mfderiv I' 𝓘(Real, Real) newCoeff y u : Real) =
      (mfderiv I' 𝓘(Real, Real) ((Finset.univ : Finset ι).sum term) y u : Real)
    have hmf :
        mfderiv I' 𝓘(Real, Real) newCoeff y =
          mfderiv I' 𝓘(Real, Real) ((Finset.univ : Finset ι).sum term) y :=
      Filter.EventuallyEq.mfderiv_eq (I := I') (I' := 𝓘(Real, Real)) hchange
    exact congrArg (fun L => L u) hmf
  rw [hderiv_change]
  rw [extDerivFun_sum_real (I' := I') (t := (Finset.univ : Finset ι))
    (φ := term) (y := y) (u := u) hterm]
  refine Finset.sum_congr rfl fun i _hi => ?_
  let oldCoeff : N -> Real := fun z => e.localFrame_coeff I b i (f z) (S z)
  let transCoeff : M -> Real :=
    fun p => frameTrans (I := I) (M := M) e b e' b' p i k
  let transPull : N -> Real := fun z => transCoeff (f z)
  have hTdiff :
      MDifferentiableAt I 𝓘(Real, Real) transCoeff (f y) :=
    frameTrans_mdiffAt (I := I) (M := M) e b e' b' hx hx' i k
  have hTpull :
      MDifferentiableAt I' 𝓘(Real, Real) transPull y :=
    hTdiff.comp y hf
  have hTderiv :
      extDerivFun (I := I') transPull y u =
        extDerivFun (I := I) transCoeff (f y) ((mfderiv I' I f y) u) := by
    rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
    change (mfderiv I' 𝓘(Real, Real) (fun z : N => transCoeff (f z)) y u : Real) =
      (mfderiv I 𝓘(Real, Real) transCoeff (f y) ((mfderiv I' I f y) u) : Real)
    simpa [Function.comp_def, transPull] using
      (mfderiv_comp_apply
        (I := I') (I' := I) (I'' := 𝓘(Real, Real))
        (g := transCoeff) (f := f) (x := y) hTdiff hf u)
  have hmul := extDerivFun_mul_real
    (I' := I') (φ := oldCoeff) (ψ := transPull) (y := y) (u := u)
    (hcoeff i) hTpull
  calc
    extDerivFun (I := I') (term i) y u =
        oldCoeff y * extDerivFun (I := I') transPull y u +
          extDerivFun (I := I') oldCoeff y u * transPull y := by
          simpa [term, oldCoeff, transPull] using hmul
    _ = frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u i *
            frameTrans (I := I) (M := M) e b e' b' (f y) i k +
          e.localFrame_coeff I b i (f y) (S y) *
            extDerivFun (I := I) transCoeff (f y) ((mfderiv I' I f y) u) := by
          simp [frameCoeffDeriv, oldCoeff, transPull, transCoeff, hTderiv]
          ring

/-- The local-frame pullback derivative formula is independent of the chosen
tangent local frame, in the sense that a value satisfying the formula in one
frame satisfies it in every overlapping frame. -/
theorem HasFrameDerivAt.change
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E}
    (e' : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e']
    (b' : Module.Basis κ Real E)
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A)
    (hx' : f y ∈ e'.baseSet) :
    HasFrameDerivAt (I := I) (I' := I') cov e' b' f S y u A := by
  classical
  rcases hA with ⟨hx, hf, hcoeff⟩
  refine ⟨hx', hf, ?_⟩
  intro k
  refine ⟨frameCoeff_mdiffAt (I := I) (I' := I') (cov := cov)
    (e := e) (b := b) e' b' ⟨hx, hf, hcoeff⟩ hx' k, ?_⟩
  let x : M := f y
  let w : TangentSpace I x := (mfderiv I' I f y) u
  let d : ι -> Real := fun i =>
    frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u i
  let s : ι -> Real := fun i => e.localFrame_coeff I b i x (S y)
  let tr : ι -> κ -> Real := fun i l =>
    frameTrans (I := I) (M := M) e b e' b' x i l
  let dt : ι -> Real := fun i =>
    extDerivFun (I := I)
      (fun p : M => frameTrans (I := I) (M := M) e b e' b' p i k) x w
  let G : ι -> ι -> Real := fun j i =>
    frameGamma (I := I) (M := M) cov e b x w j i
  let G' : κ -> Real := fun l =>
    frameGamma (I := I) (M := M) cov e' b' x w l k
  have hAcoeff : ∀ i : ι,
      e.localFrame_coeff I b i x A = d i + ∑ j : ι, s j * G j i := by
    intro i
    simpa [x, w, d, s, G] using (hcoeff i).2
  have hD :
      frameCoeffDeriv (I := I) (I' := I') (M := M) e' b' f S y u k =
        ∑ i : ι, (d i * tr i k + s i * dt i) := by
    simpa [x, w, d, s, tr, dt] using
      frameCoeffDeriv_change (I := I) (I' := I') e b e' b'
        (f := f) (S := S) (y := y) (u := u) hf
        (fun i => (hcoeff i).1) hx hx' k
  have hS : ∀ l : κ,
      e'.localFrame_coeff I b' l x (S y) = ∑ i : ι, s i * tr i l := by
    intro l
    simpa [x, s, tr] using
      frameCoeff_change (I := I) (M := M) e b e' b' hx l (S y)
  have hGsum : ∀ j : ι,
      (∑ i : ι, G j i * tr i k) = dt j + ∑ l : κ, tr j l * G' l := by
    intro j
    simpa [x, w, G, tr, dt, G'] using
      frameGamma_sum (I := I) (M := M) cov e b e' b' hx hx' w j k
  have hconn :
      (∑ i : ι, (∑ j : ι, s j * G j i) * tr i k) =
        (∑ i : ι, s i * dt i) +
          ∑ l : κ, (∑ j : ι, s j * tr j l) * G' l := by
    calc
      (∑ i : ι, (∑ j : ι, s j * G j i) * tr i k)
          = ∑ j : ι, s j * (∑ i : ι, G j i * tr i k) := by
              calc
                (∑ i : ι, (∑ j : ι, s j * G j i) * tr i k)
                    = ∑ i : ι, ∑ j : ι, (s j * G j i) * tr i k := by
                        refine Finset.sum_congr rfl fun i _ => ?_
                        rw [Finset.sum_mul]
                _ = ∑ j : ι, ∑ i : ι, (s j * G j i) * tr i k := by
                        rw [Finset.sum_comm]
                _ = ∑ j : ι, s j * (∑ i : ι, G j i * tr i k) := by
                        refine Finset.sum_congr rfl fun j _ => ?_
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun i _ => ?_
                        ring
      _ = ∑ j : ι, s j * (dt j + ∑ l : κ, tr j l * G' l) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hGsum j]
      _ = (∑ i : ι, s i * dt i) +
            ∑ l : κ, (∑ j : ι, s j * tr j l) * G' l := by
              calc
                (∑ j : ι, s j * (dt j + ∑ l : κ, tr j l * G' l))
                    = (∑ j : ι, s j * dt j) +
                        ∑ j : ι, s j * (∑ l : κ, tr j l * G' l) := by
                        simp [mul_add, Finset.sum_add_distrib]
                _ = (∑ i : ι, s i * dt i) +
                      ∑ j : ι, ∑ l : κ, s j * (tr j l * G' l) := by
                        congr 1
                        refine Finset.sum_congr rfl fun j _ => ?_
                        rw [Finset.mul_sum]
                _ = (∑ i : ι, s i * dt i) +
                      ∑ l : κ, ∑ j : ι, s j * (tr j l * G' l) := by
                        congr 1
                        rw [Finset.sum_comm]
                _ = (∑ i : ι, s i * dt i) +
                      ∑ l : κ, (∑ j : ι, s j * tr j l) * G' l := by
                        congr 1
                        refine Finset.sum_congr rfl fun l _ => ?_
                        rw [Finset.sum_mul]
                        refine Finset.sum_congr rfl fun j _ => ?_
                        ring
  calc
    e'.localFrame_coeff I b' k (f y) A =
        ∑ i : ι, e.localFrame_coeff I b i x A * tr i k := by
          simpa [x, tr] using
            frameCoeff_change (I := I) (M := M) e b e' b' hx k A
    _ = ∑ i : ι, (d i + ∑ j : ι, s j * G j i) * tr i k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hAcoeff i]
    _ = (∑ i : ι, (d i * tr i k + s i * dt i)) +
          ∑ l : κ, (∑ j : ι, s j * tr j l) * G' l := by
          calc
            (∑ i : ι, (d i + ∑ j : ι, s j * G j i) * tr i k)
                = (∑ i : ι, d i * tr i k) +
                    ∑ i : ι, (∑ j : ι, s j * G j i) * tr i k := by
                    simp [add_mul, Finset.sum_add_distrib]
            _ = (∑ i : ι, d i * tr i k) +
                    ((∑ i : ι, s i * dt i) +
                      ∑ l : κ, (∑ j : ι, s j * tr j l) * G' l) := by
                    rw [hconn]
            _ = (∑ i : ι, (d i * tr i k + s i * dt i)) +
                    ∑ l : κ, (∑ j : ι, s j * tr j l) * G' l := by
                    rw [Finset.sum_add_distrib]
                    abel
    _ = frameCoeffDeriv (I := I) (I' := I') (M := M) e' b' f S y u k +
          ∑ l : κ,
            e'.localFrame_coeff I b' l (f y) (S y) *
              frameGamma (I := I) (M := M) cov e' b' (f y)
                ((mfderiv I' I f y) u) l k := by
          rw [hD]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [x, w, G', hS l]

/-- If a pullback tangent section is represented by a smooth ambient vector
field, the local-frame pullback derivative formula gives the representative
covariant derivative. -/
theorem frameDeriv_of_rep
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {σ : (x : M) -> TangentSpace I x} {y : N} {u : TangentSpace I' y}
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hx : f y ∈ e.baseSet)
    (hf : MDifferentiableAt I' I f y)
    (hσ : MDiffSectionAt (I := I) (F := E) (V := TangentSpace I) σ (f y))
    (hSσ : PullbackSectionRealizedByAt f S σ y) :
    HasFrameDerivAt (I := I) (I' := I') cov e b f S y u
      ((cov σ (f y)) ((mfderiv I' I f y) u)) := by
  classical
  refine ⟨hx, hf, ?_⟩
  intro k
  let w : TangentSpace I (f y) := (mfderiv I' I f y) u
  let φ : M -> Real := fun x => e.localFrame_coeff I b k x (σ x)
  let ψ : N -> Real := fun z => e.localFrame_coeff I b k (f z) (S z)
  have hσdiff : MDiffAt (T% σ) (f y) :=
    mdiffSectionAt_tPercent (I := I) (F := E) (V := TangentSpace I) hσ
  have hφdiff : MDifferentiableAt I 𝓘(Real, Real) φ (f y) := by
    simpa [φ] using
      (mdifferentiableAt_localFrame_coeff
        (I := I) (e := e) (b := b) hx hσdiff k)
  have hψφ : ψ =ᶠ[𝓝 y] fun z : N => φ (f z) := by
    filter_upwards [hSσ] with z hz
    simp [ψ, φ, hz]
  have hψdiff : MDifferentiableAt I' 𝓘(Real, Real) ψ y := by
    exact (hφdiff.comp y hf).congr_of_eventuallyEq hψφ
  have hmf :
      mfderiv I' 𝓘(Real, Real) ψ y =
        mfderiv I' 𝓘(Real, Real) (fun z : N => φ (f z)) y :=
    Filter.EventuallyEq.mfderiv_eq (I := I') (I' := 𝓘(Real, Real)) hψφ
  have hmf_apply :
      mfderiv I' 𝓘(Real, Real) ψ y u =
        mfderiv I' 𝓘(Real, Real) (fun z : N => φ (f z)) y u :=
    congrArg (fun L => L u) hmf
  have hcomp :
      mfderiv I' 𝓘(Real, Real) (fun z : N => φ (f z)) y u =
        mfderiv I 𝓘(Real, Real) φ (f y) w := by
    simpa [Function.comp_def, w] using
      (mfderiv_comp_apply
        (I := I') (I' := I) (I'' := 𝓘(Real, Real))
        (g := φ) (f := f) (x := y) hφdiff hf u)
  have hderiv :
      frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u k =
        extDerivFun (I := I) φ (f y) w := by
    rw [frameCoeffDeriv, extDerivFun_real_eq_mfderiv,
      extDerivFun_real_eq_mfderiv]
    change
      (mfderiv I' 𝓘(Real, Real) ψ y u : Real) =
        (mfderiv I 𝓘(Real, Real) φ (f y) w : Real)
    rw [hmf_apply, hcomp]
  have hSy : S y = σ (f y) := hSσ.self_of_nhds
  have hlocal :=
    covariantDerivative_localFrame_coeff_eq_along
      (I := I) cov e b hx hσdiff w k
  refine ⟨by simpa [ψ] using hψdiff, ?_⟩
  calc
    e.localFrame_coeff I b k (f y)
        ((cov σ (f y)) ((mfderiv I' I f y) u))
        = extDerivFun (I := I) φ (f y) w +
            ∑ j : ι,
              e.localFrame_coeff I b j (f y) (σ (f y)) *
                e.localFrame_coeff I b k (f y)
                  ((cov (e.localFrame b j) (f y)) w) := by
          simpa [φ, w] using hlocal
    _ = frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u k +
            ∑ j : ι,
              e.localFrame_coeff I b j (f y) (S y) *
                frameGamma (I := I) (M := M) cov e b (f y)
                  ((mfderiv I' I f y) u) j k := by
          simp [hderiv, hSy, frameGamma, w]

/-- In a fixed tangent local frame, the local-frame pullback derivative value
is unique. -/
theorem HasFrameDerivAt.unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {f : N -> M}
    {S : PullbackSection f (TangentSpace I)} {y : N}
    {u : TangentSpace I' y} {A B : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A)
    (hB : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u B) :
    A = B := by
  rcases hA with ⟨hx, _hf, hAcoeff⟩
  rcases hB with ⟨_hxB, _hfB, hBcoeff⟩
  apply (e.basisAt b hx).ext_elem
  intro k
  rw [← localFrame_coeff_eq_basis_repr (I := I) e b hx k A]
  rw [← localFrame_coeff_eq_basis_repr (I := I) e b hx k B]
  rw [(hAcoeff k).2, (hBcoeff k).2]

/-- Canonical frame-defined pullback covariant derivative.

This is the public, representative-free derivative relation.  It uses the
bundle trivialization chosen by `trivializationAt` and the finite basis of the
model fiber only as a concrete way to write the local-frame formula.  The
choice is harmless because `HasFrameDerivAt.change` transports the formula to
every overlapping tangent local frame. -/
def HasPBCovDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (f : N -> M) (S : PullbackSection f (TangentSpace I)) (y : N)
    (u : TangentSpace I' y) (A : TangentSpace I (f y)) : Prop :=
  let e := trivializationAt E (TangentSpace I : M -> Type _) (f y)
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A

/-- A derivative satisfying the local-frame formula in any frame satisfies the
canonical frame-defined pullback derivative relation. -/
theorem HasPBCovDerivAt.ofFrame
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {f : N -> M}
    {S : PullbackSection f (TangentSpace I)} {y : N}
    {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A) :
    HasPBCovDerivAt (I := I) (I' := I') cov f S y u A := by
  let e₀ := trivializationAt E (TangentSpace I : M -> Type _) (f y)
  let b₀ : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  have hx₀ : f y ∈ e₀.baseSet := by simp [e₀]
  simpa [HasPBCovDerivAt, e₀, b₀] using
    (HasFrameDerivAt.change (I := I) (I' := I') (cov := cov)
      (e := e) (b := b) e₀ b₀ hA hx₀)

/-- The canonical frame-defined pullback derivative satisfies the local-frame
formula in every overlapping tangent local frame. -/
theorem HasPBCovDerivAt.toFrame
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasPBCovDerivAt (I := I) (I' := I') cov f S y u A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : f y ∈ e.baseSet) :
    HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A := by
  let e₀ := trivializationAt E (TangentSpace I : M -> Type _) (f y)
  let b₀ : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  have h₀ :
      HasFrameDerivAt (I := I) (I' := I') cov e₀ b₀ f S y u A := by
    simpa [HasPBCovDerivAt, e₀, b₀] using hA
  exact HasFrameDerivAt.change (I := I) (I' := I') (cov := cov)
    (e := e₀) (b := b₀) e b h₀ hx

/-- Uniqueness of the canonical frame-defined pullback derivative relation. -/
theorem HasPBCovDerivAt.unique
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y}
    {A B : TangentSpace I (f y)}
    (hA : HasPBCovDerivAt (I := I) (I' := I') cov f S y u A)
    (hB : HasPBCovDerivAt (I := I) (I' := I') cov f S y u B) :
    A = B := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) (f y)
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  have hAf :
      HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A := by
    simpa [HasPBCovDerivAt, e, b] using hA
  have hBf :
      HasFrameDerivAt (I := I) (I' := I') cov e b f S y u B := by
    simpa [HasPBCovDerivAt, e, b] using hB
  exact HasFrameDerivAt.unique (I := I) (I' := I') hAf hBf

/-- The canonical pullback covariant derivative of the zero pullback section is
zero. -/
theorem HasPBCovDerivAt.zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {y : N} {u : TangentSpace I' y}
    (hf : MDifferentiableAt I' I f y) :
    HasPBCovDerivAt (I := I) (I' := I') cov f
      (fun z : N => (0 : TangentSpace I (f z))) y u
      (0 : TangentSpace I (f y)) := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) (f y)
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  have hx : f y ∈ e.baseSet := by simp [e]
  apply HasPBCovDerivAt.ofFrame (I := I) (I' := I')
    (e := e) (b := b)
  refine ⟨hx, hf, ?_⟩
  intro k
  have hdiff :
      MDifferentiableAt I' 𝓘(Real, Real)
        (fun z : N => e.localFrame_coeff I b k (f z)
          (0 : TangentSpace I (f z))) y := by
    simpa using (mdifferentiableAt_const
      (I := I') (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := y))
  refine ⟨hdiff, ?_⟩
  simp [frameCoeffDeriv, frameGamma]

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

/-- Representative-based pullback derivatives satisfy the local-frame formula
in every chosen tangent local frame. -/
theorem HasPullbackCovariantDerivativeAt.toFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasPullbackCovariantDerivativeAt
      (I := I) (I' := I') (F := E) (V := TangentSpace I) cov f S y u A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : f y ∈ e.baseSet) :
    HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A := by
  rcases hA with ⟨hf, σ, hσ, hAeq⟩
  rw [hAeq]
  simpa [pullbackCovDerivOfRepresentativeAt] using
    frameDeriv_of_rep (I := I) (I' := I') (cov := cov)
      (f := f) (S := S) (σ := σ) (y := y) (u := u)
      e b hx hf hσ.1 hσ.2

/-- Representative-based pullback derivatives produce the canonical
frame-defined pullback derivative relation. -/
theorem HasPullbackCovariantDerivativeAt.toPBCov
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasPullbackCovariantDerivativeAt
      (I := I) (I' := I') (F := E) (V := TangentSpace I) cov f S y u A) :
    HasPBCovDerivAt (I := I) (I' := I') cov f S y u A := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) (f y)
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    Module.finBasis Real E
  have hx : f y ∈ e.baseSet := by simp [e]
  exact HasPBCovDerivAt.ofFrame (I := I) (I' := I')
    (hA.toFrame e b hx)

end TangentWellDefinedness

/-! ## Curves as pullback bundles -/

variable [FiniteDimensional Real E] [CompleteSpace E]

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

/-- Curve specialization of the canonical frame-defined pullback derivative. -/
def HasPBCovAlongAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (S : VectorFieldAlong I gamma) (t : Real)
    (A : TangentSpace I (gamma t)) : Prop :=
  HasPBCovDerivAt (I := I) (I' := 𝓘(Real, Real)) cov gamma S t
    (1 : TangentSpace 𝓘(Real, Real) t) A

/-- Canonical frame-defined covariant acceleration of a curve. -/
def HasPBCovAccelAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (t : Real) (A : TangentSpace I (gamma t)) : Prop :=
  HasPBCovAlongAt (I := I) cov gamma (velocityAlong I gamma) t A

/-- Along a differentiable curve, the frame-defined derivative of the zero
field is zero. -/
theorem HasPBCovAlongAt.zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real}
    (hγ : MDifferentiableAt 𝓘(Real, Real) I gamma t) :
    HasPBCovAlongAt (I := I) cov gamma
      (fun τ : Real => (0 : TangentSpace I (gamma τ))) t
      (0 : TangentSpace I (gamma t)) := by
  simpa [HasPBCovAlongAt] using
    (HasPBCovDerivAt.zero (I := I) (I' := 𝓘(Real, Real))
      (cov := cov) (f := gamma) (y := t)
      (u := (1 : TangentSpace 𝓘(Real, Real) t)) hγ)

/-! ## Two-parameter surface wrappers -/

/-- Pointwise coefficient form of a covariant derivative:
`dv + Γ v`.  This is pure finite-dimensional algebra, independent of
manifold or bundle data. -/
def coeffCov {ι : Type*} [Fintype ι]
    (Γ : Matrix ι ι Real) (dv v : ι -> Real) : ι -> Real :=
  dv + Γ.mulVec v

/-- Local-frame coefficient vector of one tangent vector. -/
def frameVec {ι : Type*}
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (v : TangentSpace I x) :
    ι -> Real :=
  fun k => e.localFrame_coeff I b k x v

/-- Reassemble a tangent vector from coefficients in a fixed local frame. -/
def frameSum {ι : Type*} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (c : ι -> Real) :
    TangentSpace I x :=
  ∑ k : ι, c k • e.localFrame b k x

/-- In the frame domain, `frameSum` inverts `frameVec` on coefficients. -/
theorem frameVec_frameSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (hx : x ∈ e.baseSet)
    (c : ι -> Real) :
    frameVec (I := I) e b (frameSum (I := I) e b c : TangentSpace I x) = c := by
  classical
  ext k
  rw [frameVec, frameSum]
  rw [localFrame_coeff_eq_basis_repr (I := I) e b hx k]
  simp [e.localFrame_apply_of_mem_baseSet b hx]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    exact Finsupp.single_eq_of_ne (Ne.symm hj)
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- In the frame domain, `frameVec` determines a tangent vector. -/
theorem frameVec_eq_iff
    {ι : Type*}
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (hx : x ∈ e.baseSet)
    {u v : TangentSpace I x} :
    frameVec (I := I) e b u = frameVec (I := I) e b v ↔ u = v := by
  constructor
  · intro h
    apply (e.basisAt b hx).ext_elem
    intro k
    rw [← localFrame_coeff_eq_basis_repr (I := I) e b hx k u]
    rw [← localFrame_coeff_eq_basis_repr (I := I) e b hx k v]
    exact congrFun h k
  · intro h
    rw [h]

/-- Local-frame derivative coefficient vector of a pullback tangent section. -/
def frameDerivVec {ι : Type*} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (f : N -> M)
    (S : PullbackSection f (TangentSpace I)) (y : N)
    (u : TangentSpace I' y) : ι -> Real :=
  fun k => frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u k

/-- Connection matrix in a fixed local frame.  The row index is the output
coefficient and the column index is the coefficient of the differentiated
field, so `frameGammaMat.mulVec` matches the `HasFrameDerivAt` formula. -/
def frameGammaMat {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (f : N -> M) (y : N)
    (u : TangentSpace I' y) : Matrix ι ι Real :=
  fun k j => frameGamma (I := I) (M := M) cov e b (f y)
    ((mfderiv I' I f y) u) j k

/-- The local-frame curvature matrix expression
`∂s Γt - ∂t Γs + ΓsΓt - ΓtΓs`. -/
def frameCurvMat {ι : Type*} [Fintype ι]
    (Γs Γt dΓt_s dΓs_t : Matrix ι ι Real) : Matrix ι ι Real :=
  dΓt_s - dΓs_t + Γs * Γt - Γt * Γs

/-- The vector represented by the local-frame curvature matrix expression
applied to a tangent vector's frame coefficients. -/
def frameCurvVec {ι : Type*} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (Γs Γt dΓt_s dΓs_t : Matrix ι ι Real)
    {x : M} (V : TangentSpace I x) : TangentSpace I x :=
  frameSum (I := I) e b
    ((frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec
      (frameVec (I := I) e b V))

/-- Coefficients of `frameCurvVec` are the curvature matrix expression. -/
theorem frameVec_frameCurvVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (hx : x ∈ e.baseSet)
    (Γs Γt dΓt_s dΓs_t : Matrix ι ι Real) (V : TangentSpace I x) :
    frameVec (I := I) e b
        (frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t V) =
      (frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec
        (frameVec (I := I) e b V) := by
  rw [frameCurvVec, frameVec_frameSum (I := I) e b hx]

/-- Vector form of the fixed-frame pullback derivative formula. -/
theorem HasFrameDerivAt.frame_vec_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {f : N -> M}
    {S : PullbackSection f (TangentSpace I)} {y : N}
    {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A) :
    frameVec (I := I) e b A =
      coeffCov (frameGammaMat (I := I) (I' := I') (M := M) cov e b f y u)
        (frameDerivVec (I := I) (I' := I') (M := M) e b f S y u)
        (frameVec (I := I) e b (S y)) := by
  classical
  ext k
  calc
    frameVec (I := I) e b A k =
        frameCoeffDeriv (I := I) (I' := I') (M := M) e b f S y u k +
          ∑ j : ι,
            e.localFrame_coeff I b j (f y) (S y) *
              frameGamma (I := I) (M := M) cov e b (f y)
                ((mfderiv I' I f y) u) j k := by
          exact (hA.2.2 k).2
    _ =
        coeffCov (frameGammaMat (I := I) (I' := I') (M := M) cov e b f y u)
          (frameDerivVec (I := I) (I' := I') (M := M) e b f S y u)
          (frameVec (I := I) e b (S y)) k := by
          simp [coeffCov, frameVec, frameDerivVec, frameGammaMat,
            Matrix.mulVec, dotProduct, mul_comm]

/-- On a real parameter line, `frameDerivVec` is the ordinary derivative of
the local-frame coefficient vector. -/
theorem frameDerivVec_eq_of_hasDerivAt
    {ι : Type*} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {gamma : Curve M}
    {S : VectorFieldAlong I gamma} {t : Real} {dS : ι -> Real}
    (hS : HasDerivAt (fun r : Real => frameVec (I := I) e b (S r)) dS t) :
    frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
      gamma S t (1 : TangentSpace 𝓘(Real, Real) t) = dS := by
  ext k
  have hk : HasDerivAt
      (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) (dS k) t := by
    simpa [frameVec] using (hasDerivAt_pi.mp hS k)
  have hmf := hk.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [frameDerivVec, frameCoeffDeriv, extDerivFun_real_eq_mfderiv]
  change
    (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
      (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t)
      (1 : TangentSpace 𝓘(Real, Real) t) = dS k
  rw [hmf]
  change (ContinuousLinearMap.toSpanSingleton Real (dS k)) (1 : Real) = dS k
  exact ContinuousLinearMap.toSpanSingleton_apply_one (R₁ := Real) (x := dS k)

/-- Build a fixed-frame along-curve derivative from a derivative of the whole
coefficient vector. -/
theorem HasFrameAlongAt.of_frameVec_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {gamma : Curve M}
    {S : VectorFieldAlong I gamma} {t : Real} {dS : ι -> Real}
    (hx : gamma t ∈ e.baseSet)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (hS : HasDerivAt (fun r : Real => frameVec (I := I) e b (S r)) dS t) :
    HasFrameAlongAt (I := I) cov e b gamma S t
      (frameSum (I := I) e b
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b gamma t
            (1 : TangentSpace 𝓘(Real, Real) t))
          dS (frameVec (I := I) e b (S t)))) := by
  classical
  refine ⟨hx, hgamma, ?_⟩
  have hderivVec := frameDerivVec_eq_of_hasDerivAt (I := I) e b
    (gamma := gamma) (S := S) hS
  have hsum := frameVec_frameSum (I := I) e b hx
    (coeffCov
      (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b gamma t
        (1 : TangentSpace 𝓘(Real, Real) t))
      dS (frameVec (I := I) e b (S t)))
  intro k
  constructor
  · have hk : HasDerivAt
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) (dS k) t := by
      simpa [frameVec] using (hasDerivAt_pi.mp hS k)
    exact hk.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  · have hk := congrFun hsum k
    change frameVec (I := I) e b
        (frameSum (I := I) e b
          (coeffCov
            (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b gamma t
              (1 : TangentSpace 𝓘(Real, Real) t))
            dS (frameVec (I := I) e b (S t)))) k =
      frameCoeffDeriv (I := I) (I' := 𝓘(Real, Real)) (M := M) e b gamma S t
          (1 : TangentSpace 𝓘(Real, Real) t) k +
        ∑ j : ι,
          e.localFrame_coeff I b j (gamma t) (S t) *
            frameGamma (I := I) (M := M) cov e b (gamma t)
              ((mfderiv 𝓘(Real, Real) I gamma t)
                (1 : TangentSpace 𝓘(Real, Real) t)) j k
    have hderiv_k :
        frameCoeffDeriv (I := I) (I' := 𝓘(Real, Real)) (M := M) e b gamma S t
            (1 : TangentSpace 𝓘(Real, Real) t) k = dS k := by
      simpa [frameDerivVec] using congrFun hderivVec k
    rw [hk, hderiv_k]
    simp [coeffCov, frameGammaMat, frameVec, Matrix.mulVec, dotProduct, mul_comm]

/-- Pure coefficient/matrix commutator identity for two covariant
first-order operators `∂s + Γs` and `∂t + Γt`.

All derivative values are explicit arguments; this lemma contains no manifold
or connection API. -/
theorem coeffCov_comm_at
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v vs vt vst vts : ι -> Real)
    (Γs Γt dΓt_s dΓs_t : Matrix ι ι Real)
    (hmix : vst = vts) :
    (coeffCov Γs
        (vst + dΓt_s.mulVec v + Γt.mulVec vs)
        (coeffCov Γt vt v) -
      coeffCov Γt
        (vts + dΓs_t.mulVec v + Γs.mulVec vt)
        (coeffCov Γs vs v)) =
      (dΓt_s - dΓs_t + Γs * Γt - Γt * Γs).mulVec v := by
  classical
  ext k
  simp only [coeffCov, Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, hmix]
  abel

/-- Restrict a two-dimensional germ to the line `σ ↦ (σ,t)`. -/
theorem eventually_prod_left
    {P : Real × Real -> Prop} {s t : Real}
    (h : ∀ᶠ q : Real × Real in 𝓝 (s, t), P q) :
    ∀ᶠ s' : Real in 𝓝 s, P (s', t) := by
  exact (ContinuousAt.prodMk continuousAt_id continuousAt_const).tendsto.eventually h

/-- Restrict a two-dimensional germ to the line `τ ↦ (s,τ)`. -/
theorem eventually_prod_right
    {P : Real × Real -> Prop} {s t : Real}
    (h : ∀ᶠ q : Real × Real in 𝓝 (s, t), P q) :
    ∀ᶠ t' : Real in 𝓝 t, P (s, t') := by
  exact (ContinuousAt.prodMk continuousAt_const continuousAt_id).tendsto.eventually h

/-- Derivative of a finite matrix-vector product.  This is the calculus helper
used later to differentiate connection-matrix terms in a fixed frame. -/
theorem hasDerivAt_mulVec
    {ι : Type*} [Fintype ι]
    {Γ : Real -> Matrix ι ι Real} {v : Real -> ι -> Real}
    {x : Real} {dΓ : Matrix ι ι Real} {dv : ι -> Real}
    (hΓ : HasDerivAt Γ dΓ x) (hv : HasDerivAt v dv x) :
    HasDerivAt (fun r => (Γ r).mulVec (v r))
      (dΓ.mulVec (v x) + (Γ x).mulVec dv) x := by
  classical
  rw [hasDerivAt_pi]
  intro i
  have hsum :
      HasDerivAt
        (fun r => Finset.univ.sum
          (fun j : ι => Γ r i j * (v r) j))
        (Finset.univ.sum
          (fun j : ι => dΓ i j * (v x) j + Γ x i j * dv j)) x := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hΓ i) j).mul
      (hasDerivAt_pi.mp hv j))
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using hsum

/-- Derivative of the pointwise coefficient covariant derivative
`dv + Γ v`. -/
theorem hasDerivAt_coeffCov
    {ι : Type*} [Fintype ι]
    {Γ : Real -> Matrix ι ι Real} {v dvFun : Real -> ι -> Real}
    {x : Real} {dΓ : Matrix ι ι Real} {dv ddv : ι -> Real}
    (hΓ : HasDerivAt Γ dΓ x) (hv : HasDerivAt v dv x)
    (hdv : HasDerivAt dvFun ddv x) :
    HasDerivAt (fun r => coeffCov (Γ r) (dvFun r) (v r))
      (ddv + dΓ.mulVec (v x) + (Γ x).mulVec dv) x := by
  have hmv := hasDerivAt_mulVec (Γ := Γ) (v := v) hΓ hv
  simpa [coeffCov, add_assoc] using hdv.add hmv

/-- A two-parameter surface, with first parameter used for variations and second
parameter used as curve time. -/
abbrev Surface (M : Type*) := Real × Real -> M

/-- The time curve `τ ↦ F (s,τ)` through a fixed variation parameter. -/
def surfaceTimeCurve (F : Surface M) (s : Real) : Curve M :=
  fun τ => F (s, τ)

/-- The parameter curve `σ ↦ F (σ,t)` through a fixed time. -/
def surfaceParamCurve (F : Surface M) (t : Real) : Curve M :=
  fun σ => F (σ, t)

/-- A vector field along a two-parameter surface. -/
abbrev SurfaceFieldAlong (I : ModelWithCorners Real E H) (F : Surface M) :=
  (p : Real × Real) -> TangentSpace I (F p)

/-- Covariant derivative in the surface-parameter direction. -/
def HasPBParamCovDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (V : SurfaceFieldAlong I F) (s t : Real)
    (A : TangentSpace I (F (s, t))) : Prop :=
  HasPBCovAlongAt (I := I) cov (surfaceParamCurve F t)
    (fun σ => V (σ, t)) s A

/-- Covariant derivative in the time direction. -/
def HasPBTimeCovDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (V : SurfaceFieldAlong I F) (s t : Real)
    (A : TangentSpace I (F (s, t))) : Prop :=
  HasPBCovAlongAt (I := I) cov (surfaceTimeCurve F s)
    (fun τ => V (s, τ)) t A

/-- The parameter-direction derivative of the zero surface field is zero. -/
theorem HasPBParamCovDerivAt.zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s t : Real}
    (hF : MDifferentiableAt 𝓘(Real, Real) I (surfaceParamCurve F t) s) :
    HasPBParamCovDerivAt (I := I) cov F
      (fun p : Real × Real => (0 : TangentSpace I (F p))) s t
      (0 : TangentSpace I (F (s, t))) := by
  simpa [HasPBParamCovDerivAt, surfaceParamCurve] using
    (HasPBCovAlongAt.zero (I := I) (cov := cov)
      (gamma := surfaceParamCurve F t) (t := s) hF)

/-- The time-direction derivative of the zero surface field is zero. -/
theorem HasPBTimeCovDerivAt.zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s t : Real}
    (hF : MDifferentiableAt 𝓘(Real, Real) I (surfaceTimeCurve F s) t) :
    HasPBTimeCovDerivAt (I := I) cov F
      (fun p : Real × Real => (0 : TangentSpace I (F p))) s t
      (0 : TangentSpace I (F (s, t))) := by
  simpa [HasPBTimeCovDerivAt, surfaceTimeCurve] using
    (HasPBCovAlongAt.zero (I := I) (cov := cov)
      (gamma := surfaceTimeCurve F s) (t := t) hF)

/-- Uniqueness of the parameter-direction surface derivative. -/
theorem HasPBParamCovDerivAt.unique
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceFieldAlong I F} {s t : Real}
    {A B : TangentSpace I (F (s, t))}
    (hA : HasPBParamCovDerivAt (I := I) cov F V s t A)
    (hB : HasPBParamCovDerivAt (I := I) cov F V s t B) :
    A = B := by
  exact HasPBCovDerivAt.unique (I := I) (I' := 𝓘(Real, Real))
    (cov := cov) (f := surfaceParamCurve F t)
    (S := fun σ => V (σ, t)) (y := s)
    (u := (1 : TangentSpace 𝓘(Real, Real) s)) hA hB

/-- Uniqueness of the time-direction surface derivative. -/
theorem HasPBTimeCovDerivAt.unique
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceFieldAlong I F} {s t : Real}
    {A B : TangentSpace I (F (s, t))}
    (hA : HasPBTimeCovDerivAt (I := I) cov F V s t A)
    (hB : HasPBTimeCovDerivAt (I := I) cov F V s t B) :
    A = B := by
  exact HasPBCovDerivAt.unique (I := I) (I' := 𝓘(Real, Real))
    (cov := cov) (f := surfaceTimeCurve F s)
    (S := fun τ => V (s, τ)) (y := t)
    (u := (1 : TangentSpace 𝓘(Real, Real) t)) hA hB

/-- Parameter-direction surface derivatives satisfy the fixed-frame
coefficient formula in any overlapping tangent local frame. -/
theorem HasPBParamCovDerivAt.frame_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceFieldAlong I F} {s t : Real}
    {A : TangentSpace I (F (s, t))}
    (hA : HasPBParamCovDerivAt (I := I) cov F V s t A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : F (s, t) ∈ e.baseSet) (k : ι) :
    e.localFrame_coeff I b k (F (s, t)) A =
      frameCoeffDeriv (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
        (surfaceParamCurve F t) (fun σ => V (σ, t)) s
        (1 : TangentSpace 𝓘(Real, Real) s) k +
        ∑ j : ι,
          e.localFrame_coeff I b j (F (s, t)) (V (s, t)) *
            frameGamma (I := I) (M := M) cov e b (F (s, t))
              ((mfderiv 𝓘(Real, Real) I (surfaceParamCurve F t) s)
                (1 : TangentSpace 𝓘(Real, Real) s)) j k := by
  have hf :
      HasFrameAlongAt (I := I) cov e b (surfaceParamCurve F t)
        (fun σ => V (σ, t)) s A := by
    simpa [HasPBParamCovDerivAt, HasPBCovAlongAt] using
      (HasPBCovDerivAt.toFrame
        (I := I) (I' := 𝓘(Real, Real)) (cov := cov)
        (f := surfaceParamCurve F t) (S := fun σ => V (σ, t))
        (y := s) (u := (1 : TangentSpace 𝓘(Real, Real) s))
        hA e b hx)
  exact (hf.2.2 k).2

/-- Vector form of `HasPBParamCovDerivAt.frame_eq`. -/
theorem HasPBParamCovDerivAt.frame_vec_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceFieldAlong I F} {s t : Real}
    {A : TangentSpace I (F (s, t))}
    (hA : HasPBParamCovDerivAt (I := I) cov F V s t A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : F (s, t) ∈ e.baseSet) :
    frameVec (I := I) e b A =
      coeffCov
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F t) (fun σ => V (σ, t)) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (frameVec (I := I) e b (V (s, t))) := by
  have hf :
      HasFrameAlongAt (I := I) cov e b (surfaceParamCurve F t)
        (fun σ => V (σ, t)) s A := by
    simpa [HasPBParamCovDerivAt, HasPBCovAlongAt] using
      (HasPBCovDerivAt.toFrame
        (I := I) (I' := 𝓘(Real, Real)) (cov := cov)
        (f := surfaceParamCurve F t) (S := fun σ => V (σ, t))
        (y := s) (u := (1 : TangentSpace 𝓘(Real, Real) s))
        hA e b hx)
  exact HasFrameDerivAt.frame_vec_eq (I := I) (I' := 𝓘(Real, Real))
    (cov := cov) hf

/-- Time-direction surface derivatives satisfy the fixed-frame coefficient
formula in any overlapping tangent local frame. -/
theorem HasPBTimeCovDerivAt.frame_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceFieldAlong I F} {s t : Real}
    {A : TangentSpace I (F (s, t))}
    (hA : HasPBTimeCovDerivAt (I := I) cov F V s t A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : F (s, t) ∈ e.baseSet) (k : ι) :
    e.localFrame_coeff I b k (F (s, t)) A =
      frameCoeffDeriv (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
        (surfaceTimeCurve F s) (fun τ => V (s, τ)) t
        (1 : TangentSpace 𝓘(Real, Real) t) k +
        ∑ j : ι,
          e.localFrame_coeff I b j (F (s, t)) (V (s, t)) *
            frameGamma (I := I) (M := M) cov e b (F (s, t))
              ((mfderiv 𝓘(Real, Real) I (surfaceTimeCurve F s) t)
                (1 : TangentSpace 𝓘(Real, Real) t)) j k := by
  have hf :
      HasFrameAlongAt (I := I) cov e b (surfaceTimeCurve F s)
        (fun τ => V (s, τ)) t A := by
    simpa [HasPBTimeCovDerivAt, HasPBCovAlongAt] using
      (HasPBCovDerivAt.toFrame
        (I := I) (I' := 𝓘(Real, Real)) (cov := cov)
        (f := surfaceTimeCurve F s) (S := fun τ => V (s, τ))
        (y := t) (u := (1 : TangentSpace 𝓘(Real, Real) t))
        hA e b hx)
  exact (hf.2.2 k).2

/-- Vector form of `HasPBTimeCovDerivAt.frame_eq`. -/
theorem HasPBTimeCovDerivAt.frame_vec_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V : SurfaceFieldAlong I F} {s t : Real}
    {A : TangentSpace I (F (s, t))}
    (hA : HasPBTimeCovDerivAt (I := I) cov F V s t A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : F (s, t) ∈ e.baseSet) :
    frameVec (I := I) e b A =
      coeffCov
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F s) (fun τ => V (s, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        (frameVec (I := I) e b (V (s, t))) := by
  have hf :
      HasFrameAlongAt (I := I) cov e b (surfaceTimeCurve F s)
        (fun τ => V (s, τ)) t A := by
    simpa [HasPBTimeCovDerivAt, HasPBCovAlongAt] using
      (HasPBCovDerivAt.toFrame
        (I := I) (I' := 𝓘(Real, Real)) (cov := cov)
        (f := surfaceTimeCurve F s) (S := fun τ => V (s, τ))
        (y := t) (u := (1 : TangentSpace 𝓘(Real, Real) t))
        hA e b hx)
  exact HasFrameDerivAt.frame_vec_eq (I := I) (I' := 𝓘(Real, Real))
    (cov := cov) hf

/-- A two-parameter covariant 2-jet of a surface field.

`Vs` is locally `D_s V`, `Vt` is locally `D_t V`, while `DstV` and `DtsV`
are the pointwise second derivatives `D_s(D_t V)` and `D_t(D_s V)`. -/
structure HasPBSurfaceCovDeriv2At
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (V Vs Vt : SurfaceFieldAlong I F)
    (s t : Real) (DstV DtsV : TangentSpace I (F (s, t))) : Prop where
  has_param_germ :
    ∀ᶠ q : Real × Real in 𝓝 (s, t),
      HasPBParamCovDerivAt (I := I) cov F V q.1 q.2 (Vs q)
  has_time_germ :
    ∀ᶠ q : Real × Real in 𝓝 (s, t),
      HasPBTimeCovDerivAt (I := I) cov F V q.1 q.2 (Vt q)
  has_param_time :
    HasPBParamCovDerivAt (I := I) cov F Vt s t DstV
  has_time_param :
    HasPBTimeCovDerivAt (I := I) cov F Vs s t DtsV

/-- Frame-vector expansion of `D_s(D_t V)` from a surface 2-jet.

The hypotheses `hΓt`, `hvt`, and `hvs` are exactly the scalar/vector
coefficient regularity needed to differentiate the time-direction frame
formula in the parameter direction. -/
theorem HasPBSurfaceCovDeriv2At.dst_frame
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V Vs Vt : SurfaceFieldAlong I F}
    {s t : Real} {DstV DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F V Vs Vt s t DstV DtsV)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hmem : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet)
    {dΓt_s : Matrix ι ι Real} {vst vs : ι -> Real}
    (hΓt : HasDerivAt
      (fun σ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t)) dΓt_s s)
    (hvt : HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real => frameVec (I := I) e b (V (σ, t))) vs s) :
    frameVec (I := I) e b DstV =
      coeffCov
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (vst + dΓt_s.mulVec (frameVec (I := I) e b (V (s, t))) +
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t
            (1 : TangentSpace 𝓘(Real, Real) t)).mulVec vs)
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t
            (1 : TangentSpace 𝓘(Real, Real) t))
          (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
            (surfaceTimeCurve F s) (fun τ => V (s, τ)) t
            (1 : TangentSpace 𝓘(Real, Real) t))
          (frameVec (I := I) e b (V (s, t)))) := by
  have hx : F (s, t) ∈ e.baseSet := hmem.self_of_nhds
  have hDst :=
    HasPBParamCovDerivAt.frame_vec_eq (I := I) (cov := cov)
      hjet.has_param_time e b hx
  have htime_at :
      HasPBTimeCovDerivAt (I := I) cov F V s t (Vt (s, t)) :=
    hjet.has_time_germ.self_of_nhds
  have hVt_at :=
    HasPBTimeCovDerivAt.frame_vec_eq (I := I) (cov := cov)
      htime_at e b hx
  have htime_line :
      (fun σ : Real => frameVec (I := I) e b (Vt (σ, t))) =ᶠ[𝓝 s]
        (fun σ : Real =>
          coeffCov
            (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
              (surfaceTimeCurve F σ) t
              (1 : TangentSpace 𝓘(Real, Real) t))
            (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
              (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
              (1 : TangentSpace 𝓘(Real, Real) t))
            (frameVec (I := I) e b (V (σ, t)))) := by
    filter_upwards [eventually_prod_left hjet.has_time_germ, hmem] with σ hσ hσmem
    exact HasPBTimeCovDerivAt.frame_vec_eq (I := I) (cov := cov)
      hσ e b hσmem
  have htime_deriv :
      HasDerivAt (fun σ : Real => frameVec (I := I) e b (Vt (σ, t)))
        (vst + dΓt_s.mulVec (frameVec (I := I) e b (V (s, t))) +
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t
            (1 : TangentSpace 𝓘(Real, Real) t)).mulVec vs) s := by
    have hraw := hasDerivAt_coeffCov
      (Γ := fun σ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t))
      (v := fun σ : Real => frameVec (I := I) e b (V (σ, t)))
      (dvFun := fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t))
      hΓt hvs hvt
    exact hraw.congr_of_eventuallyEq htime_line
  have hderivVec :=
    frameDerivVec_eq_of_hasDerivAt (I := I) e b
      (gamma := surfaceParamCurve F t)
      (S := fun σ => Vt (σ, t)) htime_deriv
  rw [hDst, hderivVec, hVt_at]

/-- Frame-vector expansion of `D_t(D_s V)` from a surface 2-jet. -/
theorem HasPBSurfaceCovDeriv2At.dts_frame
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V Vs Vt : SurfaceFieldAlong I F}
    {s t : Real} {DstV DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F V Vs Vt s t DstV DtsV)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hmem : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet)
    {dΓs_t : Matrix ι ι Real} {vts vt : ι -> Real}
    (hΓs : HasDerivAt
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s)) dΓs_t t)
    (hvs : HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real => frameVec (I := I) e b (V (s, τ))) vt t) :
    frameVec (I := I) e b DtsV =
      coeffCov
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        (vts + dΓs_t.mulVec (frameVec (I := I) e b (V (s, t))) +
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s
            (1 : TangentSpace 𝓘(Real, Real) s)).mulVec vt)
        (coeffCov
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s
            (1 : TangentSpace 𝓘(Real, Real) s))
          (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
            (surfaceParamCurve F t) (fun σ => V (σ, t)) s
            (1 : TangentSpace 𝓘(Real, Real) s))
          (frameVec (I := I) e b (V (s, t)))) := by
  have hx : F (s, t) ∈ e.baseSet := hmem.self_of_nhds
  have hDts :=
    HasPBTimeCovDerivAt.frame_vec_eq (I := I) (cov := cov)
      hjet.has_time_param e b hx
  have hparam_at :
      HasPBParamCovDerivAt (I := I) cov F V s t (Vs (s, t)) :=
    hjet.has_param_germ.self_of_nhds
  have hVs_at :=
    HasPBParamCovDerivAt.frame_vec_eq (I := I) (cov := cov)
      hparam_at e b hx
  have hparam_line :
      (fun τ : Real => frameVec (I := I) e b (Vs (s, τ))) =ᶠ[𝓝 t]
        (fun τ : Real =>
          coeffCov
            (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
              (surfaceParamCurve F τ) s
              (1 : TangentSpace 𝓘(Real, Real) s))
            (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
              (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
              (1 : TangentSpace 𝓘(Real, Real) s))
            (frameVec (I := I) e b (V (s, τ)))) := by
    filter_upwards [eventually_prod_right hjet.has_param_germ, hmem] with τ hτ hτmem
    exact HasPBParamCovDerivAt.frame_vec_eq (I := I) (cov := cov)
      hτ e b hτmem
  have hparam_deriv :
      HasDerivAt (fun τ : Real => frameVec (I := I) e b (Vs (s, τ)))
        (vts + dΓs_t.mulVec (frameVec (I := I) e b (V (s, t))) +
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s
            (1 : TangentSpace 𝓘(Real, Real) s)).mulVec vt) t := by
    have hraw := hasDerivAt_coeffCov
      (Γ := fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s))
      (v := fun τ : Real => frameVec (I := I) e b (V (s, τ)))
      (dvFun := fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s))
      hΓs hvt hvs
    exact hraw.congr_of_eventuallyEq hparam_line
  have hderivVec :=
    frameDerivVec_eq_of_hasDerivAt (I := I) e b
      (gamma := surfaceTimeCurve F s)
      (S := fun τ => Vs (s, τ)) hparam_deriv
  rw [hDts, hderivVec, hVs_at]

/-- Fixed-frame coefficient commutator produced by a surface 2-jet.

This is the geometric-calculus bridge before curvature identification: the
right hand side is the usual curvature matrix expression
`∂s Γt - ∂t Γs + ΓsΓt - ΓtΓs` applied to the coefficient vector of `V`. -/
theorem HasPBSurfaceCovDeriv2At.frame_comm
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V Vs Vt : SurfaceFieldAlong I F}
    {s t : Real} {DstV DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F V Vs Vt s t DstV DtsV)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hmem_s : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet)
    (hmem_t : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet)
    {dΓt_s dΓs_t : Matrix ι ι Real} {vs vt vst vts : ι -> Real}
    (hΓt : HasDerivAt
      (fun σ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t)) dΓt_s s)
    (hvt_s : HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real => frameVec (I := I) e b (V (σ, t))) vs s)
    (hΓs : HasDerivAt
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s)) dΓs_t t)
    (hvs_t : HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real => frameVec (I := I) e b (V (s, τ))) vt t)
    (hmix : vst = vts) :
    frameVec (I := I) e b (DstV - DtsV) =
      (dΓt_s - dΓs_t +
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s) *
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t) -
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t) *
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s)).mulVec
        (frameVec (I := I) e b (V (s, t))) := by
  have hdst := hjet.dst_frame (I := I) e b hmem_s hΓt hvt_s hvs
  have hdts := hjet.dts_frame (I := I) e b hmem_t hΓs hvs_t hvt
  have hvs_eq :=
    frameDerivVec_eq_of_hasDerivAt (I := I) e b
      (gamma := surfaceParamCurve F t)
      (S := fun σ => V (σ, t)) hvs
  have hvt_eq :=
    frameDerivVec_eq_of_hasDerivAt (I := I) e b
      (gamma := surfaceTimeCurve F s)
      (S := fun τ => V (s, τ)) hvt
  calc
    frameVec (I := I) e b (DstV - DtsV) =
        frameVec (I := I) e b DstV - frameVec (I := I) e b DtsV := by
          ext k
          simp [frameVec]
    _ =
        (dΓt_s - dΓs_t +
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s
            (1 : TangentSpace 𝓘(Real, Real) s) *
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t
            (1 : TangentSpace 𝓘(Real, Real) t) -
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t
            (1 : TangentSpace 𝓘(Real, Real) t) *
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s
            (1 : TangentSpace 𝓘(Real, Real) s)).mulVec
          (frameVec (I := I) e b (V (s, t))) := by
          rw [hdst, hdts, hvs_eq, hvt_eq]
          exact coeffCov_comm_at
            (v := frameVec (I := I) e b (V (s, t)))
            (vs := vs) (vt := vt) (vst := vst) (vts := vts)
            (Γs := frameGammaMat
              (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
              (surfaceParamCurve F t) s
              (1 : TangentSpace 𝓘(Real, Real) s))
            (Γt := frameGammaMat
              (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
              (surfaceTimeCurve F s) t
              (1 : TangentSpace 𝓘(Real, Real) t))
            (dΓt_s := dΓt_s) (dΓs_t := dΓs_t) hmix

/-- Same as `HasPBSurfaceCovDeriv2At.frame_comm`, packaged through
`frameCurvMat`. -/
theorem HasPBSurfaceCovDeriv2At.frame_comm_mat
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V Vs Vt : SurfaceFieldAlong I F}
    {s t : Real} {DstV DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F V Vs Vt s t DstV DtsV)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hmem_s : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet)
    (hmem_t : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet)
    {dΓt_s dΓs_t : Matrix ι ι Real} {vs vt vst vts : ι -> Real}
    (hΓt : HasDerivAt
      (fun σ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t)) dΓt_s s)
    (hvt_s : HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real => frameVec (I := I) e b (V (σ, t))) vs s)
    (hΓs : HasDerivAt
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s)) dΓs_t t)
    (hvs_t : HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real => frameVec (I := I) e b (V (s, τ))) vt t)
    (hmix : vst = vts) :
    frameVec (I := I) e b (DstV - DtsV) =
      (frameCurvMat
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        dΓt_s dΓs_t).mulVec
        (frameVec (I := I) e b (V (s, t))) := by
  simpa [frameCurvMat] using
    hjet.frame_comm (I := I) e b hmem_s hmem_t hΓt hvt_s hvs hΓs hvs_t hvt hmix

/-- Jacobi-facing form of the fixed-frame commutator: if `D_s(D_t V)=0`,
then `D_t(D_s V)` has coefficients `-R(S,T)V` in the same frame. -/
theorem HasPBSurfaceCovDeriv2At.frame_dts_neg
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V Vs Vt : SurfaceFieldAlong I F}
    {s t : Real} {DstV DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F V Vs Vt s t DstV DtsV)
    (hDst : DstV = 0)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hmem_s : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet)
    (hmem_t : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet)
    {dΓt_s dΓs_t : Matrix ι ι Real} {vs vt vst vts : ι -> Real}
    (hΓt : HasDerivAt
      (fun σ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t)) dΓt_s s)
    (hvt_s : HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real => frameVec (I := I) e b (V (σ, t))) vs s)
    (hΓs : HasDerivAt
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s)) dΓs_t t)
    (hvs_t : HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real => frameVec (I := I) e b (V (s, τ))) vt t)
    (hmix : vst = vts) :
    frameVec (I := I) e b DtsV =
      -((frameCurvMat
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        dΓt_s dΓs_t).mulVec
        (frameVec (I := I) e b (V (s, t)))) := by
  have hcomm := hjet.frame_comm_mat (I := I) e b hmem_s hmem_t
    hΓt hvt_s hvs hΓs hvs_t hvt hmix
  have hneg :
      -frameVec (I := I) e b DtsV =
        (frameCurvMat
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceParamCurve F t) s
            (1 : TangentSpace 𝓘(Real, Real) s))
          (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
            (surfaceTimeCurve F s) t
            (1 : TangentSpace 𝓘(Real, Real) t))
          dΓt_s dΓs_t).mulVec
          (frameVec (I := I) e b (V (s, t))) := by
    have hframe_neg :
        frameVec (I := I) e b (-DtsV) = -frameVec (I := I) e b DtsV := by
      ext k
      simp [frameVec]
    simpa [hDst, hframe_neg] using hcomm
  calc
    frameVec (I := I) e b DtsV = -(-frameVec (I := I) e b DtsV) := by simp
    _ =
      -((frameCurvMat
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        dΓt_s dΓs_t).mulVec
        (frameVec (I := I) e b (V (s, t)))) := by
        rw [hneg]

/-- Vector form of `HasPBSurfaceCovDeriv2At.frame_dts_neg`, reconstructed in
the same fixed local frame. -/
theorem HasPBSurfaceCovDeriv2At.frame_dts_neg_vec
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {V Vs Vt : SurfaceFieldAlong I F}
    {s t : Real} {DstV DtsV : TangentSpace I (F (s, t))}
    (hjet : HasPBSurfaceCovDeriv2At (I := I) cov F V Vs Vt s t DstV DtsV)
    (hDst : DstV = 0)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E)
    (hmem_s : ∀ᶠ σ : Real in 𝓝 s, F (σ, t) ∈ e.baseSet)
    (hmem_t : ∀ᶠ τ : Real in 𝓝 t, F (s, τ) ∈ e.baseSet)
    {dΓt_s dΓs_t : Matrix ι ι Real} {vs vt vst vts : ι -> Real}
    (hΓt : HasDerivAt
      (fun σ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F σ) t
          (1 : TangentSpace 𝓘(Real, Real) t)) dΓt_s s)
    (hvt_s : HasDerivAt
      (fun σ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceTimeCurve F σ) (fun τ => V (σ, τ)) t
          (1 : TangentSpace 𝓘(Real, Real) t)) vst s)
    (hvs : HasDerivAt
      (fun σ : Real => frameVec (I := I) e b (V (σ, t))) vs s)
    (hΓs : HasDerivAt
      (fun τ : Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F τ) s
          (1 : TangentSpace 𝓘(Real, Real) s)) dΓs_t t)
    (hvs_t : HasDerivAt
      (fun τ : Real =>
        frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b
          (surfaceParamCurve F τ) (fun σ => V (σ, τ)) s
          (1 : TangentSpace 𝓘(Real, Real) s)) vts t)
    (hvt : HasDerivAt
      (fun τ : Real => frameVec (I := I) e b (V (s, τ))) vt t)
    (hmix : vst = vts) :
    DtsV =
      -frameCurvVec (I := I) e b
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceParamCurve F t) s
          (1 : TangentSpace 𝓘(Real, Real) s))
        (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
          (surfaceTimeCurve F s) t
          (1 : TangentSpace 𝓘(Real, Real) t))
        dΓt_s dΓs_t (V (s, t)) := by
  let Γs : Matrix ι ι Real :=
      (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
        (surfaceParamCurve F t) s
        (1 : TangentSpace 𝓘(Real, Real) s))
  let Γt : Matrix ι ι Real :=
      (frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b
        (surfaceTimeCurve F s) t
        (1 : TangentSpace 𝓘(Real, Real) t))
  let c : ι -> Real :=
    (frameCurvMat Γs Γt dΓt_s dΓs_t).mulVec
      (frameVec (I := I) e b (V (s, t)))
  have hx : F (s, t) ∈ e.baseSet := hmem_s.self_of_nhds
  apply (frameVec_eq_iff (I := I) e b hx).mp
  have hcoeff := hjet.frame_dts_neg (I := I) hDst e b hmem_s hmem_t
    hΓt hvt_s hvs hΓs hvs_t hvt hmix
  have hright :
      frameVec (I := I) e b
          (-(frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
            (V (s, t)))) =
        -c := by
    have hneg :
        frameVec (I := I) e b
            (-(frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
              (V (s, t)))) =
          -frameVec (I := I) e b
            (frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t
              (V (s, t))) := by
      ext k
      simp [frameVec]
    rw [hneg, frameVec_frameCurvVec (I := I) e b hx Γs Γt dΓt_s dΓs_t
      (V (s, t))]
  change frameVec (I := I) e b DtsV =
    frameVec (I := I) e b
      (-(frameCurvVec (I := I) e b Γs Γt dΓt_s dΓs_t (V (s, t))))
  rw [hcoeff, hright]

section CurveFrameCompat

variable [FiniteDimensional Real E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A representative-based along-curve derivative satisfies the local-frame
formula in every tangent local frame containing the curve point. -/
theorem HasPullbackCovariantDerivativeAlongCurveAt.toFrame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {S : VectorFieldAlong I gamma}
    {t : Real} {A : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov gamma S t A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : gamma t ∈ e.baseSet) :
    HasFrameAlongAt (I := I) cov e b gamma S t A :=
  HasPullbackCovariantDerivativeAt.toFrame
    (I := I) (I' := 𝓘(Real, Real)) hA e b hx

/-- A representative-based along-curve derivative produces the canonical
frame-defined along-curve derivative. -/
theorem HasPullbackCovariantDerivativeAlongCurveAt.toPBCov
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {S : VectorFieldAlong I gamma}
    {t : Real} {A : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantDerivativeAlongCurveAt (I := I) cov gamma S t A) :
    HasPBCovAlongAt (I := I) cov gamma S t A := by
  simpa [HasPBCovAlongAt] using
    (HasPullbackCovariantDerivativeAt.toPBCov
      (I := I) (I' := 𝓘(Real, Real)) hA)

/-- A representative-based pullback acceleration satisfies the local-frame
acceleration formula in every tangent local frame containing the curve point. -/
theorem HasPullbackCovariantAccelerationAt.toFrame
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {A : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantAccelerationAt (I := I) cov gamma t A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : gamma t ∈ e.baseSet) :
    HasFrameAccelAt (I := I) cov e b gamma t A :=
  HasPullbackCovariantDerivativeAlongCurveAt.toFrame
    (I := I) hA e b hx

/-- A representative-based pullback acceleration produces the canonical
frame-defined acceleration relation. -/
theorem HasPullbackCovariantAccelerationAt.toPBCov
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {t : Real} {A : TangentSpace I (gamma t)}
    (hA : HasPullbackCovariantAccelerationAt (I := I) cov gamma t A) :
    HasPBCovAccelAt (I := I) cov gamma t A :=
  HasPullbackCovariantDerivativeAlongCurveAt.toPBCov (I := I) hA

end CurveFrameCompat

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
