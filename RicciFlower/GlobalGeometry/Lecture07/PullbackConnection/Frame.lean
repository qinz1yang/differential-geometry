import RicciFlower.GlobalGeometry.Lecture07.PullbackConnection.Base


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
    {ι κ : Type} [Fintype κ]
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
  classical
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
    {ι κ : Type} [Fintype ι] [Fintype κ]
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
  classical
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
    {ι κ : Type} [Fintype ι] [Fintype κ]
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
    {ι : Type*} [Fintype ι]
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
    {ι : Type*} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {f : N -> M}
    {S : PullbackSection f (TangentSpace I)} {y : N}
    {u : TangentSpace I' y} {A B : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A)
    (hB : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u B) :
    A = B := by
  classical
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
    {ι : Type} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {f : N -> M}
    {S : PullbackSection f (TangentSpace I)} {y : N}
    {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A) :
    HasPBCovDerivAt (I := I) (I' := I') cov f S y u A := by
  classical
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
    {ι : Type} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasPBCovDerivAt (I := I) (I' := I') cov f S y u A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : f y ∈ e.baseSet) :
    HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A := by
  classical
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
    {ι : Type*} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {f : N -> M} {S : PullbackSection f (TangentSpace I)}
    {y : N} {u : TangentSpace I' y} {A : TangentSpace I (f y)}
    (hA : HasPullbackCovariantDerivativeAt
      (I := I) (I' := I') (F := E) (V := TangentSpace I) cov f S y u A)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) (hx : f y ∈ e.baseSet) :
    HasFrameDerivAt (I := I) (I' := I') cov e b f S y u A := by
  classical
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

end Lecture07
end GlobalGeometry
end RicciFlower
