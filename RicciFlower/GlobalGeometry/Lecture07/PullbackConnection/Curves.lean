import RicciFlower.GlobalGeometry.Lecture07.PullbackConnection.Frame


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
    {ι : Type*} [Fintype ι]
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (hx : x ∈ e.baseSet)
    (c : ι -> Real) :
    frameVec (I := I) e b (frameSum (I := I) e b c : TangentSpace I x) = c := by
  classical
  ext k
  rw [frameVec, frameSum]
  rw [localFrame_coeff_eq_basis_repr (I := I) e b hx k]
  simp only [e.localFrame_apply_of_mem_baseSet b hx, map_sum, map_smul,
    Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single k]
  · rw [Finsupp.single_eq_same, mul_one]
  · intro j _ hj
    rw [Finsupp.single_eq_of_ne (a := j) (b := (1 : Real)) (a' := k) (Ne.symm hj),
      mul_zero]
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
    {ι : Type*} [Fintype ι]
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
    {ι : Type*} [Fintype ι]
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
    {ι : Type*} [Fintype ι]
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
    {ι : Type*} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
    {ι : Type} [Fintype ι]
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
variable {ι : Type*} [Fintype ι]

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
