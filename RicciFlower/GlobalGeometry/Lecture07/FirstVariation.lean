import RicciFlower.GlobalGeometry.Jacobi
import RicciFlower.GlobalGeometry.Lecture07.CoordinateEquation
import RicciFlower.GlobalGeometry.Lecture07.SurfaceCalculus
import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.LeviCivita.Torsion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.4: first variation of arc length

This file adds the book-facing arc-length and energy interfaces for Lecture 7.4.
The actual first-variation formula is represented by predicates whose right
hand sides use the pullback covariant-derivative API from Lecture 7.3.  Formal
fixed-endpoint and geodesic corollaries are proved here; the remaining analytic
producer is differentiating the speed integral on a compact parameter tube and
performing the final integration-by-parts assembly.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle Filter intervalIntegral
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-! ## Metric product-rule producer -/

/-- Expand a tangent-space inner product in any local frame. -/
private theorem inner_eq_sum_frame
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {x : M} (hx : x ∈ e.baseSet)
    (u v : TangentSpace I x) :
    g.inner x u v =
      ∑ i : ι, ∑ j : ι,
        frameVec (I := I) e b u i * frameVec (I := I) e b v j *
          Coordinates.metricCompForMetricInFrame (I := I) g (e.localFrame b) x i j := by
  classical
  have hu :
      u = ∑ i : ι,
        frameVec (I := I) e b u i • e.localFrame b i x := by
    calc
      u = ∑ i : ι, (e.basisAt b hx).repr u i • e.localFrame b i x := by
        rw [← (e.basisAt b hx).sum_repr u]
        simp [e.localFrame_apply_of_mem_baseSet b hx]
      _ = ∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [frameVec, localFrame_coeff_eq_basis_repr (I := I) e b hx i u]
  have hv :
      v = ∑ j : ι,
        frameVec (I := I) e b v j • e.localFrame b j x := by
    calc
      v = ∑ j : ι, (e.basisAt b hx).repr v j • e.localFrame b j x := by
        rw [← (e.basisAt b hx).sum_repr v]
        simp [e.localFrame_apply_of_mem_baseSet b hx]
      _ = ∑ j : ι, frameVec (I := I) e b v j • e.localFrame b j x := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [frameVec, localFrame_coeff_eq_basis_repr (I := I) e b hx j v]
  calc
    g.inner x u v =
        g.inner x
          (∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x) v := by
            exact congrArg (fun z => g.inner x z v) hu
    _ =
        g.inner x
          (∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x)
          (∑ j : ι, frameVec (I := I) e b v j • e.localFrame b j x) := by
            exact congrArg (fun z =>
              g.inner x
                (∑ i : ι, frameVec (I := I) e b u i • e.localFrame b i x) z) hv
    _ = ∑ j : ι, ∑ i : ι,
        frameVec (I := I) e b u i * frameVec (I := I) e b v j *
          Coordinates.metricCompForMetricInFrame (I := I) g (e.localFrame b) x i j := by
            simp [Coordinates.metricCompForMetricInFrame, map_sum, Finset.mul_sum,
              mul_assoc, mul_left_comm]
    _ = ∑ i : ι, ∑ j : ι,
        frameVec (I := I) e b u i * frameVec (I := I) e b v j *
          Coordinates.metricCompForMetricInFrame (I := I) g (e.localFrame b) x i j := by
            rw [Finset.sum_comm]

/-- A fixed-frame along-curve covariant-derivative witness contains the
ordinary derivative of the frame-coordinate vector. -/
private theorem HasFrameAlongAt.hasDerivAt_frameVec
    {ι : Type*} [Fintype ι]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {e : TangentTriv (I := I) (M := M)} [MemTrivializationAtlas e]
    {b : Module.Basis ι Real E} {gamma : Curve M}
    {S : VectorFieldAlong I gamma} {t : Real}
    {A : TangentSpace I (gamma t)}
    (hA : HasFrameAlongAt (I := I) cov e b gamma S t A) :
    HasDerivAt (fun r : Real => frameVec (I := I) e b (S r))
      (frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M)
        e b gamma S t (1 : TangentSpace 𝓘(Real, Real) t)) t := by
  rw [hasDerivAt_pi]
  intro k
  have hkmd :
      MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t :=
    (hA.2.2 k).1
  have hkmf :
      HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t) :=
    hkmd.hasMFDerivAt
  have hkf :
      HasFDerivAt
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r))
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t) t :=
    HasMFDerivAt.hasFDerivAt hkmf
  have hk :
      HasDerivAt
        (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r))
        ((mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun r : Real => e.localFrame_coeff I b k (gamma r) (S r)) t)
            (1 : TangentSpace 𝓘(Real, Real) t)) t :=
    HasFDerivAt.hasDerivAt hkf
  simpa [frameVec, frameDerivVec, frameCoeffDeriv,
    RicciFlower.extDerivFun_real_eq_mfderiv] using hk

/-- Metric compatibility gives the derivative of local-frame metric
components along a differentiable real curve. -/
private theorem metricComp_hasDerivAt_along
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (e : TangentTriv (I := I) (M := M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι Real E) {gamma : Curve M} {t : Real}
    (hx : gamma t ∈ e.baseSet)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t)
    (a c : ι) :
    HasDerivAt
      (fun r : Real =>
        Coordinates.metricCompForMetricInFrame (I := I) g
          (e.localFrame b) (gamma r) a c)
      ((∑ p : ι,
          frameGamma (I := I) (M := M) cov e b (gamma t)
            (curveVelocity I gamma t) a p *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (e.localFrame b) (gamma t) p c) +
        (∑ p : ι,
          frameGamma (I := I) (M := M) cov e b (gamma t)
            (curveVelocity I gamma t) c p *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (e.localFrame b) (gamma t) a p)) t := by
  classical
  let frame := e.localFrame b
  let hframe := e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hf : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => Coordinates.metricCompForMetricInFrame (I := I) g frame y a c)
      (gamma t) :=
    Coordinates.metricComp_mdiffAt (I := I) g frame hframe e.open_baseSet hx a c
  have hderiv :
      HasDerivAt
        (fun r : Real =>
          Coordinates.metricCompForMetricInFrame (I := I) g frame (gamma r) a c)
        (extDerivFun (I := I)
          (fun y : M => Coordinates.metricCompForMetricInFrame (I := I) g frame y a c)
          (gamma t) (curveVelocity I gamma t)) t :=
    extDerivFun_along_curve_eq_deriv (I := I) hf hgamma
  have hformula :=
    Coordinates.metricComp_extDeriv_tangent
      (I := I) g cov hmc frame hframe e.open_baseSet hx
      (curveVelocity I gamma t) a c
  rw [hformula] at hderiv
  simpa [frame, hframe, frameGamma, Coordinates.christoffelAlongInFrame]
    using hderiv

/-- Pure coefficient algebra behind metric compatibility:
differentiate `Sᵢ Tⱼ Gᵢⱼ`, substitute
`G'ᵢⱼ = Γᵖᵢ Gₚⱼ + Γᵖⱼ Gᵢₚ`, and reindex the Christoffel terms into
`⟨∇S,T⟩ + ⟨S,∇T⟩`. -/
private theorem frame_inner_product_rule_algebra
    {ι : Type*} [Fintype ι]
    (S T dS dT : ι -> Real) (Γ : Matrix ι ι Real)
    (G : ι -> ι -> Real) :
    (∑ i : ι, ∑ j : ι,
        ((dS i * T j + S i * dT j) * G i j +
          (S i * T j) *
            ((∑ p : ι, Γ p i * G p j) +
              (∑ p : ι, Γ p j * G i p)))) =
      (∑ i : ι, ∑ j : ι,
        coeffCov Γ dS S i * T j * G i j) +
      (∑ i : ι, ∑ j : ι,
        S i * coeffCov Γ dT T j * G i j) := by
  classical
  have hΓS :
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p i * G p j)) =
        (∑ i : ι, ∑ j : ι,
          (∑ p : ι, Γ i p * S p) * T j * G i j) := by
    calc
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p i * G p j))
          = ∑ i : ι, ∑ j : ι, ∑ p : ι,
              S i * T j * (Γ p i * G p j) := by
              simp [Finset.mul_sum]
      _ = ∑ i : ι, ∑ p : ι, ∑ j : ι,
              S i * T j * (Γ p i * G p j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ i : ι, ∑ j : ι,
              S i * T j * (Γ p i * G p j) := by
              rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ j : ι, ∑ i : ι,
              S i * T j * (Γ p i * G p j) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ j : ι,
              (∑ i : ι, Γ p i * S i) * T j * G p j := by
              refine Finset.sum_congr rfl fun p _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
      _ = ∑ i : ι, ∑ j : ι,
              (∑ p : ι, Γ i p * S p) * T j * G i j := rfl
  have hΓT :
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p j * G i p)) =
        (∑ i : ι, ∑ j : ι,
          S i * (∑ p : ι, Γ j p * T p) * G i j) := by
    calc
      (∑ i : ι, ∑ j : ι,
          S i * T j * (∑ p : ι, Γ p j * G i p))
          = ∑ i : ι, ∑ j : ι, ∑ p : ι,
              S i * T j * (Γ p j * G i p) := by
              simp [Finset.mul_sum]
      _ = ∑ i : ι, ∑ p : ι, ∑ j : ι,
              S i * T j * (Γ p j * G i p) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ p : ι,
              S i * (∑ j : ι, Γ p j * T j) * G i p := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.mul_sum]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
      _ = ∑ i : ι, ∑ j : ι,
              S i * (∑ p : ι, Γ j p * T p) * G i j := rfl
  have hΓS' :
      (∑ i : ι, ∑ j : ι, ∑ p : ι,
          S i * T j * (Γ p i * G p j)) =
        (∑ i : ι, ∑ j : ι,
          (∑ p : ι, Γ i p * S p) * T j * G i j) := by
    simpa [Finset.mul_sum] using hΓS
  have hΓT' :
      (∑ i : ι, ∑ j : ι, ∑ p : ι,
          S i * T j * (Γ p j * G i p)) =
        (∑ i : ι, ∑ j : ι,
          (∑ p : ι, S i * (Γ j p * T p)) * G i j) := by
    simpa [Finset.mul_sum] using hΓT
  simp [coeffCov, Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, add_mul]
  rw [hΓS', hΓT']
  ring

/-- Metric-compatible product rule for the inner product of two pullback
fields along a real curve. -/
theorem inner_hasDerivAt_of_pbCov
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {gamma : Curve M} {S T : VectorFieldAlong I gamma} {t : Real}
    {A B : TangentSpace I (gamma t)}
    (hS : HasPBCovAlongAt (I := I) cov gamma S t A)
    (hT : HasPBCovAlongAt (I := I) cov gamma T t B) :
    HasDerivAt
      (fun r : Real => g.inner (gamma r) (S r) (T r))
      (g.inner (gamma t) A (T t) + g.inner (gamma t) (S t) B) t := by
  classical
  let e := Coordinates.coordinateTrivializationAt (I := I) (gamma t)
  let b : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real E :=
    Module.finBasis Real E
  have hx : gamma t ∈ e.baseSet := by
    change (chartAt H (gamma t)).source (gamma t)
    exact mem_chart_source H (gamma t)
  have hSf : HasFrameAlongAt (I := I) cov e b gamma S t A := by
    simpa [HasPBCovAlongAt, HasFrameAlongAt] using
      (HasPBCovDerivAt.toFrame (I := I) (I' := 𝓘(Real, Real))
        (cov := cov) (f := gamma) (S := S) (y := t)
        (u := (1 : TangentSpace 𝓘(Real, Real) t)) (A := A)
        hS e b hx)
  have hTf : HasFrameAlongAt (I := I) cov e b gamma T t B := by
    simpa [HasPBCovAlongAt, HasFrameAlongAt] using
      (HasPBCovDerivAt.toFrame (I := I) (I' := 𝓘(Real, Real))
        (cov := cov) (f := gamma) (S := T) (y := t)
        (u := (1 : TangentSpace 𝓘(Real, Real) t)) (A := B)
        hT e b hx)
  let Γ : Matrix (Coordinates.CoordinateIdx (𝕜 := Real) E)
      (Coordinates.CoordinateIdx (𝕜 := Real) E) Real :=
    frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov e b gamma t
      (1 : TangentSpace 𝓘(Real, Real) t)
  let dS : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b gamma S t
      (1 : TangentSpace 𝓘(Real, Real) t)
  let dT : Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    frameDerivVec (I := I) (I' := 𝓘(Real, Real)) (M := M) e b gamma T t
      (1 : TangentSpace 𝓘(Real, Real) t)
  let G : Real ->
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun r i j =>
      Coordinates.metricCompForMetricInFrame (I := I) g
        (e.localFrame b) (gamma r) i j
  let dG : Coordinates.CoordinateIdx (𝕜 := Real) E ->
      Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γ p i * G t p j) +
      (∑ p : Coordinates.CoordinateIdx (𝕜 := Real) E,
        Γ p j * G t i p)
  let Q : Real -> Real :=
    fun r =>
      ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
          frameVec (I := I) e b (S r) i *
            frameVec (I := I) e b (T r) j * G r i j
  let dQ : Real :=
    ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        ((dS i * frameVec (I := I) e b (T t) j +
            frameVec (I := I) e b (S t) i * dT j) * G t i j +
          (frameVec (I := I) e b (S t) i *
              frameVec (I := I) e b (T t) j) * dG i j)
  have hSder :
      HasDerivAt (fun r : Real => frameVec (I := I) e b (S r)) dS t := by
    simpa [dS] using hSf.hasDerivAt_frameVec (I := I)
  have hTder :
      HasDerivAt (fun r : Real => frameVec (I := I) e b (T r)) dT t := by
    simpa [dT] using hTf.hasDerivAt_frameVec (I := I)
  have hGder (i j : Coordinates.CoordinateIdx (𝕜 := Real) E) :
      HasDerivAt (fun r : Real => G r i j) (dG i j) t := by
    have hγ : MDifferentiableAt 𝓘(Real, Real) I gamma t := hSf.2.1
    have hmetric :=
      metricComp_hasDerivAt_along (I := I) g cov hmc e b hx hγ i j
    simpa [G, dG, Γ, frameGammaMat] using hmetric
  have hQ : HasDerivAt Q dQ t := by
    dsimp [Q, dQ]
    refine HasDerivAt.fun_sum ?_
    intro i _hi
    refine HasDerivAt.fun_sum ?_
    intro j _hj
    have hSij := hasDerivAt_pi.mp hSder i
    have hTij := hasDerivAt_pi.mp hTder j
    exact ((hSij.mul hTij).mul (hGder i j))
  have hmem : ∀ᶠ r : Real in 𝓝 t, gamma r ∈ e.baseSet :=
    hSf.2.1.continuousAt.tendsto.eventually (e.open_baseSet.mem_nhds hx)
  have heq :
      (fun r : Real => g.inner (gamma r) (S r) (T r)) =ᶠ[𝓝 t] Q := by
    filter_upwards [hmem] with r hr
    exact inner_eq_sum_frame (I := I) g e b hr (S r) (T r)
  have hderiv : HasDerivAt
      (fun r : Real => g.inner (gamma r) (S r) (T r)) dQ t :=
    hQ.congr_of_eventuallyEq heq
  have hdQ :
      dQ = g.inner (gamma t) A (T t) + g.inner (gamma t) (S t) B := by
    have hAvec := HasFrameDerivAt.frame_vec_eq (I := I) hSf
    have hBvec := HasFrameDerivAt.frame_vec_eq (I := I) hTf
    have hAlg :=
      frame_inner_product_rule_algebra
        (S := frameVec (I := I) e b (S t))
        (T := frameVec (I := I) e b (T t))
        (dS := dS) (dT := dT) (Γ := Γ) (G := G t)
    calc
      dQ =
          (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              coeffCov Γ dS (frameVec (I := I) e b (S t)) i *
                frameVec (I := I) e b (T t) j * G t i j) +
          (∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              frameVec (I := I) e b (S t) i *
                coeffCov Γ dT (frameVec (I := I) e b (T t)) j * G t i j) := by
            simpa [dQ, dG, G] using hAlg
      _ = g.inner (gamma t) A (T t) + g.inner (gamma t) (S t) B := by
            rw [inner_eq_sum_frame (I := I) g e b hx A (T t)]
            rw [inner_eq_sum_frame (I := I) g e b hx (S t) B]
            rw [hAvec, hBvec]
  simpa [hdQ] using hderiv

/-! ## Arc-length and energy functionals -/

/-- Pointwise speed of a curve with respect to `g`. -/
def pathSpeed (g : SmoothRiemannianMetric I M) (gamma : Curve M) (t : Real) :
    Real :=
  Real.sqrt (speedSq (I := I) g gamma t)

/-- Arc length of a curve on the oriented interval `a..b`. -/
def pathLength (g : SmoothRiemannianMetric I M) (gamma : Curve M)
    (a b : Real) : Real :=
  ∫ t in a..b, pathSpeed (I := I) g gamma t

/-- Energy of a curve on the oriented interval `a..b`, using squared speed. -/
def pathEnergy (g : SmoothRiemannianMetric I M) (gamma : Curve M)
    (a b : Real) : Real :=
  ∫ t in a..b, speedSq (I := I) g gamma t

/-- Length of the time curves in a two-parameter variation. -/
def variationLength (g : SmoothRiemannianMetric I M) (F : Surface M)
    (a b s : Real) : Real :=
  pathLength (I := I) g (timeCurve F s) a b

/-- Energy of the time curves in a two-parameter variation. -/
def variationEnergy (g : SmoothRiemannianMetric I M) (F : Surface M)
    (a b s : Real) : Real :=
  pathEnergy (I := I) g (timeCurve F s) a b

/-- The unit tangent field `T / |T|` along a curve.  This is only intended for
use under the usual nonzero-speed hypotheses; no such hypothesis is needed to
state the expression. -/
def unitTangentAlong (g : SmoothRiemannianMetric I M) (gamma : Curve M) :
    VectorFieldAlong I gamma :=
  fun t => (pathSpeed (I := I) g gamma t)⁻¹ • curveVelocity I gamma t

theorem pathSpeed_eq_one_of_unitSpeed
    {g : SmoothRiemannianMetric I M} {gamma : Curve M}
    (h : IsUnitSpeed (I := I) g gamma) (t : Real) :
    pathSpeed (I := I) g gamma t = 1 := by
  simp [pathSpeed, h t]

theorem unitTangentAlong_eq_velocityAlong_of_unitSpeed
    {g : SmoothRiemannianMetric I M} {gamma : Curve M}
    (h : IsUnitSpeed (I := I) g gamma) :
    unitTangentAlong (I := I) g gamma = velocityAlong I gamma := by
  funext t
  simp [unitTangentAlong, velocityAlong, pathSpeed_eq_one_of_unitSpeed (I := I) h t]

private theorem coordTimeDeriv_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real => coordTimeDeriv (I := I) x0 F p.1 p.2 i)
      (s, t) := by
  let φ : Real × Real → Real :=
    fun p => surfaceCoordComp (I := I) x0 F p i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hD : ContDiffAt Real (0 : WithTop ℕ∞) (fderiv Real φ) (s, t) :=
    hφ.fderiv_right (m := (0 : WithTop ℕ∞)) (by simp)
  have happly :
      ContDiffAt Real (0 : WithTop ℕ∞)
        (fun p : Real × Real => (fderiv Real φ p) (0, (1 : Real))) (s, t) :=
    hD.clm_apply contDiffAt_const
  simpa [φ, coordTimeDeriv] using happly.continuousAt

private theorem coordParamDeriv_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real => coordParamDeriv (I := I) x0 F p.1 p.2 i)
      (s, t) := by
  let φ : Real × Real → Real :=
    fun p => surfaceCoordComp (I := I) x0 F p i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hD : ContDiffAt Real (0 : WithTop ℕ∞) (fderiv Real φ) (s, t) :=
    hφ.fderiv_right (m := (0 : WithTop ℕ∞)) (by simp)
  have happly :
      ContDiffAt Real (0 : WithTop ℕ∞)
        (fun p : Real × Real => (fderiv Real φ p) ((1 : Real), 0)) (s, t) :=
    hD.clm_apply contDiffAt_const
  simpa [φ, coordParamDeriv] using happly.continuousAt

private theorem coordTs_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real => coordTs (I := I) x0 F p.1 p.2 i)
      (s, t) := by
  let φ : Real × Real → Real :=
    fun p => surfaceCoordComp (I := I) x0 F p i
  let A : Real × Real → Real :=
    fun p => coordTimeDeriv (I := I) x0 F p.1 p.2 i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv] using hD
  have hD : ContDiffAt Real (0 : WithTop ℕ∞) (fderiv Real A) (s, t) :=
    hA.fderiv_right (m := (0 : WithTop ℕ∞)) (by simp)
  have happly :
      ContDiffAt Real (0 : WithTop ℕ∞)
        (fun p : Real × Real => (fderiv Real A p) ((1 : Real), 0)) (s, t) :=
    hD.clm_apply contDiffAt_const
  simpa [A, coordTs] using happly.continuousAt

private theorem coordTt_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real => coordTt (I := I) x0 F p.1 p.2 i)
      (s, t) := by
  let φ : Real × Real → Real :=
    fun p => surfaceCoordComp (I := I) x0 F p i
  let A : Real × Real → Real :=
    fun p => coordTimeDeriv (I := I) x0 F p.1 p.2 i
  have hφ : ContDiffAt Real ∞ φ (s, t) := by
    simpa [φ] using hF.coordCompAt_contMDiffAt (I := I) hx i
  have hA : ContDiffAt Real ∞ A (s, t) := by
    have hD : ContDiffAt Real ∞
        (fun p : Real × Real =>
          (fderiv Real φ p) (0, (1 : Real))) (s, t) := by
      have hfder := hφ.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
      exact hfder.clm_apply contDiffAt_const
    simpa [A, φ, coordTimeDeriv] using hD
  have hD : ContDiffAt Real (0 : WithTop ℕ∞) (fderiv Real A) (s, t) :=
    hA.fderiv_right (m := (0 : WithTop ℕ∞)) (by simp)
  have happly :
      ContDiffAt Real (0 : WithTop ℕ∞)
        (fun p : Real × Real => (fderiv Real A p) (0, (1 : Real))) (s, t) :=
    hD.clm_apply contDiffAt_const
  simpa [A, coordTt] using happly.continuousAt

private theorem frameVec_timeField_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0) :
    ContinuousAt
      (fun p : Real × Real =>
        frameVec (I := I) (Coordinates.coordinateTrivializationAt (I := I) x0)
          (Module.finBasis Real E) (timeField I F p))
      (s, t) := by
  rw [continuousAt_pi]
  intro i
  have hcoord := coordTimeDeriv_continuousAt_of_mem (I := I) hF hx i
  have heq :
      (fun p : Real × Real =>
        frameVec (I := I) (Coordinates.coordinateTrivializationAt (I := I) x0)
          (Module.finBasis Real E) (timeField I F p) i)
        =ᶠ[𝓝 (s, t)]
      (fun p : Real × Real => coordTimeDeriv (I := I) x0 F p.1 p.2 i) := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    have hframe := congrFun (frameVec_timeField_eq (I := I) x0 hp) i
    have hcoordEq := hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hp i
    simpa [timeField, surfaceTimeField] using hframe.trans hcoordEq
  exact hcoord.congr_of_eventuallyEq heq

private theorem frameVec_paramField_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0) :
    ContinuousAt
      (fun p : Real × Real =>
        frameVec (I := I) (Coordinates.coordinateTrivializationAt (I := I) x0)
          (Module.finBasis Real E) (paramField I F p))
      (s, t) := by
  rw [continuousAt_pi]
  intro i
  have hcoord := coordParamDeriv_continuousAt_of_mem (I := I) hF hx i
  have heq :
      (fun p : Real × Real =>
        frameVec (I := I) (Coordinates.coordinateTrivializationAt (I := I) x0)
          (Module.finBasis Real E) (paramField I F p) i)
        =ᶠ[𝓝 (s, t)]
      (fun p : Real × Real => coordParamDeriv (I := I) x0 F p.1 p.2 i) := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    have hframe := congrFun (frameVec_paramField_eq (I := I) x0 hp) i
    have hcoordEq := hF.paramFrameCoeff_eq_coordParamDeriv (I := I) hp i
    simpa [paramField, surfaceParamField] using hframe.trans hcoordEq
  exact hcoord.congr_of_eventuallyEq heq

private theorem timeFrameCoeff_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real => timeFrameCoeff (I := I) x0 F p.1 p.2 i)
      (s, t) := by
  have hcoord := coordTimeDeriv_continuousAt_of_mem (I := I) hF hx i
  have heq :
      (fun p : Real × Real => timeFrameCoeff (I := I) x0 F p.1 p.2 i)
        =ᶠ[𝓝 (s, t)]
      (fun p : Real × Real => coordTimeDeriv (I := I) x0 F p.1 p.2 i) := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    exact hF.timeFrameCoeff_eq_coordTimeDeriv (I := I) hp i
  exact hcoord.congr_of_eventuallyEq heq

private theorem paramFrameCoeff_continuousAt_of_mem
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {x0 : M} {s t : Real}
    (hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real => paramFrameCoeff (I := I) x0 F p.1 p.2 i)
      (s, t) := by
  have hcoord := coordParamDeriv_continuousAt_of_mem (I := I) hF hx i
  have heq :
      (fun p : Real × Real => paramFrameCoeff (I := I) x0 F p.1 p.2 i)
        =ᶠ[𝓝 (s, t)]
      (fun p : Real × Real => coordParamDeriv (I := I) x0 F p.1 p.2 i) := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    exact hF.paramFrameCoeff_eq_coordParamDeriv (I := I) hp i
  exact hcoord.congr_of_eventuallyEq heq

private theorem frameGammaMat_time_continuousAt
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real)
    (j k : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceTimeCurve F p.1) p.2
          (1 : TangentSpace 𝓘(Real, Real) p.2) k j)
      (s, t) := by
  classical
  let x0 : M := F (s, t)
  have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0 := by
    simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
  let rhs : Real × Real → Real := fun p =>
    ∑ i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E,
      timeFrameCoeff (I := I) x0 F p.1 p.2 i *
        Realized.christoffelCoordFun (I := I) cov x0 i j k (F p)
  have hrhs : ContinuousAt rhs (s, t) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    have hT := timeFrameCoeff_continuousAt_of_mem (I := I) hF hx i
    have hΓ : ContinuousAt
        (fun p : Real × Real =>
          Realized.christoffelCoordFun (I := I) cov x0 i j k (F p)) (s, t) := by
      have hΓmd :
          MDifferentiableAt I 𝓘(Real, Real)
            (Realized.christoffelCoordFun (I := I) cov x0 i j k)
            (F (s, t)) := by
        simpa [x0] using
          Realized.christoffelCoordFun_mdiffAt_one (I := I) cov hcov x0 i j k
      exact hΓmd.continuousAt.comp (hF.continuousAt (I := I) (s, t))
    exact hT.mul hΓ
  have heq :
      (fun p : Real × Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceTimeCurve F p.1) p.2
          (1 : TangentSpace 𝓘(Real, Real) p.2) k j)
        =ᶠ[𝓝 (s, t)] rhs := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    simpa [rhs, x0] using
      frameGammaMat_time (I := I) cov x0 F p.1 p.2 hp j k
  exact hrhs.congr_of_eventuallyEq heq

private theorem frameGammaMat_param_continuousAt
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real)
    (j k : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceParamCurve F p.2) p.1
          (1 : TangentSpace 𝓘(Real, Real) p.1) k j)
      (s, t) := by
  classical
  let x0 : M := F (s, t)
  have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0 := by
    simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
  let rhs : Real × Real → Real := fun p =>
    ∑ i : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E,
      paramFrameCoeff (I := I) x0 F p.1 p.2 i *
        Realized.christoffelCoordFun (I := I) cov x0 i j k (F p)
  have hrhs : ContinuousAt rhs (s, t) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    have hS := paramFrameCoeff_continuousAt_of_mem (I := I) hF hx i
    have hΓ : ContinuousAt
        (fun p : Real × Real =>
          Realized.christoffelCoordFun (I := I) cov x0 i j k (F p)) (s, t) := by
      have hΓmd :
          MDifferentiableAt I 𝓘(Real, Real)
            (Realized.christoffelCoordFun (I := I) cov x0 i j k)
            (F (s, t)) := by
        simpa [x0] using
          Realized.christoffelCoordFun_mdiffAt_one (I := I) cov hcov x0 i j k
      exact hΓmd.continuousAt.comp (hF.continuousAt (I := I) (s, t))
    exact hS.mul hΓ
  have heq :
      (fun p : Real × Real =>
        frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
          (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
          (Module.finBasis Real E) (surfaceParamCurve F p.2) p.1
          (1 : TangentSpace 𝓘(Real, Real) p.1) k j)
        =ᶠ[𝓝 (s, t)] rhs := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    simpa [rhs, x0] using
      frameGammaMat_param (I := I) cov x0 F p.1 p.2 hp j k
  exact hrhs.congr_of_eventuallyEq heq

private theorem dsTimeCoeffIn_continuousAt
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContinuousAt
      (fun p : Real × Real =>
        dsTimeCoeffIn (I := I) cov (F (s, t)) F p.1 p.2)
      (s, t) := by
  rw [continuousAt_pi]
  intro k
  have hTs := coordTs_continuousAt_of_mem (I := I) hF
    (by simpa using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))) k
  have hsum : ContinuousAt
      (fun p : Real × Real =>
        ∑ j : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E,
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
            (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
            (Module.finBasis Real E) (surfaceParamCurve F p.2) p.1
            (1 : TangentSpace 𝓘(Real, Real) p.1) k j *
          frameVec (I := I) (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
            (Module.finBasis Real E) (timeField I F p) j) (s, t) := by
    refine tendsto_finset_sum _ fun j _ => ?_
    exact (frameGammaMat_param_continuousAt (I := I) hcov hF s t j k).mul
      (by
        have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) (F (s, t)) :=
          Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
        exact (continuousAt_pi.mp
          (frameVec_timeField_continuousAt_of_mem (I := I) hF hx) j))
  have htotal := hTs.add hsum
  simpa [dsTimeCoeffIn, coeffCov, Matrix.mulVec, dotProduct] using htotal

private theorem dtTimeCoeffIn_continuousAt
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContinuousAt
      (fun p : Real × Real =>
        dtTimeCoeffIn (I := I) cov (F (s, t)) F p.1 p.2)
      (s, t) := by
  rw [continuousAt_pi]
  intro k
  have hTt := coordTt_continuousAt_of_mem (I := I) hF
    (by simpa using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))) k
  have hsum : ContinuousAt
      (fun p : Real × Real =>
        ∑ j : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E,
          frameGammaMat (I := I) (I' := 𝓘(Real, Real)) (M := M) cov
            (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
            (Module.finBasis Real E) (surfaceTimeCurve F p.1) p.2
            (1 : TangentSpace 𝓘(Real, Real) p.2) k j *
          frameVec (I := I) (Coordinates.coordinateTrivializationAt (I := I) (F (s, t)))
            (Module.finBasis Real E) (timeField I F p) j) (s, t) := by
    refine tendsto_finset_sum _ fun j _ => ?_
    exact (frameGammaMat_time_continuousAt (I := I) hcov hF s t j k).mul
      (by
        have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) (F (s, t)) :=
          Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
        exact (continuousAt_pi.mp
          (frameVec_timeField_continuousAt_of_mem (I := I) hF hx) j))
  have htotal := hTt.add hsum
  simpa [dtTimeCoeffIn, coeffCov, Matrix.mulVec, dotProduct] using htotal

private theorem metricComp_center_continuousAt
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real)
    (i j : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContinuousAt
      (fun p : Real × Real =>
        Coordinates.metricCompForMetricInFrame (I := I) g
          (Coordinates.coordinateFrameAt (I := I) (F (s, t))) (F p) i j)
      (s, t) := by
  let x0 : M := F (s, t)
  have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0 := by
    simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
  have hmetric :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame (I := I) g
            (Coordinates.coordinateFrameAt (I := I) x0) y i j) (F (s, t)) := by
    simpa [x0] using
      Coordinates.metricComp_mdiffAt (I := I) g
        (Coordinates.coordinateFrameAt (I := I) x0)
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0)
        (Coordinates.coordinateFrameSet_open (I := I) x0) hx i j
  exact hmetric.continuousAt.comp (hF.continuousAt (I := I) (s, t))

private theorem dsTime_time_inner_continuousAt
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContinuousAt
      (fun p : Real × Real =>
        g.inner (F p) (dsTimeField (I := I) cov F p) (timeField I F p))
      (s, t) := by
  classical
  let x0 : M := F (s, t)
  let e := Coordinates.coordinateTrivializationAt (I := I) x0
  let b : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real E :=
    Module.finBasis Real E
  let rhs : Real × Real -> Real := fun p =>
    ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        dsTimeCoeffIn (I := I) cov x0 F p.1 p.2 i *
          timeFrameCoeff (I := I) x0 F p.1 p.2 j *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (Coordinates.coordinateFrameAt (I := I) x0) (F p) i j
  have hmetric : ∀ i j : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ContinuousAt
        (fun p : Real × Real =>
          Coordinates.metricCompForMetricInFrame (I := I) g
            (Coordinates.coordinateFrameAt (I := I) x0) (F p) i j) (s, t) := by
    intro i j
    simpa [x0] using metricComp_center_continuousAt (I := I) g hF s t i j
  have hrhs : ContinuousAt rhs (s, t) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    have hds := continuousAt_pi.mp
      (dsTimeCoeffIn_continuousAt (I := I) hcov hF s t) i
    have htcoeff := timeFrameCoeff_continuousAt_of_mem (I := I) hF
      (by simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))) j
    exact (hds.mul htcoeff).mul (hmetric i j)
  have heq :
      (fun p : Real × Real =>
        g.inner (F p) (dsTimeField (I := I) cov F p) (timeField I F p))
        =ᶠ[𝓝 (s, t)] rhs := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0 := by
      simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    have hdsEq := SmoothSurface.dsTimeField_eq_fixed_eventually_prod
      (I := I) (cov := cov) hF s t
    filter_upwards [hmem, hdsEq] with p hp hdsFixed
    have hpE : F p ∈ e.baseSet := by
      simpa [e, x0, Coordinates.coordinateFrameSet,
        Coordinates.coordinateTrivializationAt] using hp
    have hdsFrame :
        frameVec (I := I) e b (dsTimeField (I := I) cov F p) =
          dsTimeCoeffIn (I := I) cov x0 F p.1 p.2 := by
      rw [hdsFixed]
      simpa [e, x0, dsTimeFieldIn] using
        frameVec_frameSum (I := I) e b hpE
          (dsTimeCoeffIn (I := I) cov x0 F p.1 p.2)
    have htimeFrame :
        frameVec (I := I) e b (timeField I F p) =
          fun i : Coordinates.CoordinateIdx (𝕜 := Real) E =>
            timeFrameCoeff (I := I) x0 F p.1 p.2 i := by
      have h := frameVec_timeField_eq (I := I) x0 hp
      simpa [e, b, x0, timeField, surfaceTimeField] using h
    calc
      g.inner (F p) (dsTimeField (I := I) cov F p) (timeField I F p)
          =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              frameVec (I := I) e b (dsTimeField (I := I) cov F p) i *
                frameVec (I := I) e b (timeField I F p) j *
                  Coordinates.metricCompForMetricInFrame (I := I) g
                    (e.localFrame b) (F p) i j := by
            simpa [e, b] using
              inner_eq_sum_frame (I := I) g e b hpE
                (dsTimeField (I := I) cov F p) (timeField I F p)
      _ = rhs p := by
            simp [rhs, hdsFrame, htimeFrame, e, b, x0,
              Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt]
  exact hrhs.congr_of_eventuallyEq heq

private theorem time_time_inner_continuousAt
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContinuousAt
      (fun p : Real × Real =>
        g.inner (F p) (timeField I F p) (timeField I F p))
      (s, t) := by
  classical
  let x0 : M := F (s, t)
  let e := Coordinates.coordinateTrivializationAt (I := I) x0
  let b : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real E :=
    Module.finBasis Real E
  let rhs : Real × Real -> Real := fun p =>
    ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        timeFrameCoeff (I := I) x0 F p.1 p.2 i *
          timeFrameCoeff (I := I) x0 F p.1 p.2 j *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (Coordinates.coordinateFrameAt (I := I) x0) (F p) i j
  have hmetric : ∀ i j : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ContinuousAt
        (fun p : Real × Real =>
          Coordinates.metricCompForMetricInFrame (I := I) g
            (Coordinates.coordinateFrameAt (I := I) x0) (F p) i j) (s, t) := by
    intro i j
    simpa [x0] using metricComp_center_continuousAt (I := I) g hF s t i j
  have hrhs : ContinuousAt rhs (s, t) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    have hicoeff := timeFrameCoeff_continuousAt_of_mem (I := I) hF
      (by simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))) i
    have hjcoeff := timeFrameCoeff_continuousAt_of_mem (I := I) hF
      (by simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))) j
    exact (hicoeff.mul hjcoeff).mul (hmetric i j)
  have heq :
      (fun p : Real × Real =>
        g.inner (F p) (timeField I F p) (timeField I F p))
        =ᶠ[𝓝 (s, t)] rhs := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0 := by
      simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    filter_upwards [hmem] with p hp
    have hpE : F p ∈ e.baseSet := by
      simpa [e, x0, Coordinates.coordinateFrameSet,
        Coordinates.coordinateTrivializationAt] using hp
    have htimeFrame :
        frameVec (I := I) e b (timeField I F p) =
          fun i : Coordinates.CoordinateIdx (𝕜 := Real) E =>
            timeFrameCoeff (I := I) x0 F p.1 p.2 i := by
      have h := frameVec_timeField_eq (I := I) x0 hp
      simpa [e, b, x0, timeField, surfaceTimeField] using h
    calc
      g.inner (F p) (timeField I F p) (timeField I F p)
          =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              frameVec (I := I) e b (timeField I F p) i *
                frameVec (I := I) e b (timeField I F p) j *
                  Coordinates.metricCompForMetricInFrame (I := I) g
                    (e.localFrame b) (F p) i j := by
            simpa [e, b] using
              inner_eq_sum_frame (I := I) g e b hpE
                (timeField I F p) (timeField I F p)
      _ = rhs p := by
            simp [rhs, htimeFrame, e, b, x0,
              Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt]
  exact hrhs.congr_of_eventuallyEq heq

private theorem param_dtTime_inner_continuousAt
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    ContinuousAt
      (fun p : Real × Real =>
        g.inner (F p) (paramField I F p) (dtTimeField (I := I) cov F p))
      (s, t) := by
  classical
  let x0 : M := F (s, t)
  let e := Coordinates.coordinateTrivializationAt (I := I) x0
  let b : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real E :=
    Module.finBasis Real E
  let rhs : Real × Real -> Real := fun p =>
    ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
        paramFrameCoeff (I := I) x0 F p.1 p.2 i *
          dtTimeCoeffIn (I := I) cov x0 F p.1 p.2 j *
            Coordinates.metricCompForMetricInFrame (I := I) g
              (Coordinates.coordinateFrameAt (I := I) x0) (F p) i j
  have hmetric : ∀ i j : Coordinates.CoordinateIdx (𝕜 := Real) E,
      ContinuousAt
        (fun p : Real × Real =>
          Coordinates.metricCompForMetricInFrame (I := I) g
            (Coordinates.coordinateFrameAt (I := I) x0) (F p) i j) (s, t) := by
    intro i j
    simpa [x0] using metricComp_center_continuousAt (I := I) g hF s t i j
  have hrhs : ContinuousAt rhs (s, t) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    have hpcoeff := paramFrameCoeff_continuousAt_of_mem (I := I) hF
      (by simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))) i
    have hdt := continuousAt_pi.mp
      (dtTimeCoeffIn_continuousAt (I := I) hcov hF s t) j
    exact (hpcoeff.mul hdt).mul (hmetric i j)
  have heq :
      (fun p : Real × Real =>
        g.inner (F p) (paramField I F p) (dtTimeField (I := I) cov F p))
        =ᶠ[𝓝 (s, t)] rhs := by
    have hU : IsOpen (Coordinates.coordinateFrameSet (I := I) x0) :=
      Coordinates.coordinateFrameSet_open (I := I) x0
    have hx : F (s, t) ∈ Coordinates.coordinateFrameSet (I := I) x0 := by
      simpa [x0] using Coordinates.coordinateFrameAt_mem (I := I) (F (s, t))
    have hmem : ∀ᶠ p : Real × Real in 𝓝 (s, t),
        F p ∈ Coordinates.coordinateFrameSet (I := I) x0 :=
      (hF.continuousAt (I := I) (s, t)).eventually_mem (hU.mem_nhds hx)
    have hdtEq := SmoothSurface.dtTimeField_eq_fixed_eventually_prod
      (I := I) (cov := cov) hF s t
    filter_upwards [hmem, hdtEq] with p hp hdtFixed
    have hpE : F p ∈ e.baseSet := by
      simpa [e, x0, Coordinates.coordinateFrameSet,
        Coordinates.coordinateTrivializationAt] using hp
    have hparamFrame :
        frameVec (I := I) e b (paramField I F p) =
          fun i : Coordinates.CoordinateIdx (𝕜 := Real) E =>
            paramFrameCoeff (I := I) x0 F p.1 p.2 i := by
      have h := frameVec_paramField_eq (I := I) x0 hp
      simpa [e, b, x0, paramField, surfaceParamField] using h
    have hdtFrame :
        frameVec (I := I) e b (dtTimeField (I := I) cov F p) =
          dtTimeCoeffIn (I := I) cov x0 F p.1 p.2 := by
      rw [hdtFixed]
      simpa [e, x0, dtTimeFieldIn] using
        frameVec_frameSum (I := I) e b hpE
          (dtTimeCoeffIn (I := I) cov x0 F p.1 p.2)
    calc
      g.inner (F p) (paramField I F p) (dtTimeField (I := I) cov F p)
          =
          ∑ i : Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : Coordinates.CoordinateIdx (𝕜 := Real) E,
              frameVec (I := I) e b (paramField I F p) i *
                frameVec (I := I) e b (dtTimeField (I := I) cov F p) j *
                  Coordinates.metricCompForMetricInFrame (I := I) g
                    (e.localFrame b) (F p) i j := by
            simpa [e, b] using
              inner_eq_sum_frame (I := I) g e b hpE
                (paramField I F p) (dtTimeField (I := I) cov F p)
      _ = rhs p := by
            simp [rhs, hparamFrame, hdtFrame, e, b, x0,
              Coordinates.coordinateFrameAt, Coordinates.coordinateTrivializationAt]
  exact hrhs.congr_of_eventuallyEq heq

private theorem dsTime_time_inner_intervalIntegrable
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    (s0 a b : Real) :
    IntervalIntegrable
      (fun t : Real =>
        g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t))
      MeasureTheory.volume a b := by
  have hcont : ContinuousOn
      (fun t : Real =>
        g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t))
      (Set.uIcc a b) := by
    refine continuousOn_of_forall_continuousAt fun t _ht => ?_
    have hp := dsTime_time_inner_continuousAt (I := I) g hcov hF s0 t
    have hline : ContinuousAt (fun τ : Real => (s0, τ)) t :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    simpa [timeCurve, timeField, surfaceTimeField, velocityAlong] using
      hp.comp hline
  exact hcont.intervalIntegrable

private theorem pathSpeed_intervalIntegrable
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    (s a b : Real) :
    IntervalIntegrable
      (fun t : Real => pathSpeed (I := I) g (timeCurve F s) t)
      MeasureTheory.volume a b := by
  have hcont : ContinuousOn
      (fun t : Real => pathSpeed (I := I) g (timeCurve F s) t)
      (Set.uIcc a b) := by
    refine continuousOn_of_forall_continuousAt fun t _ht => ?_
    have hp := time_time_inner_continuousAt (I := I) g hF s t
    have hline : ContinuousAt (fun τ : Real => (s, τ)) t :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    have hsq := hp.comp hline
    exact Real.continuous_sqrt.continuousAt.comp (by
      simpa [pathSpeed, speedSq, timeCurve, timeField, surfaceTimeField,
        velocityAlong] using hsq)
  exact hcont.intervalIntegrable

private theorem speedSq_surface_continuous
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} (hF : SmoothSurface (I := I) F) :
    Continuous
      (fun p : Real × Real => speedSq (I := I) g (timeCurve F p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have h := time_time_inner_continuousAt (I := I) g hF p.1 p.2
  simpa [speedSq, timeCurve, timeField, surfaceTimeField, velocityAlong] using h

private theorem speedSq_pos_tube
    (g : SmoothRiemannianMetric I M)
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    {s0 a b : Real}
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0)) :
    ∃ δ : Real, 0 < δ ∧
      ∀ s ∈ Set.Icc (s0 - δ) (s0 + δ),
        ∀ t ∈ Set.uIcc a b,
          (1 / 2 : Real) < speedSq (I := I) g (timeCurve F s) t := by
  classical
  let U : Set (Real × Real) :=
    {p | (1 / 2 : Real) < speedSq (I := I) g (timeCurve F p.1) p.2}
  have hUopen : IsOpen U := by
    have hcont := speedSq_surface_continuous (I := I) g hF
    simpa [U] using (isOpen_lt continuous_const hcont)
  have hslice : ({s0} : Set Real) ×ˢ Set.uIcc a b ⊆ U := by
    intro p hp
    rcases hp with ⟨hs, ht⟩
    have hp1 : p.1 = s0 := by simpa using hs
    change (1 / 2 : Real) < speedSq (I := I) g (timeCurve F p.1) p.2
    rw [hp1, hunit p.2]
    norm_num
  obtain ⟨u, v, huopen, _hvopen, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (t := Set.uIcc a b)
      isCompact_uIcc hUopen hslice
  have hs0u : s0 ∈ u := hsu (by simp)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (huopen.mem_nhds hs0u)
  refine ⟨ε / 2, by positivity, ?_⟩
  intro s hs t ht
  have hsu' : s ∈ u := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hs.1, hs.2, hεpos]
  have htv' : t ∈ v := htv ht
  have hpU : (s, t) ∈ U := huv ⟨hsu', htv'⟩
  simpa [U] using hpU

private theorem speedParamDerivIntegrand_continuousAt_of_pos
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F) {s t : Real}
    (hpos : 0 < speedSq (I := I) g (timeCurve F s) t) :
    ContinuousAt
      (fun p : Real × Real =>
        (pathSpeed (I := I) g (timeCurve F p.1) p.2)⁻¹ *
          g.inner (F p)
            (dsTimeField (I := I) cov F p)
            (timeField I F p))
      (s, t) := by
  have hsq_cont := (speedSq_surface_continuous (I := I) g hF).continuousAt
    (x := (s, t))
  have hpath_cont : ContinuousAt
      (fun p : Real × Real =>
        pathSpeed (I := I) g (timeCurve F p.1) p.2) (s, t) := by
    exact Real.continuous_sqrt.continuousAt.comp (by
      simpa [pathSpeed] using hsq_cont)
  have hpath_ne :
      pathSpeed (I := I) g (timeCurve F s) t ≠ 0 := by
    have hsqrt_pos : 0 < Real.sqrt (speedSq (I := I) g (timeCurve F s) t) :=
      Real.sqrt_pos.2 hpos
    simpa [pathSpeed] using ne_of_gt hsqrt_pos
  exact (hpath_cont.inv₀ hpath_ne).mul
    (dsTime_time_inner_continuousAt (I := I) g hcov hF s t)

private theorem param_dtTime_inner_intervalIntegrable
    [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} (hF : SmoothSurface (I := I) F)
    (s0 a b : Real) :
    IntervalIntegrable
      (fun t : Real =>
        g.inner (F (s0, t))
          (variationField I F s0 t)
          (dtTimeField (I := I) cov F (s0, t)))
      MeasureTheory.volume a b := by
  have hcont : ContinuousOn
      (fun t : Real =>
        g.inner (F (s0, t))
          (variationField I F s0 t)
          (dtTimeField (I := I) cov F (s0, t)))
      (Set.uIcc a b) := by
    refine continuousOn_of_forall_continuousAt fun t _ht => ?_
    have hp := param_dtTime_inner_continuousAt (I := I) g hcov hF s0 t
    have hline : ContinuousAt (fun τ : Real => (s0, τ)) t :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    simpa [variationField, paramField] using hp.comp hline
  exact hcont.intervalIntegrable

/-! ## Pointwise first-variation producers -/

/-- Pointwise parameter derivative of the squared speed of a smooth variation.

This is the pointwise product-rule part of the first variation formula:
metric compatibility gives the derivative of `⟨T,T⟩` in the variation
parameter.  The later torsion-free step rewrites this field as `D_t V`. -/
private theorem speedSq_param_hasDerivAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {F : Surface M} (hF : SmoothSurface (I := I) F) (s t : Real) :
    HasDerivAt
      (fun σ : Real => speedSq (I := I) g (timeCurve F σ) t)
      (2 * g.inner (F (s, t))
        (dsTimeField (I := I) cov F (s, t))
        (timeField I F (s, t))) s := by
  have hDsT :
      HasPBCovAlongAt (I := I) cov (paramCurve F t)
        (fun σ : Real => timeField I F (σ, t)) s
        (dsTimeField (I := I) cov F (s, t)) := by
    have h := SmoothSurface.hasParam_dsTime (I := I) (cov := cov) hF s t
    simpa [HasPBParamCovDerivAt, paramCurve, timeField, surfaceParamCurve,
      surfaceTimeField] using h
  have hinner :=
    inner_hasDerivAt_of_pbCov (I := I) g hmc
      (gamma := paramCurve F t)
      (S := fun σ : Real => timeField I F (σ, t))
      (T := fun σ : Real => timeField I F (σ, t))
      (t := s) hDsT hDsT
  have htarget :
      g.inner (F (s, t)) (dsTimeField (I := I) cov F (s, t))
          (curveVelocity I (timeCurve F s) t) +
        g.inner (F (s, t)) (curveVelocity I (timeCurve F s) t)
          (dsTimeField (I := I) cov F (s, t)) =
      2 * g.inner (F (s, t))
        (dsTimeField (I := I) cov F (s, t))
        (curveVelocity I (timeCurve F s) t) := by
    have hsymm :
        g.inner (F (s, t)) (curveVelocity I (timeCurve F s) t)
            (dsTimeField (I := I) cov F (s, t)) =
          g.inner (F (s, t)) (dsTimeField (I := I) cov F (s, t))
            (curveVelocity I (timeCurve F s) t) := by
      exact g.symm (F (s, t)) (curveVelocity I (timeCurve F s) t)
        (dsTimeField (I := I) cov F (s, t))
    rw [hsymm]
    ring
  change
    HasDerivAt
      (fun σ : Real =>
        g.inner (F (σ, t)) (curveVelocity I (timeCurve F σ) t)
          (curveVelocity I (timeCurve F σ) t))
      (2 * g.inner (F (s, t))
        (dsTimeField (I := I) cov F (s, t))
        (curveVelocity I (timeCurve F s) t)) s
  convert hinner using 1
  simpa [paramCurve, timeField] using htarget.symm

/-- Pointwise parameter derivative of speed at a nonzero-speed point. -/
private theorem pathSpeed_param_hasDerivAt_of_ne
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {F : Surface M} (hF : SmoothSurface (I := I) F) {s t : Real}
    (hnez : speedSq (I := I) g (timeCurve F s) t ≠ 0) :
    HasDerivAt
      (fun σ : Real => pathSpeed (I := I) g (timeCurve F σ) t)
      ((pathSpeed (I := I) g (timeCurve F s) t)⁻¹ *
        g.inner (F (s, t))
          (dsTimeField (I := I) cov F (s, t))
          (timeField I F (s, t))) s := by
  have hsq :=
    speedSq_param_hasDerivAt (I := I) g hmc hF s t
  have hsqrt := hsq.sqrt hnez
  have hderiv :
      HasDerivAt
        (fun σ : Real => pathSpeed (I := I) g (timeCurve F σ) t)
        ((2 * g.inner (F (s, t))
          (dsTimeField (I := I) cov F (s, t))
          (timeField I F (s, t))) /
            (2 * pathSpeed (I := I) g (timeCurve F s) t)) s := by
    simpa [pathSpeed, timeField] using hsqrt
  convert hderiv using 1
  ring_nf

/-- Pointwise parameter derivative of speed along a unit-speed base curve. -/
private theorem pathSpeed_param_hasDerivAt_of_unitSpeed
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {F : Surface M} (hF : SmoothSurface (I := I) F) {s0 : Real}
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0)) (t : Real) :
    HasDerivAt
      (fun s : Real => pathSpeed (I := I) g (timeCurve F s) t)
      (g.inner (F (s0, t))
        (dsTimeField (I := I) cov F (s0, t))
        (timeField I F (s0, t))) s0 := by
  have hnonzero :
      speedSq (I := I) g (timeCurve F s0) t ≠ 0 := by
    simp [hunit t]
  have h :=
    pathSpeed_param_hasDerivAt_of_ne (I := I) g hmc hF
      (s := s0) (t := t) hnonzero
  simpa [pathSpeed, hunit t] using h

/-- Time derivative of the boundary pairing `⟨V,T⟩` along a variation.

The torsion-free mixed-derivative identity supplies `D_t V = D_s T`; the
acceleration input supplies `D_t T = A`. -/
private theorem boundaryPairing_hasDerivAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (htf : RicciFlower.LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} (hF : SmoothSurface (I := I) F) {s0 : Real}
    {A : VectorFieldAlong I (timeCurve F s0)} {t : Real}
    (hA : HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) :
    HasDerivAt
      (fun τ : Real =>
        g.inner (F (s0, τ)) (variationField I F s0 τ)
          (velocityAlong I (timeCurve F s0) τ))
      (g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t) +
        g.inner (F (s0, t)) (variationField I F s0 t) (A t)) t := by
  have hDtV :
      HasPBCovAlongAt (I := I) cov (timeCurve F s0)
        (variationField I F s0) t
        (dsTimeField (I := I) cov F (s0, t)) := by
    have h := SmoothSurface.hasTime_param_eq_dsTime
      (I := I) (cov := cov) htf hF s0 t
    simpa [HasPBTimeCovDerivAt, timeCurve, variationField, paramField,
      surfaceTimeCurve, surfaceParamField] using h
  simpa [timeCurve] using
    inner_hasDerivAt_of_pbCov (I := I) g hmc
      (gamma := timeCurve F s0)
      (S := variationField I F s0)
      (T := velocityAlong I (timeCurve F s0))
      (t := t) hDtV hA

/-- The supplied acceleration field agrees pointwise with the canonical
surface time-acceleration field. -/
private theorem accel_eq_dtTimeField
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} (hF : SmoothSurface (I := I) F) {s0 t : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (hA : HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) :
    A t = dtTimeField (I := I) cov F (s0, t) := by
  have hcanon :
      HasPBCovAccelAt (I := I) cov (timeCurve F s0) t
        (dtTimeField (I := I) cov F (s0, t)) := by
    have h := SmoothSurface.hasTime_time (I := I) (cov := cov) hF s0 t
    simpa [HasPBTimeCovDerivAt, HasPBCovAccelAt, HasPBCovAlongAt,
      timeCurve, surfaceTimeCurve, surfaceTimeField, velocityAlong] using h
  exact HasPBCovDerivAt.unique (I := I) (I' := 𝓘(Real, Real)) hA hcanon

private theorem variation_accel_inner_intervalIntegrable
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (hF : SmoothSurface (I := I) F)
    (hA : ∀ t ∈ Set.uIcc a b,
      HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) :
    IntervalIntegrable
      (fun t : Real =>
        g.inner (F (s0, t)) (variationField I F s0 t) (A t))
      MeasureTheory.volume a b := by
  have hcanon := param_dtTime_inner_intervalIntegrable (I := I) g hcov hF s0 a b
  refine hcanon.congr ?_
  intro t ht
  have htu : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
  have hAeq := accel_eq_dtTimeField (I := I) (cov := cov) hF (hA t htu)
  change
    g.inner (F (s0, t)) (variationField I F s0 t)
        (dtTimeField (I := I) cov F (s0, t)) =
      g.inner (F (s0, t)) (variationField I F s0 t) (A t)
  rw [← hAeq]

private theorem variationLength_hasDerivAt_integral
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {F : Surface M} {s0 a b : Real}
    (hF : SmoothSurface (I := I) F)
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0)) :
    HasDerivAt (fun s => variationLength (I := I) g F a b s)
      (∫ t in a..b,
        g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t)) s0 := by
  classical
  obtain ⟨δ, hδpos, hδtube⟩ :=
    speedSq_pos_tube (I := I) g hF (s0 := s0) (a := a) (b := b) hunit
  let S : Set Real := Set.Icc (s0 - δ) (s0 + δ)
  let Fspeed : Real -> Real -> Real := fun s t =>
    pathSpeed (I := I) g (timeCurve F s) t
  let Fprime : Real -> Real -> Real := fun s t =>
    (pathSpeed (I := I) g (timeCurve F s) t)⁻¹ *
      g.inner (F (s, t))
        (dsTimeField (I := I) cov F (s, t))
        (timeField I F (s, t))
  have hS_nhds : S ∈ 𝓝 s0 := by
    have hleft : s0 - δ < s0 := sub_lt_self s0 hδpos
    have hright : s0 < s0 + δ := lt_add_of_pos_right s0 hδpos
    simpa [S] using Icc_mem_nhds hleft hright
  have hF_meas :
      ∀ᶠ s in 𝓝 s0,
        MeasureTheory.AEStronglyMeasurable
          (Fspeed s) (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    refine Filter.Eventually.of_forall fun s => ?_
    exact (pathSpeed_intervalIntegrable (I := I) g hF s a b).aestronglyMeasurable_restrict_uIoc
  have hF_int : IntervalIntegrable (Fspeed s0) MeasureTheory.volume a b := by
    simpa [Fspeed] using pathSpeed_intervalIntegrable (I := I) g hF s0 a b
  have hFprime_cont0 : ContinuousOn (Fprime s0) (Set.uIcc a b) := by
    refine continuousOn_of_forall_continuousAt fun t _ht => ?_
    have hpos : 0 < speedSq (I := I) g (timeCurve F s0) t := by
      rw [hunit t]
      norm_num
    have hp := speedParamDerivIntegrand_continuousAt_of_pos
      (I := I) g hcov hF (s := s0) (t := t) hpos
    have hline : ContinuousAt (fun τ : Real => (s0, τ)) t :=
      ContinuousAt.prodMk continuousAt_const continuousAt_id
    simpa [Fprime, timeCurve, timeField, surfaceTimeField, velocityAlong] using
      hp.comp hline
  have hFprime_int0 :
      IntervalIntegrable (Fprime s0) MeasureTheory.volume a b :=
    hFprime_cont0.intervalIntegrable
  have hFprime_meas :
      MeasureTheory.AEStronglyMeasurable
        (Fprime s0) (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    hFprime_int0.aestronglyMeasurable_restrict_uIoc
  let K : Set (Real × Real) := S ×ˢ Set.uIcc a b
  have hK_compact : IsCompact K := by
    simpa [K, S] using (isCompact_Icc.prod (isCompact_uIcc : IsCompact (Set.uIcc a b)))
  have hFprime_contK : ContinuousOn (fun p : Real × Real => Fprime p.1 p.2) K := by
    refine continuousOn_of_forall_continuousAt fun p hp => ?_
    have hpS : p.1 ∈ S := hp.1
    have hpt : p.2 ∈ Set.uIcc a b := hp.2
    have hpos_half :
        (1 / 2 : Real) < speedSq (I := I) g (timeCurve F p.1) p.2 := by
      exact hδtube p.1 (by simpa [S] using hpS) p.2 hpt
    have hpos : 0 < speedSq (I := I) g (timeCurve F p.1) p.2 := by
      linarith
    simpa [Fprime] using
      speedParamDerivIntegrand_continuousAt_of_pos
        (I := I) g hcov hF (s := p.1) (t := p.2) hpos
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hFprime_contK
  have hbound :
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
        ∀ s ∈ S, ‖Fprime s t‖ ≤ (fun _ : Real => C) t := by
    refine Filter.Eventually.of_forall fun t ht s hs => ?_
    exact hC (s, t) ⟨hs, Set.uIoc_subset_uIcc ht⟩
  have hbound_int :
      IntervalIntegrable (fun _ : Real => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hdiff :
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
        ∀ s ∈ S, HasDerivAt (fun σ => Fspeed σ t) (Fprime s t) s := by
    refine Filter.Eventually.of_forall fun t ht s hs => ?_
    have htu : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    have hpos_half :
        (1 / 2 : Real) < speedSq (I := I) g (timeCurve F s) t := by
      exact hδtube s (by simpa [S] using hs) t htu
    have hne : speedSq (I := I) g (timeCurve F s) t ≠ 0 := by
      have hpos : 0 < speedSq (I := I) g (timeCurve F s) t := by linarith
      exact ne_of_gt hpos
    simpa [Fspeed, Fprime, timeField, surfaceTimeField, velocityAlong] using
      pathSpeed_param_hasDerivAt_of_ne (I := I) g hmc hF
        (s := s) (t := t) hne
  have hLeibniz :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := a) (b := b)
      (F := Fspeed) (F' := Fprime) (x₀ := s0) (s := S)
      hS_nhds hF_meas hF_int hFprime_meas hbound hbound_int hdiff
  have hderiv_raw :
      HasDerivAt (fun s => variationLength (I := I) g F a b s)
        (∫ t in a..b, Fprime s0 t) s0 := by
    simpa [variationLength, pathLength, Fspeed] using hLeibniz.2
  have hvalue :
      (∫ t in a..b, Fprime s0 t) =
        ∫ t in a..b,
          g.inner (F (s0, t))
            (dsTimeField (I := I) cov F (s0, t))
            (velocityAlong I (timeCurve F s0) t) := by
    refine intervalIntegral.integral_congr ?_
    intro t _ht
    have hspeed : pathSpeed (I := I) g (timeCurve F s0) t = 1 :=
      pathSpeed_eq_one_of_unitSpeed (I := I) hunit t
    simp [Fprime, hspeed, timeField, velocityAlong]
  rwa [hvalue] at hderiv_raw

/-! ## Boundary and first-variation right hand sides -/

/-- Boundary term `⟨V,U⟩|_a^b` for a variation field `V` and a chosen field `U`
along the base time curve. -/
def lengthBoundaryTerm (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (U : VectorFieldAlong I (timeCurve F s0)) : Real :=
  g.inner (F (s0, b)) (variationField I F s0 b) (U b) -
    g.inner (F (s0, a)) (variationField I F s0 a) (U a)

/-- Interior term `∫ ⟨V,A⟩` for the first variation formula. -/
def lengthInteriorTerm (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (A : VectorFieldAlong I (timeCurve F s0)) : Real :=
  ∫ t in a..b, g.inner (F (s0, t)) (variationField I F s0 t) (A t)

/-- RHS of the full length first-variation formula using `U = T / |T|` and
`A = ∇_T U`. -/
def lengthFirstVariationRHS (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (A : VectorFieldAlong I (timeCurve F s0)) : Real :=
  -lengthInteriorTerm (I := I) g F s0 a b A +
    lengthBoundaryTerm (I := I) g F s0 a b
      (unitTangentAlong (I := I) g (timeCurve F s0))

/-- RHS of the unit-speed length first-variation formula using
`A = ∇_T T`. -/
def unitSpeedLengthFirstVariationRHS
    (g : SmoothRiemannianMetric I M) (F : Surface M)
    (s0 a b : Real) (A : VectorFieldAlong I (timeCurve F s0)) : Real :=
  -lengthInteriorTerm (I := I) g F s0 a b A +
    lengthBoundaryTerm (I := I) g F s0 a b (velocityAlong I (timeCurve F s0))

/-- Full first variation formula, with an explicit field `A = ∇_T(T/|T|)`.
The proof producer is intentionally separate from the formula interface. -/
def HasLengthFirstVariationAtWith
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real)
    (A : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  (∀ t ∈ Set.uIcc a b,
    HasPBCovAlongAt (I := I) cov (timeCurve F s0)
      (unitTangentAlong (I := I) g (timeCurve F s0)) t (A t)) ∧
  HasDerivAt (fun s => variationLength (I := I) g F a b s)
    (lengthFirstVariationRHS (I := I) g F s0 a b A) s0

/-- Existential form of the full first variation formula. -/
def HasLengthFirstVariationAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real) : Prop :=
  ∃ A : VectorFieldAlong I (timeCurve F s0),
    HasLengthFirstVariationAtWith (I := I) g cov F s0 a b A

/-- Unit-speed first variation formula, with an explicit acceleration field
`A = ∇_T T`. -/
def HasUnitSpeedLengthFirstVariationAtWith
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real)
    (A : VectorFieldAlong I (timeCurve F s0)) : Prop :=
  IsUnitSpeed (I := I) g (timeCurve F s0) ∧
  (∀ t ∈ Set.uIcc a b,
    HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) ∧
  HasDerivAt (fun s => variationLength (I := I) g F a b s)
    (unitSpeedLengthFirstVariationRHS (I := I) g F s0 a b A) s0

/-- Existential form of the unit-speed first variation formula. -/
def HasUnitSpeedLengthFirstVariationAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (F : Surface M) (s0 a b : Real) : Prop :=
  ∃ A : VectorFieldAlong I (timeCurve F s0),
    HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A

private theorem firstVariation_unitSpeed_of_length_deriv_integral
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (htf : RicciFlower.LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (hF : SmoothSurface (I := I) F)
    (hA : ∀ t ∈ Set.uIcc a b,
      HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t))
    (hDint : IntervalIntegrable
      (fun t : Real =>
        g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t))
      MeasureTheory.volume a b)
    (hVAint : IntervalIntegrable
      (fun t : Real =>
        g.inner (F (s0, t)) (variationField I F s0 t) (A t))
      MeasureTheory.volume a b)
    (hlen : HasDerivAt (fun s => variationLength (I := I) g F a b s)
      (∫ t in a..b,
        g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t)) s0) :
    HasDerivAt (fun s => variationLength (I := I) g F a b s)
      (unitSpeedLengthFirstVariationRHS (I := I) g F s0 a b A) s0 := by
  let D : Real → Real := fun t =>
    g.inner (F (s0, t))
      (dsTimeField (I := I) cov F (s0, t))
      (velocityAlong I (timeCurve F s0) t)
  let VA : Real → Real := fun t =>
    g.inner (F (s0, t)) (variationField I F s0 t) (A t)
  let B : Real → Real := fun t =>
    g.inner (F (s0, t)) (variationField I F s0 t)
      (velocityAlong I (timeCurve F s0) t)
  have hBderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt B (D t + VA t) t := by
    intro t ht
    simpa [B, D, VA] using
      boundaryPairing_hasDerivAt (I := I) g hmc htf hF (hA t ht)
  have hDVAint : IntervalIntegrable (fun t : Real => D t + VA t)
      MeasureTheory.volume a b := hDint.add hVAint
  have hFTC :
      ∫ t in a..b, (D t + VA t) = B b - B a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hBderiv hDVAint
  have hsplit :
      ∫ t in a..b, (D t + VA t) =
        (∫ t in a..b, D t) + ∫ t in a..b, VA t := by
    simpa using intervalIntegral.integral_add hDint hVAint
  have hsum :
      (∫ t in a..b, D t) + ∫ t in a..b, VA t = B b - B a :=
    hsplit.symm.trans hFTC
  have hD_eq :
      ∫ t in a..b, D t =
        (-∫ t in a..b, VA t) + (B b - B a) := by
    calc
      ∫ t in a..b, D t =
          ((∫ t in a..b, D t) + ∫ t in a..b, VA t) -
            ∫ t in a..b, VA t := by ring
      _ = (B b - B a) - ∫ t in a..b, VA t := by rw [hsum]
      _ = (-∫ t in a..b, VA t) + (B b - B a) := by ring
  have hvalue :
      (∫ t in a..b,
        g.inner (F (s0, t))
          (dsTimeField (I := I) cov F (s0, t))
          (velocityAlong I (timeCurve F s0) t)) =
        unitSpeedLengthFirstVariationRHS (I := I) g F s0 a b A := by
    simpa [unitSpeedLengthFirstVariationRHS, lengthInteriorTerm,
      lengthBoundaryTerm, D, VA, B] using hD_eq
  exact hvalue ▸ hlen

/-- Unit-speed first variation of arc length.

The checked geometric input now includes the pullback metric-compatible product
rule `inner_hasDerivAt_of_pbCov`.  The smoothness of `cov` is needed for the
analytic regularity of the canonical acceleration and compact-tube integrands. -/
theorem firstVariation_unitSpeed
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) cov (1 : WithTop ℕ∞))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (htf : RicciFlower.LeviCivita.IsTorsionFree (I := I) cov)
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (hF : SmoothSurface (I := I) F)
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0))
    (hA : ∀ t ∈ Set.uIcc a b,
      HasPBCovAccelAt (I := I) cov (timeCurve F s0) t (A t)) :
    HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A := by
  refine ⟨hunit, hA, ?_⟩
  have hDint := dsTime_time_inner_intervalIntegrable
    (I := I) g hcov hF s0 a b
  have hVAint := variation_accel_inner_intervalIntegrable
    (I := I) g hcov hF hA
  have hlen := variationLength_hasDerivAt_integral
    (I := I) (a := a) (b := b) g hcov hmc hF hunit
  exact firstVariation_unitSpeed_of_length_deriv_integral
    (I := I) g hmc htf hF hA hDint hVAint hlen

theorem HasLengthFirstVariationAtWith.unitSpeed
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (h : HasLengthFirstVariationAtWith (I := I) g cov F s0 a b A)
    (hunit : IsUnitSpeed (I := I) g (timeCurve F s0)) :
    HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A := by
  rcases h with ⟨hA, hderiv⟩
  refine ⟨hunit, ?_, ?_⟩
  · intro t ht
    simpa [HasPBCovAccelAt, unitTangentAlong_eq_velocityAlong_of_unitSpeed
      (I := I) hunit] using hA t ht
  · simpa [lengthFirstVariationRHS, unitSpeedLengthFirstVariationRHS,
      lengthBoundaryTerm, unitTangentAlong_eq_velocityAlong_of_unitSpeed
      (I := I) hunit] using hderiv

/-! ## Fixed-endpoint formal consequences -/

/-- The endpoint `t` is fixed to first order in the variation parameter near
`s0`. -/
def HasFixedEndpointAt (F : Surface M) (s0 t : Real) : Prop :=
  Filter.EventuallyEq (𝓝 s0) (fun s : Real => F (s, t))
    (fun _s : Real => F (s0, t))

theorem variationField_eq_zero_of_fixedEndpoint
    {F : Surface M} {s0 t : Real}
    (h : HasFixedEndpointAt F s0 t) :
    variationField I F s0 t = 0 := by
  unfold variationField paramCurve HasFixedEndpointAt at *
  have hvel :
      curveVelocity I (fun s : Real => F (s, t)) s0 =
        curveVelocity I (fun _s : Real => F (s0, t)) s0 := by
    unfold curveVelocity
    rw [Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) h]
  rw [hvel]
  exact curveVelocity_const (I := I) (x := F (s0, t)) s0

theorem lengthBoundaryTerm_eq_zero_of_fixedEndpoints
    {g : SmoothRiemannianMetric I M} {F : Surface M}
    {s0 a b : Real} {U : VectorFieldAlong I (timeCurve F s0)}
    (ha : HasFixedEndpointAt F s0 a)
    (hb : HasFixedEndpointAt F s0 b) :
    lengthBoundaryTerm (I := I) g F s0 a b U = 0 := by
  have hVa : variationField I F s0 a = 0 :=
    variationField_eq_zero_of_fixedEndpoint (I := I) ha
  have hVb : variationField I F s0 b = 0 :=
    variationField_eq_zero_of_fixedEndpoint (I := I) hb
  rw [lengthBoundaryTerm, hVa, hVb]
  have hb0 :
      g.inner (F (s0, b)) (0 : TangentSpace I (F (s0, b))) (U b) = 0 := by
    rw [show g.inner (F (s0, b)) (0 : TangentSpace I (F (s0, b))) =
      (0 : TangentSpace I (F (s0, b)) →L[Real] Real) by simp]
    rfl
  have ha0 :
      g.inner (F (s0, a)) (0 : TangentSpace I (F (s0, a))) (U a) = 0 := by
    rw [show g.inner (F (s0, a)) (0 : TangentSpace I (F (s0, a))) =
      (0 : TangentSpace I (F (s0, a)) →L[Real] Real) by simp]
    rfl
  change
    g.inner (F (s0, b)) (0 : TangentSpace I (F (s0, b))) (U b) -
      g.inner (F (s0, a)) (0 : TangentSpace I (F (s0, a))) (U a) = 0
  rw [hb0, ha0]
  ring

theorem HasUnitSpeedLengthFirstVariationAtWith.fixedEndpoints
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (h : HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A)
    (ha : HasFixedEndpointAt F s0 a)
    (hb : HasFixedEndpointAt F s0 b) :
    HasDerivAt (fun s => variationLength (I := I) g F a b s)
      (-lengthInteriorTerm (I := I) g F s0 a b A) s0 := by
  rcases h with ⟨_hunit, _hA, hderiv⟩
  simpa [unitSpeedLengthFirstVariationRHS,
    lengthBoundaryTerm_eq_zero_of_fixedEndpoints (I := I) (g := g)
      (F := F) (U := velocityAlong I (timeCurve F s0)) ha hb] using hderiv

theorem HasUnitSpeedLengthFirstVariationAtWith.fixedEndpoints_geodesic
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {F : Surface M} {s0 a b : Real}
    {A : VectorFieldAlong I (timeCurve F s0)}
    (h : HasUnitSpeedLengthFirstVariationAtWith (I := I) g cov F s0 a b A)
    (ha : HasFixedEndpointAt F s0 a)
    (hb : HasFixedEndpointAt F s0 b)
    (hA0 : ∀ t : Real, A t = 0) :
    HasDerivAt (fun s => variationLength (I := I) g F a b s) 0 s0 := by
  have hfixed :=
    HasUnitSpeedLengthFirstVariationAtWith.fixedEndpoints (I := I)
      (g := g) (cov := cov) (F := F) (s0 := s0) (a := a) (b := b)
      (A := A) h ha hb
  have hint :
      lengthInteriorTerm (I := I) g F s0 a b A = 0 := by
    unfold lengthInteriorTerm
    rw [show (∫ t in a..b,
        g.inner (F (s0, t)) (variationField I F s0 t) (A t)) =
          ∫ _t in a..b, (0 : Real) from ?_]
    · simp
    · apply intervalIntegral.integral_congr
      intro t _ht
      change g.inner (F (s0, t)) (variationField I F s0 t) (A t) = 0
      rw [hA0 t]
      exact map_zero (g.inner (F (s0, t)) (variationField I F s0 t))
  simpa [hint] using hfixed

end Lecture07
end GlobalGeometry
end RicciFlower
