import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Regularized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.First
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Transport.BackwardConnection
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeDifference
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cov_sq_smul
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (V : ∀ tau, TangentSpace I (gamma tau))
    (F : ∀ r, TangentSpace I (squareReparametrization gamma r)) (s : Real)
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I
      gamma (s ^ 2))
    (hV : DifferentiableAt Real
      (chartRepAt (I := I) gamma V (s ^ 2)) (s ^ 2))
    (hF : F =ᶠ[nhds s]
      fun r : Real ↦ (2 * r) • V (r ^ 2)) :
    covDerivAlong (I := I) g (squareReparametrization gamma) F s =
      (2 : Real) • V (s ^ 2) +
        (2 * s) • ((2 * s) •
          covDerivAlong (I := I) g gamma V (s ^ 2)) := by
  let B : ∀ r, TangentSpace I (squareReparametrization gamma r) :=
    fun r ↦ V (r ^ 2)
  have hsqdiff : DifferentiableAt Real (fun r : Real ↦ r ^ 2) s :=
    differentiableAt_id.pow 2
  have hsqderiv : deriv (fun r : Real ↦ r ^ 2) s = 2 * s := by
    rw [deriv_pow_field]
    norm_num
  have hBdiff : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma) B s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) gamma V (s ^ 2) ∘ fun r : Real ↦ r ^ 2) s
    exact DifferentiableAt.comp (f := fun r : Real ↦ r ^ 2) s hV hsqdiff
  have hBcov :
      covDerivAlong (I := I) g (squareReparametrization gamma) B s =
        (2 * s) • covDerivAlong (I := I) g gamma V (s ^ 2) := by
    have hcomp := covDerivAlong_comp (I := I) g gamma V
      (fun r : Real ↦ r ^ 2) s hgamma hV hsqdiff
    rw [hsqderiv] at hcomp
    change covDerivAlong (I := I) g (fun r : Real ↦ gamma (r ^ 2))
      (fun r : Real ↦ V (r ^ 2)) s = _
    exact hcomp
  have hlin := (hasDerivAt_id (x := s)).const_mul (2 : Real)
  have hlinDiff : DifferentiableAt Real (fun r : Real ↦ 2 * r) s := by
    simpa only [id_eq] using hlin.differentiableAt
  have hlinDeriv : deriv (fun r : Real ↦ 2 * r) s = 2 := by
    simpa only [id_eq, mul_one] using hlin.deriv
  rw [covDerivAlong_congr_of_eventuallyEq (I := I) g
    (squareReparametrization gamma) hF]
  have hprod := covDerivAlong_smulFun (I := I) g (squareReparametrization gamma)
    (fun r : Real ↦ 2 * r) B s hlinDiff hBdiff
  rw [hlinDeriv, hBcov] at hprod
  change covDerivAlong (I := I) g (squareReparametrization gamma)
    (fun r : Real ↦ (2 * r) • V (r ^ 2)) s = _
  exact hprod

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lPair_test_field
    (beta : Real → M) (s : Real) (hbeta : ContinuousAt beta s)
    (W0 : TangentSpace I (beta s)) :
    ∃ W : (r : Real) → TangentSpace I (beta r),
      W s = W0 ∧
        DifferentiableAt Real (chartRepAt (I := I) beta W s) s := by
  let x : M := beta s
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let w : E := e.continuousLinearMapAt Real x W0
  let W : (r : Real) → TangentSpace I (beta r) :=
    fun r ↦ tangentConstInChart (I := I) x w (beta r)
  have hxbase : x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E
      (TangentSpace I : M → Type _) x
  have hWs : W s = W0 := by
    change tangentConstInChart (I := I) x
      (e.continuousLinearMapAt Real x W0) x = W0
    exact tangentConstInChart_self_continuousLinearMapAt (I := I) x W0
  have hpre : {r : Real | beta r ∈ e.baseSet} ∈ nhds s :=
    hbeta.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (by simpa only [x] using hxbase))
  have hWrep : chartRepAt (I := I) beta W s =ᶠ[nhds s]
      fun _ : Real ↦ w := by
    filter_upwards [hpre] with r hr
    change e.continuousLinearMapAt Real (beta r)
      (e.symmL Real (beta r) w) = w
    exact e.continuousLinearMapAt_symmL (R := Real) hr w
  refine ⟨W, hWs, ?_⟩
  exact (differentiableAt_const (c := w)).congr_of_eventuallyEq hWrep

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem differentiableAt_chartRepAt_lVelocity
    (gamma : Real → M) (s : Real)
    (hgamma : ContMDiffAt 𝓘(Real, Real) I 2 gamma s) :
    DifferentiableAt Real
      (chartRepAt (I := I) gamma
        (fun r : Real ↦ lVelocity (I := I) gamma r) s) s := by
  change DifferentiableAt Real
    (fun u : Real ↦
      (trivializationAt E (TangentSpace I) (gamma s)).continuousLinearMapAt
        Real (gamma u) (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))) s
  exact DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
    (I := I) gamma s hgamma

noncomputable def lJacobiVelocity
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) : TangentSpace I (gamma tau) :=
  covDerivAlong (I := I) (S.base.metric (T - tau)) gamma Y tau

noncomputable def lJacobiPair
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) (W : TangentSpace I (gamma tau)) : Real :=
  let t := T - tau
  let g := S.base.metric t
  let cov := S.base.connection t
  let X := lVelocity (I := I) gamma tau
  let DY := lJacobiVelocity S T gamma Y tau
  let D2Y := covDerivAlong (I := I) g gamma (lJacobiVelocity S T gamma Y) tau
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 cov (S.ricci t) (gamma tau)
  g.inner (gamma tau) D2Y W +
      S.base.rm04 t (gamma tau) (vec4 (Y tau) X X W) -
    (1 / 2 : Real) *
      hessianSec (I := I) cov (metricCov_smooth (I := I) g)
        (S.scalar t) (scalarSmoothOfSolution (I := I) S t) (gamma tau)
        (vec2 (Y tau) W) +
    (1 / (2 * tau)) * g.inner (gamma tau) DY W +
    2 * S.ricciAt t (gamma tau) (vec2 DY W) -
    dRic (vec3 X (Y tau) W) +
    dRic (vec3 (Y tau) X W) +
    dRic (vec3 W X (Y tau))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lPair_second_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma (r ^ 2))
    (hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2))
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) s)
    (hDY : DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVelocity S T gamma Y)
        (s ^ 2)) (s ^ 2))
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s)
    (W : TangentSpace I (gamma (s ^ 2))) :
    (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2)) W
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (squareReparametrization gamma)
          (fun r : Real ↦
            covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              (squareReparametrization gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) =
      2 * (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
          (lJacobiVelocity S T gamma Y (s ^ 2)) W +
        4 * s ^ 2 * (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (lJacobiVelocity S T gamma Y) (s ^ 2)) W -
        (2 * s) *
          (let N := totalNabla0SFun (𝕜 := Real) (I := I)
              2 (S.base.connection (T - s ^ 2))
                (S.ricci (T - s ^ 2)) (gamma (s ^ 2))
           N (vec3 (lVelocity (I := I) (squareReparametrization gamma) s)
                (Y (s ^ 2)) W) +
           N (vec3 (Y (s ^ 2))
                (lVelocity (I := I) (squareReparametrization gamma) s) W) -
           N (vec3 W (lVelocity (I := I) (squareReparametrization gamma) s)
                (Y (s ^ 2)))) := by
  classical
  let tau : Real := s ^ 2
  let alpha : Real → M := squareReparametrization gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let q := S.base.metric (T - tau)
  let DY : ∀ u, TangentSpace I (gamma u) := lJacobiVelocity S T gamma Y
  let A : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Yb r
  let Z : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) q alpha Yb r
  have hsqdiff (r : Real) : DifferentiableAt Real
      (fun u : Real ↦ u ^ 2) r := differentiableAt_id.pow 2
  have hsqderiv (r : Real) : deriv (fun u : Real ↦ u ^ 2) r = 2 * r := by
    rw [deriv_pow_field]
    norm_num
  have hgamma0 : MDifferentiableAt
      (modelWithCornersSelf Real Real) I gamma tau := by
    simpa only [tau] using hgamma_sq.self_of_nhds
  have hY0 : DifferentiableAt Real
      (chartRepAt (I := I) gamma Y tau) tau := by
    simpa only [tau] using hY_sq.self_of_nhds
  have halpha_ev : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    filter_upwards [hgamma_sq] with r hgamma
    have hsquare : MDifferentiableAt
        (modelWithCornersSelf Real Real) (modelWithCornersSelf Real Real)
        (fun u : Real ↦ u ^ 2) r :=
      mdifferentiableAt_iff_differentiableAt.mpr (hsqdiff r)
    change MDifferentiableAt (modelWithCornersSelf Real Real) I
      (gamma ∘ fun u : Real ↦ u ^ 2) r
    exact hgamma.comp (f := fun u : Real ↦ u ^ 2) r hsquare
  have halpha := halpha_ev.self_of_nhds
  have hYb : DifferentiableAt Real
      (chartRepAt (I := I) alpha Yb s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) gamma Y tau ∘ fun r : Real ↦ r ^ 2) s
    exact DifferentiableAt.comp (f := fun r : Real ↦ r ^ 2) s hY0
      (hsqdiff s)
  have hP_eq : P =ᶠ[nhds s]
      fun r : Real ↦ (2 * r) • DY (r ^ 2) := by
    filter_upwards [hgamma_sq, hY_sq] with r hgamma hYr
    have hcomp := covDerivAlong_comp (I := I)
      (S.base.metric (T - r ^ 2)) gamma Y
      (fun u : Real ↦ u ^ 2) r hgamma hYr (hsqdiff r)
    rw [hsqderiv r] at hcomp
    change (covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
      (fun u : Real ↦ gamma (u ^ 2)) (fun u : Real ↦ Y (u ^ 2)) r : E) = _
    exact congrArg (fun v ↦ (v : E)) hcomp
  let B : ∀ r, TangentSpace I (alpha r) := fun r ↦ DY (r ^ 2)
  have hBdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha B s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) gamma DY tau ∘ fun r : Real ↦ r ^ 2) s
    exact DifferentiableAt.comp (f := fun r : Real ↦ r ^ 2) s
      (by simpa only [DY, tau] using hDY) (hsqdiff s)
  have hlin := (hasDerivAt_id (x := s)).const_mul (2 : Real)
  have hprodDiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ (2 * r) • B r) s) s := by
    rw [chartRepAt_smulFun]
    exact (hlin.smul hBdiff.hasDerivAt).differentiableAt
  have hPdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s := by
    have hPB : P =ᶠ[nhds s] fun r ↦ (2 * r) • B r := by
      filter_upwards [hP_eq] with r hr
      change P r = (2 * r) • DY (r ^ 2)
      exact hr
    exact hprodDiff.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hPB)
  have hPcov :
      covDerivAlong (I := I) q alpha P s =
        (2 : Real) • DY tau +
          (2 * s) • ((2 * s) •
            covDerivAlong (I := I) q gamma DY tau) := by
    change covDerivAlong (I := I) q (squareReparametrization gamma) P s =
      (2 : Real) • DY (s ^ 2) + (2 * s) • ((2 * s) •
        covDerivAlong (I := I) q gamma DY (s ^ 2))
    exact cov_sq_smul (I := I) q gamma DY P s hgamma0
      (by simpa only [DY, tau] using hDY) hP_eq
  have hPZ : P s = Z s := by
    rfl
  obtain ⟨Wb, hWs, hWdiff⟩ :=
    lPair_test_field (I := I) alpha s halpha.continuousAt W
  have hchart : DifferentiableAt Real
      (chartCurve (I := I) (alpha s) alpha) s := by
    change DifferentiableAt Real (extChartAt I (alpha s) ∘ alpha) s
    exact mdifferentiableAt_iff_differentiableAt.mp
      (mdifferentiableAt_iff_target.mp halpha).2
  have hmetricP :=
    metric_compat_hasDerivAt_inner_of_chartCurveDeriv
      (I := I) q alpha P Wb s halpha.continuousAt hchart hPdiff hWdiff
  have hZdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha Z s) s := by
    simpa only [alpha, Z, q, tau, Yb] using hZ
  have hmetricZ :=
    metric_compat_hasDerivAt_inner_of_chartCurveDeriv
      (I := I) q alpha Z Wb s halpha.continuousAt hchart hZdiff hWdiff
  let N := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection (T - tau)) (S.ricci (T - tau)) (alpha s)
  let C : Real := (2 * s) *
    (N (vec3 (A s) (Yb s) (Wb s)) +
      N (vec3 (Yb s) (A s) (Wb s)) -
      N (vec3 (Wb s) (A s) (Yb s)))
  have hconn : HasDerivAt
      (fun r : Real ↦ q.inner (alpha r)
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Yb r) (A r))
        (Wb r)) C s := by
    simpa only [q, tau, C, N, alpha, A, Yb] using
      connBack_along_sq (I := I) S hS T alpha A Yb Wb s ht
        halpha (by simpa only [A, alpha] using hA) hYb hWdiff
  have hscalar :
      (fun r : Real ↦ q.inner (alpha r)
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Yb r) (A r))
        (Wb r)) =ᶠ[nhds s]
      fun r : Real ↦
        q.inner (alpha r) (P r) (Wb r) -
          q.inner (alpha r) (Z r) (Wb r) := by
    filter_upwards [halpha_ev] with r halpha_r
    have hdiff := covAlong_diff (I := I)
      (S.base.metric (T - r ^ 2)) q alpha Yb r halpha_r
    have hdiff' : P r - Z r =
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Yb r) (A r)) := by
      simpa only [P, Z, A, lVelocity] using hdiff
    rw [← hdiff']
    rw [ContinuousLinearMap.map_sub, sub_apply]
  have hmetric := (hmetricP.sub hmetricZ).congr_of_eventuallyEq hscalar
  have huniq := hmetric.unique hconn
  have hD2 :
      q.inner (alpha s) (covDerivAlong (I := I) q alpha Z s) (Wb s) =
        q.inner (alpha s) (covDerivAlong (I := I) q alpha P s) (Wb s) - C := by
    rw [hPZ] at huniq
    linarith
  have hPinner :
      q.inner (alpha s) (covDerivAlong (I := I) q alpha P s) (Wb s) =
        2 * q.inner (alpha s) (DY tau) (Wb s) +
          4 * s ^ 2 * q.inner (alpha s)
            (covDerivAlong (I := I) q gamma DY tau) (Wb s) := by
    rw [q.symm (alpha s)
      (covDerivAlong (I := I) q alpha P s) (Wb s), hPcov]
    let DYs : TangentSpace I (alpha s) := DY tau
    let D2 : TangentSpace I (alpha s) :=
      covDerivAlong (I := I) q gamma DY tau
    have hadd :
        q.inner (alpha s) (Wb s)
            ((2 : Real) • DYs + (2 * s) • ((2 * s) • D2)) =
          q.inner (alpha s) (Wb s) ((2 : Real) • DYs) +
            q.inner (alpha s) (Wb s) ((2 * s) • ((2 * s) • D2)) :=
      (q.inner (alpha s) (Wb s)).map_add _ _
    have htwo :
        q.inner (alpha s) (Wb s) ((2 : Real) • DYs) =
          2 * q.inner (alpha s) DYs (Wb s) := by
      rw [map_smul (q.inner (alpha s) (Wb s)), smul_eq_mul,
        q.symm (alpha s) (Wb s) DYs]
    have hnested :
        q.inner (alpha s) (Wb s) ((2 * s) • ((2 * s) • D2)) =
          (2 * s) * ((2 * s) * q.inner (alpha s) D2 (Wb s)) := by
      rw [map_smul (q.inner (alpha s) (Wb s)), smul_eq_mul]
      rw [map_smul (q.inner (alpha s) (Wb s)), smul_eq_mul,
        q.symm (alpha s) (Wb s) D2]
    change q.inner (alpha s) (Wb s)
      ((2 : Real) • DYs + (2 * s) • ((2 * s) • D2)) = _
    rw [hadd, htwo, hnested]
    dsimp only [DYs, D2]
    ring
  have hsecond :
      q.inner (alpha s) (Wb s)
          (covDerivAlong (I := I) q alpha Z s) =
        2 * q.inner (alpha s) (DY tau) (Wb s) +
          4 * s ^ 2 * q.inner (alpha s)
            (covDerivAlong (I := I) q gamma DY tau) (Wb s) - C := by
    rw [q.symm (alpha s) (Wb s)
      (covDerivAlong (I := I) q alpha Z s), hD2, hPinner]
  rw [← hWs]
  change q.inner (alpha s) (Wb s)
      (covDerivAlong (I := I) q alpha Z s) =
    2 * q.inner (alpha s) (DY tau) (Wb s) +
      4 * s ^ 2 * q.inner (alpha s)
        (covDerivAlong (I := I) q gamma DY tau) (Wb s) - C
  exact hsecond

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lJacobiPair_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (s : Real) (hs : 0 < s) (ht : T - s ^ 2 ∈ D.regular)
    (hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma (r ^ 2))
    (hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2))
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) s)
    (hDY : DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVelocity S T gamma Y)
        (s ^ 2)) (s ^ 2))
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s)
    (W : TangentSpace I (gamma (s ^ 2))) :
    4 * s ^ 2 * lJacobiPair S T gamma Y (s ^ 2) W =
      lRegularizedJacobiPair S T (squareReparametrization gamma)
        (fun r : Real ↦ Y (r ^ 2)) s W := by
  classical
  let tau : Real := s ^ 2
  let alpha : Real → M := squareReparametrization gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let q := S.base.metric (T - tau)
  let X := lVelocity (I := I) gamma tau
  let DY : ∀ u, TangentSpace I (gamma u) := lJacobiVelocity S T gamma Y
  let N := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection (T - tau)) (S.ricci (T - tau)) (gamma tau)
  let Rm := S.base.rm04 (T - tau) (gamma tau)
  let Ric := S.ricciAt (T - tau) (gamma tau)
  let c : Real := 2 * s
  have hgamma0 : MDifferentiableAt
      (modelWithCornersSelf Real Real) I gamma tau := by
    simpa only [tau] using hgamma_sq.self_of_nhds
  have hY0 : DifferentiableAt Real
      (chartRepAt (I := I) gamma Y tau) tau := by
    simpa only [tau] using hY_sq.self_of_nhds
  have hsecond := lPair_second_eq (I := I) S hS T gamma Y s ht
    hgamma_sq hY_sq hA hDY hZ W
  let Dreg : Real :=
    (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s) W
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        (squareReparametrization gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma) (fun u : Real ↦ Y (u ^ 2)) r) s)
  let D2 : Real := q.inner (gamma tau)
    (covDerivAlong (I := I) q gamma DY tau) W
  let U : Real := q.inner (gamma tau) (DY tau) W
  let Hess : Real :=
    hessianSec (I := I) (S.base.connection (T - tau))
      (metricCov_smooth (I := I) q)
      (S.scalar (T - tau)) (scalarSmoothOfSolution (I := I) S (T - tau))
      (gamma tau) (vec2 (Y tau) W)
  let R : Real := Rm (vec4 (Y tau) X X W)
  let RicD : Real := Ric (vec2 (DY tau) W)
  let N0 : Real := N (vec3 X (Y tau) W)
  let N1 : Real := N (vec3 (Y tau) X W)
  let N2 : Real := N (vec3 W X (Y tau))
  let Rreg : Real := Rm
    (vec4 (Y tau) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s) W)
  let Ricreg : Real := Ric
    (vec2 (covDerivAlong (I := I) q alpha Yb s) W)
  let Nreg0 : Real := N
    (vec3 (lVelocity (I := I) alpha s) (Y tau) W)
  let Nreg1 : Real := N
    (vec3 (Y tau) (lVelocity (I := I) alpha s) W)
  let Nreg2 : Real := N
    (vec3 W (lVelocity (I := I) alpha s) (Y tau))
  change Dreg = 2 * U + 4 * s ^ 2 * D2 -
    (2 * s) * (Nreg0 + Nreg1 - Nreg2) at hsecond
  have hAs : lVelocity (I := I) alpha s = c • X := by
    simpa only [alpha, c, X, tau] using
      lVelocity_squareReparametrization_of_pos (I := I) gamma s hs
  have hZs :
      covDerivAlong (I := I) q alpha Yb s = c • DY tau := by
    have hcomp := covDerivAlong_comp (I := I) q gamma Y
      (fun r : Real ↦ r ^ 2) s hgamma0 hY0
        (differentiableAt_id.pow 2)
    have hsqderiv : deriv (fun r : Real ↦ r ^ 2) s = c := by
      rw [deriv_pow_field]
      simp only [c]
      norm_num
    rw [hsqderiv] at hcomp
    change covDerivAlong (I := I) q (fun r : Real ↦ gamma (r ^ 2))
      (fun r : Real ↦ Y (r ^ 2)) s = _
    exact hcomp
  have slot_scale : ∀ {n : Nat} {x : M}
      (L : Tensor0SSpace n I x) (v : Fin n → TangentSpace I x)
      (i : Fin n) (a : Real) (z : TangentSpace I x),
      L (Function.update v i (a • z)) =
        a * L (Function.update v i z) := by
    intro n x L v i a z
    simpa only [smul_eq_mul] using L.map_update_smul v i a z
  have hN0 : Nreg0 = c * N0 := by
    change N (vec3 (lVelocity (I := I) alpha s) (Y tau) W) =
      c * N (vec3 X (Y tau) W)
    rw [hAs]
    have h := slot_scale N (vec3 X (Y tau) W) (0 : Fin 3) c X
    have hl : Function.update (vec3 X (Y tau) W) (0 : Fin 3) (c • X) =
        vec3 (c • X) (Y tau) W := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 X (Y tau) W) (0 : Fin 3) X =
        vec3 X (Y tau) W := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr] using h
  have hN1 : Nreg1 = c * N1 := by
    change N (vec3 (Y tau) (lVelocity (I := I) alpha s) W) =
      c * N (vec3 (Y tau) X W)
    rw [hAs]
    have h := slot_scale N (vec3 (Y tau) X W) (1 : Fin 3) c X
    have hl : Function.update (vec3 (Y tau) X W) (1 : Fin 3) (c • X) =
        vec3 (Y tau) (c • X) W := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 (Y tau) X W) (1 : Fin 3) X =
        vec3 (Y tau) X W := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr] using h
  have hN2 : Nreg2 = c * N2 := by
    change N (vec3 W (lVelocity (I := I) alpha s) (Y tau)) =
      c * N (vec3 W X (Y tau))
    rw [hAs]
    have h := slot_scale N (vec3 W X (Y tau)) (1 : Fin 3) c X
    have hl : Function.update (vec3 W X (Y tau)) (1 : Fin 3) (c • X) =
        vec3 W (c • X) (Y tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 W X (Y tau)) (1 : Fin 3) X =
        vec3 W X (Y tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr] using h
  have hRic : Ricreg = c * RicD := by
    change Ric (vec2 (covDerivAlong (I := I) q alpha Yb s) W) =
      c * Ric (vec2 (DY tau) W)
    rw [hZs]
    have h := slot_scale Ric (vec2 (DY tau) W) (0 : Fin 2) c (DY tau)
    have hl : Function.update (vec2 (DY tau) W) (0 : Fin 2) (c • DY tau) =
        vec2 (c • DY tau) W := by
      funext i
      fin_cases i <;> simp [vec2]
    have hr : Function.update (vec2 (DY tau) W) (0 : Fin 2) (DY tau) =
        vec2 (DY tau) W := by
      funext i
      fin_cases i <;> simp [vec2]
    simpa only [hl, hr] using h
  have hRm1 :
      Rm (vec4 (Y tau) (c • X) X W) =
        c * Rm (vec4 (Y tau) X X W) := by
    have h := slot_scale Rm (vec4 (Y tau) X X W) (1 : Fin 4) c X
    have hl : Function.update (vec4 (Y tau) X X W) (1 : Fin 4) (c • X) =
        vec4 (Y tau) (c • X) X W := by
      funext i
      fin_cases i <;> simp [vec4]
    have hr : Function.update (vec4 (Y tau) X X W) (1 : Fin 4) X =
        vec4 (Y tau) X X W := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [hl, hr] using h
  have hRm2 :
      Rm (vec4 (Y tau) (c • X) (c • X) W) =
        c * Rm (vec4 (Y tau) (c • X) X W) := by
    have h := slot_scale Rm (vec4 (Y tau) (c • X) X W)
      (2 : Fin 4) c X
    have hl : Function.update (vec4 (Y tau) (c • X) X W)
        (2 : Fin 4) (c • X) = vec4 (Y tau) (c • X) (c • X) W := by
      funext i
      fin_cases i <;> simp [vec4]
    have hr : Function.update (vec4 (Y tau) (c • X) X W)
        (2 : Fin 4) X = vec4 (Y tau) (c • X) X W := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [hl, hr] using h
  have hRm : Rreg = 4 * s ^ 2 * R := by
    change Rm (vec4 (Y tau) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s) W) =
        4 * s ^ 2 * Rm (vec4 (Y tau) X X W)
    rw [hAs, hRm2, hRm1]
    simp only [c]
    ring
  simp only [lJacobiPair, lRegularizedJacobiPair]
  change 4 * s ^ 2 *
      (D2 + R - (1 / 2 : Real) * Hess +
        (1 / (2 * s ^ 2)) * U + 2 * RicD - N0 + N1 + N2) =
    Dreg + Rreg - 2 * s ^ 2 * Hess + 4 * s * Nreg1 + 4 * s * Ricreg
  rw [hsecond]
  rw [hRm, hN0, hN1, hN2, hRic]
  simp only [c]
  field_simp [ne_of_gt hs]
  ring

def HasLJacobiAt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) : Prop :=
  MDifferentiableAt (modelWithCornersSelf Real Real) I gamma tau ∧
    DifferentiableAt Real (chartRepAt (I := I) gamma Y tau) tau ∧
    DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVelocity S T gamma Y) tau) tau ∧
    ∀ W : TangentSpace I (gamma tau), lJacobiPair S T gamma Y tau W = 0

def IsLJacobi
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (J : Set Real) : Prop :=
  ∀ tau ∈ J, HasLJacobiAt S T gamma Y tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem differentiableAt_chartRepAt_lJacobiVelocity_of_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (s : Real) (hs : 0 < s) (ht : T - s ^ 2 ∈ D.regular)
    (hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma (r ^ 2))
    (hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2))
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) s)
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s) :
    DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVelocity S T gamma Y)
        (s ^ 2)) (s ^ 2) := by
  let tau : Real := s ^ 2
  let alpha : Real → M := squareReparametrization gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let q := S.base.metric (T - tau)
  let DY : ∀ u, TangentSpace I (gamma u) := lJacobiVelocity S T gamma Y
  let A : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lVelocity (I := I) alpha r
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Yb r
  let Z : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) q alpha Yb r
  let C : ∀ r, TangentSpace I (alpha r) := fun r ↦
    CovariantDerivative.difference
      (metricCov (I := I) (S.base.metric (T - r ^ 2)))
      (metricCov (I := I) q) (alpha r) (Yb r) (A r)
  have hsqdiff (r : Real) : DifferentiableAt Real
      (fun u : Real ↦ u ^ 2) r := differentiableAt_id.pow 2
  have hsqderiv (r : Real) : deriv (fun u : Real ↦ u ^ 2) r = 2 * r := by
    rw [deriv_pow_field]
    norm_num
  have halpha_ev : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    filter_upwards [hgamma_sq] with r hgamma
    have hsquare : MDifferentiableAt
        (modelWithCornersSelf Real Real) (modelWithCornersSelf Real Real)
        (fun u : Real ↦ u ^ 2) r :=
      mdifferentiableAt_iff_differentiableAt.mpr (hsqdiff r)
    change MDifferentiableAt (modelWithCornersSelf Real Real) I
      (gamma ∘ fun u : Real ↦ u ^ 2) r
    exact hgamma.comp (f := fun u : Real ↦ u ^ 2) r hsquare
  have halpha := halpha_ev.self_of_nhds
  have hY0 : DifferentiableAt Real
      (chartRepAt (I := I) gamma Y tau) tau := by
    simpa only [tau] using hY_sq.self_of_nhds
  have hYb : DifferentiableAt Real
      (chartRepAt (I := I) alpha Yb s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) gamma Y tau ∘ fun r : Real ↦ r ^ 2) s
    exact DifferentiableAt.comp (f := fun r : Real ↦ r ^ 2) s hY0
      (hsqdiff s)
  have hC : DifferentiableAt Real
      (chartRepAt (I := I) alpha C s) s := by
    simpa only [C, q, tau, alpha, Yb, A] using
      connBack_vec_sq (I := I) S hS T alpha A Yb s ht halpha
        (by simpa only [A, alpha] using hA) hYb
  have hPZ : P =ᶠ[nhds s] fun r ↦ Z r + C r := by
    filter_upwards [halpha_ev] with r halpha_r
    have hdiff := covAlong_diff (I := I)
      (S.base.metric (T - r ^ 2)) q alpha Yb r halpha_r
    have hdiff' : P r - Z r = C r := by
      simpa only [P, Z, C, A, lVelocity] using hdiff
    exact (sub_eq_iff_eq_add.mp hdiff').trans (add_comm _ _)
  have hPdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s := by
    have hsum : DifferentiableAt Real
        (chartRepAt (I := I) alpha (fun r ↦ Z r + C r) s) s := by
      rw [chartRepAt_add]
      have hZ' : DifferentiableAt Real
          (chartRepAt (I := I) alpha Z s) s := by
        simpa only [Z, q, tau, alpha, Yb] using hZ
      exact hZ'.add hC
    exact hsum.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hPZ)
  have hPB : P =ᶠ[nhds s]
      fun r : Real ↦ (2 * r) • DY (r ^ 2) := by
    filter_upwards [hgamma_sq, hY_sq] with r hgamma hYr
    have hcomp := covDerivAlong_comp (I := I)
      (S.base.metric (T - r ^ 2)) gamma Y
      (fun u : Real ↦ u ^ 2) r hgamma hYr (hsqdiff r)
    rw [hsqderiv r] at hcomp
    change (covDerivAlong (I := I) (S.base.metric (T - r ^ 2))
      (fun u : Real ↦ gamma (u ^ 2)) (fun u : Real ↦ Y (u ^ 2)) r : E) = _
    exact congrArg (fun v ↦ (v : E)) hcomp
  let B : ∀ r, TangentSpace I (alpha r) := fun r ↦ DY (r ^ 2)
  have hlin : DifferentiableAt Real (fun r : Real ↦ 2 * r) s :=
    (differentiableAt_const (c := (2 : Real))).mul differentiableAt_id
  have hlin0 : 2 * s ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hs)
  have hinv : DifferentiableAt Real (fun r : Real ↦ (2 * r)⁻¹) s :=
    hlin.inv hlin0
  have hscaled : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ (2 * r)⁻¹ • P r) s) s := by
    rw [chartRepAt_smulFun]
    exact hinv.smul hPdiff
  have hB_eq : B =ᶠ[nhds s] fun r ↦ (2 * r)⁻¹ • P r := by
    filter_upwards [hPB, Ioi_mem_nhds hs] with r hPr hr
    change DY (r ^ 2) = (2 * r)⁻¹ • P r
    rw [hPr]
    exact (inv_smul_smul₀
      (mul_ne_zero (by norm_num) (ne_of_gt hr)) (DY (r ^ 2))).symm
  have hBdiff : DifferentiableAt Real
      (chartRepAt (I := I) alpha B s) s :=
    hscaled.congr_of_eventuallyEq
      (chartRepAt_eventuallyEq_of_eventuallyEq (I := I) alpha hB_eq)
  have htau_pos : 0 < tau := by
    simpa only [tau] using sq_pos_of_pos hs
  have hsqrt : DifferentiableAt Real Real.sqrt tau :=
    differentiableAt_id.sqrt htau_pos.ne'
  have hsqrt_eq : Real.sqrt tau = s := by
    simpa only [tau] using Real.sqrt_sq hs.le
  have hBroot : DifferentiableAt Real
      (chartRepAt (I := I) alpha B s) (Real.sqrt tau) := by
    simpa only [hsqrt_eq] using hBdiff
  have hcomp := hBroot.comp tau hsqrt
  have hroot_eq :
      (chartRepAt (I := I) alpha B s ∘ Real.sqrt) =ᶠ[nhds tau]
        chartRepAt (I := I) gamma DY tau := by
    filter_upwards [Ioi_mem_nhds htau_pos] with u hu
    change
      (trivializationAt E (TangentSpace I) (gamma (s ^ 2))).continuousLinearMapAt
          Real (gamma (Real.sqrt u ^ 2)) (DY (Real.sqrt u ^ 2)) =
        (trivializationAt E (TangentSpace I) (gamma (s ^ 2))).continuousLinearMapAt
          Real (gamma u) (DY u)
    rw [Real.sq_sqrt hu.le]
  simpa only [DY, tau, Function.comp_def] using
    hcomp.congr_of_eventuallyEq hroot_eq.symm

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hasLJacobiAt_of_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (s : Real) (hs : 0 < s) (ht : T - s ^ 2 ∈ D.regular)
    (hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma (r ^ 2))
    (hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2))
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) s)
    (hreg : HasLRegularizedJacobiAt S T (squareReparametrization gamma)
      (fun r : Real ↦ Y (r ^ 2)) s) :
    HasLJacobiAt S T gamma Y (s ^ 2) := by
  rcases hreg with ⟨_, _, hZ, hzero⟩
  have hDY := differentiableAt_chartRepAt_lJacobiVelocity_of_squareReparametrization (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA hZ
  refine ⟨hgamma_sq.self_of_nhds, hY_sq.self_of_nhds, hDY, ?_⟩
  intro W
  have hscale := lJacobiPair_squareReparametrization (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA hDY hZ W
  rw [hzero W] at hscale
  have hfac : 4 * s ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hs))
  exact (mul_eq_zero.mp hscale).resolve_left hfac

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
