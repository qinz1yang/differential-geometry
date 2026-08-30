import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.First
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.ConnectionBackward
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeDifference
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve

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
    (F : ∀ r, TangentSpace I (sqReparam gamma r)) (s : Real)
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I
      gamma (s ^ 2))
    (hV : DifferentiableAt Real
      (chartRepAt (I := I) gamma V (s ^ 2)) (s ^ 2))
    (hF : F =ᶠ[nhds s]
      fun r : Real ↦ (2 * r) • V (r ^ 2)) :
    covDerivAlong (I := I) g (sqReparam gamma) F s =
      (2 : Real) • V (s ^ 2) +
        (2 * s) • ((2 * s) •
          covDerivAlong (I := I) g gamma V (s ^ 2)) := by
  let B : ∀ r, TangentSpace I (sqReparam gamma r) :=
    fun r ↦ V (r ^ 2)
  have hsqdiff : DifferentiableAt Real (fun r : Real ↦ r ^ 2) s :=
    differentiableAt_id.pow 2
  have hsqderiv : deriv (fun r : Real ↦ r ^ 2) s = 2 * s := by
    rw [deriv_pow_field]
    norm_num
  have hBdiff : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma) B s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) gamma V (s ^ 2) ∘ fun r : Real ↦ r ^ 2) s
    exact DifferentiableAt.comp (f := fun r : Real ↦ r ^ 2) s hV hsqdiff
  have hBcov :
      covDerivAlong (I := I) g (sqReparam gamma) B s =
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
    (sqReparam gamma) hF]
  have hprod := covDerivAlong_smulFun (I := I) g (sqReparam gamma)
    (fun r : Real ↦ 2 * r) B s hlinDiff hBdiff
  rw [hlinDeriv, hBcov] at hprod
  change covDerivAlong (I := I) g (sqReparam gamma)
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
private theorem lVelocity_chartRepAt_diff
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

noncomputable def lJacobiVel
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
  let DY := lJacobiVel S T gamma Y tau
  let D2Y := covDerivAlong (I := I) g gamma (lJacobiVel S T gamma Y) tau
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 cov (S.ricci t) (gamma tau)
  g.inner (gamma tau) D2Y W +
      S.base.rm04 t (gamma tau) (vec4 (Y tau) X X W) -
    (1 / 2 : Real) *
      hessianSec (I := I) cov (metricCov_smooth (I := I) g)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t) (gamma tau)
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
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦ lVelocity (I := I) (sqReparam gamma) r) s) s)
    (hDY : DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVel S T gamma Y)
        (s ^ 2)) (s ^ 2))
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (sqReparam gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s)
    (W : TangentSpace I (gamma (s ^ 2))) :
    (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2)) W
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (sqReparam gamma)
          (fun r : Real ↦
            covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              (sqReparam gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) =
      2 * (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
          (lJacobiVel S T gamma Y (s ^ 2)) W +
        4 * s ^ 2 * (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (lJacobiVel S T gamma Y) (s ^ 2)) W -
        (2 * s) *
          (let N := totalNabla0SFun (𝕜 := Real) (I := I)
              2 (S.base.connection (T - s ^ 2))
                (S.ricci (T - s ^ 2)) (gamma (s ^ 2))
           N (vec3 (lVelocity (I := I) (sqReparam gamma) s)
                (Y (s ^ 2)) W) +
           N (vec3 (Y (s ^ 2))
                (lVelocity (I := I) (sqReparam gamma) s) W) -
           N (vec3 W (lVelocity (I := I) (sqReparam gamma) s)
                (Y (s ^ 2)))) := by
  classical
  let tau : Real := s ^ 2
  let alpha : Real → M := sqReparam gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let q := S.base.metric (T - tau)
  let DY : ∀ u, TangentSpace I (gamma u) := lJacobiVel S T gamma Y
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
    change covDerivAlong (I := I) q (sqReparam gamma) P s =
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
theorem lJacobiPair_sq
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
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦ lVelocity (I := I) (sqReparam gamma) r) s) s)
    (hDY : DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVel S T gamma Y)
        (s ^ 2)) (s ^ 2))
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (sqReparam gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s)
    (W : TangentSpace I (gamma (s ^ 2))) :
    4 * s ^ 2 * lJacobiPair S T gamma Y (s ^ 2) W =
      lRegJacobiPair S T (sqReparam gamma)
        (fun r : Real ↦ Y (r ^ 2)) s W := by
  classical
  let tau : Real := s ^ 2
  let alpha : Real → M := sqReparam gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let q := S.base.metric (T - tau)
  let X := lVelocity (I := I) gamma tau
  let DY : ∀ u, TangentSpace I (gamma u) := lJacobiVel S T gamma Y
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
    (S.base.metric (T - s ^ 2)).inner (sqReparam gamma s) W
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        (sqReparam gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (sqReparam gamma) (fun u : Real ↦ Y (u ^ 2)) r) s)
  let D2 : Real := q.inner (gamma tau)
    (covDerivAlong (I := I) q gamma DY tau) W
  let U : Real := q.inner (gamma tau) (DY tau) W
  let Hess : Real :=
    hessianSec (I := I) (S.base.connection (T - tau))
      (metricCov_smooth (I := I) q)
      (S.scalar (T - tau)) (scalarSmoothOfSol (I := I) S (T - tau))
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
      lVelocity_sq_pos (I := I) gamma s hs
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
  simp only [lJacobiPair, lRegJacobiPair]
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
      (chartRepAt (I := I) gamma (lJacobiVel S T gamma Y) tau) tau ∧
    ∀ W : TangentSpace I (gamma tau), lJacobiPair S T gamma Y tau W = 0

def IsLJacobi
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (J : Set Real) : Prop :=
  ∀ tau ∈ J, HasLJacobiAt S T gamma Y tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lReg_jacobi_on
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    {alpha beta : Real → M}
    (Y : ∀ r, TangentSpace I (alpha r))
    (Y' : ∀ r, TangentSpace I (beta r))
    (s : Real) (U : Set Real) (hU : IsOpen U) (hsU : s ∈ U)
    (hcurve : Set.EqOn alpha beta U)
    (hfield : ∀ r ∈ U, (Y r : E) = (Y' r : E))
    (h : HasLRegJacobiAt S T alpha Y s) :
    HasLRegJacobiAt S T beta Y' s := by
  let g := S.base.metric (T - s ^ 2)
  have hcurveEv : alpha =ᶠ[𝓝 s] beta := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    exact hcurve hr
  have hfieldEv : ∀ᶠ r in 𝓝 s, (Y r : E) = (Y' r : E) := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    exact hfield r hr
  have hD1Ev : ∀ᶠ r in 𝓝 s,
      (covDerivAlong (I := I) g alpha Y r : E) =
        (covDerivAlong (I := I) g beta Y' r : E) := by
    filter_upwards [hU.mem_nhds hsU] with r hr
    apply DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) g Y Y'
    · filter_upwards [hU.mem_nhds hr] with q hq
      exact hcurve hq
    · filter_upwards [hU.mem_nhds hr] with q hq
      exact hfield q hq
  rcases h with ⟨halpha, hYdiff, hDYdiff, hzero⟩
  refine ⟨halpha.congr_of_eventuallyEq hcurveEv.symm, ?_, ?_, ?_⟩
  · have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
      (I := I) Y Y' hcurveEv hfieldEv
    exact hrep.differentiableAt_iff.mp hYdiff
  · have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
      (I := I) (fun r ↦ covDerivAlong (I := I) g alpha Y r)
        (fun r ↦ covDerivAlong (I := I) g beta Y' r) hcurveEv hD1Ev
    exact hrep.differentiableAt_iff.mp hDYdiff
  · intro W
    have hcurve0 : alpha s = beta s := hcurve hsU
    have hfield0 : (Y s : E) = (Y' s : E) := hfield s hsU
    have hvel0 : (lVelocity (I := I) alpha s : E) =
        (lVelocity (I := I) beta s : E) := by
      exact congrArg (fun L : Real →L[Real] E ↦ L (1 : Real))
        (Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)
          hcurveEv)
    have hD10 := hD1Ev.self_of_nhds
    have hD2 :
        (covDerivAlong (I := I) g alpha
          (fun r ↦ covDerivAlong (I := I) g alpha Y r) s : E) =
        (covDerivAlong (I := I) g beta
          (fun r ↦ covDerivAlong (I := I) g beta Y' r) s : E) := by
      exact DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
        (I := I) g
        (fun r ↦ covDerivAlong (I := I) g alpha Y r)
        (fun r ↦ covDerivAlong (I := I) g beta Y' r) hcurveEv hD1Ev
    unfold lRegJacobiPair at hzero ⊢
    dsimp only at hzero ⊢
    rw [hcurve0] at hzero
    have hzero' := hzero W
    rw [← hfield0, ← hvel0, ← hD10, ← hD2]
    exact hzero'

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lJacobiVel_sq_diff
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
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦ lVelocity (I := I) (sqReparam gamma) r) s) s)
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (sqReparam gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s) :
    DifferentiableAt Real
      (chartRepAt (I := I) gamma (lJacobiVel S T gamma Y)
        (s ^ 2)) (s ^ 2) := by
  let tau : Real := s ^ 2
  let alpha : Real → M := sqReparam gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let q := S.base.metric (T - tau)
  let DY : ∀ u, TangentSpace I (gamma u) := lJacobiVel S T gamma Y
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
theorem lJacobi_of_sq
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
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦ lVelocity (I := I) (sqReparam gamma) r) s) s)
    (hreg : HasLRegJacobiAt S T (sqReparam gamma)
      (fun r : Real ↦ Y (r ^ 2)) s) :
    HasLJacobiAt S T gamma Y (s ^ 2) := by
  rcases hreg with ⟨_, _, hZ, hzero⟩
  have hDY := lJacobiVel_sq_diff (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA hZ
  refine ⟨hgamma_sq.self_of_nhds, hY_sq.self_of_nhds, hDY, ?_⟩
  intro W
  have hscale := lJacobiPair_sq (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA hDY hZ W
  rw [hzero W] at hscale
  have hfac : 4 * s ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hs))
  exact (mul_eq_zero.mp hscale).resolve_left hfac

omit [InnerProductSpace Real E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lExp_jacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real)
    (hpos : (Z, tau) ∈ lExpPosDom S T x) :
    HasLJacobiAt S T
      (fun q ↦ lExp S T x Z q)
      (fun q ↦ mfderiv 𝓘(Real, E) I
        (fun W : E ↦ lExp S T x W q) Z V)
      tau := by
  let s : Real := Real.sqrt tau
  let alpha : Real → M := lRegCurve S T x Z
  let J : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lRegJacobiField S T x Z V r
  let gamma : Real → M := fun q ↦ lExp S T x Z q
  let Y : ∀ q, TangentSpace I (gamma q) := fun q ↦
    mfderiv 𝓘(Real, E) I (fun W : E ↦ lExp S T x W q) Z V
  change 0 < tau ∧ Real.sqrt tau ∈ lRegDomain S T x Z at hpos
  rcases hpos with ⟨htau, hsdom⟩
  have hs : 0 < s := by
    simpa only [s] using Real.sqrt_pos.2 htau
  have hsq : s ^ 2 = tau := by
    simpa only [s] using Real.sq_sqrt htau.le
  have ht : T - s ^ 2 ∈ D.regular := by
    rcases hsdom with ⟨beta, K, _hKopen, _hKconn, _h0K, hsK, hbeta⟩
    exact (hbeta.2.2 s hsK).1
  have hregAll : IsLRegJacobi S T alpha J (lRegDomain S T x Z) := by
    simpa only [alpha, J] using
      lRegCurve_jacobi (I := I) S hS T x Z V
        (lRegDomain S T x Z) (fun _ hr ↦ hr)
  have hreg : HasLRegJacobiAt S T alpha J s := hregAll s hsdom
  have hdom : ∀ᶠ r in nhds s, r ∈ lRegDomain S T x Z :=
    (lRegDomain_isOpen S T x Z).mem_nhds hsdom
  have hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma (r ^ 2) := by
    filter_upwards [hdom, Ioi_mem_nhds hs] with r hrdom hr
    have hrreg := hregAll r hrdom
    have hsqrt : DifferentiableAt Real Real.sqrt (r ^ 2) :=
      differentiableAt_id.sqrt (sq_pos_of_pos hr).ne'
    have hsqrtMD : MDifferentiableAt
        (modelWithCornersSelf Real Real) (modelWithCornersSelf Real Real)
        Real.sqrt (r ^ 2) :=
      mdifferentiableAt_iff_differentiableAt.mpr hsqrt
    have hroot : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
    have halpha : MDifferentiableAt
        (modelWithCornersSelf Real Real) I alpha (Real.sqrt (r ^ 2)) := by
      simpa only [hroot] using hrreg.1
    have hcomp := halpha.comp (f := Real.sqrt) (r ^ 2) hsqrtMD
    simpa only [gamma, alpha, lExp, Function.comp_def] using hcomp
  have hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real (chartRepAt (I := I) gamma Y (r ^ 2))
        (r ^ 2) := by
    filter_upwards [hdom, Ioi_mem_nhds hs] with r hrdom hr
    have hrreg := hregAll r hrdom
    have hsqrt : DifferentiableAt Real Real.sqrt (r ^ 2) :=
      differentiableAt_id.sqrt (sq_pos_of_pos hr).ne'
    have hroot : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
    have hJ : DifferentiableAt Real
        (chartRepAt (I := I) alpha J r) (Real.sqrt (r ^ 2)) := by
      simpa only [hroot] using hrreg.2.1
    have hcomp := hJ.comp (r ^ 2) hsqrt
    have heq : chartRepAt (I := I) gamma Y (r ^ 2) =
        chartRepAt (I := I) alpha J r ∘ Real.sqrt := by
      funext q
      have hbase : gamma (r ^ 2) = alpha r := by
        simp only [gamma, alpha, lExp, hroot]
      have hcurve : gamma q = alpha (Real.sqrt q) := by
        rfl
      have hYq : Y q = J (Real.sqrt q) := by
        simpa only [Y, J] using
          lExpJacobi_eq (I := I) S T x Z V q
      simp only [chartRepAt_apply, Function.comp_def]
      rw [hbase, hcurve, hYq]
    rw [heq]
    exact hcomp
  let delta : Real → M := sqReparam gamma
  have halphaInf : ContMDiffAt (modelWithCornersSelf Real Real) I ∞ alpha s := by
    have hparam : ContMDiffAt (modelWithCornersSelf Real Real)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun r : Real ↦ (((Z : E), r) : E × Real)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hcomp := (lRegCurve_smooth (I := I) (M := M) S hS T x hsdom).comp
      s hparam
    simpa only [alpha, Function.comp_def] using hcomp
  have hdelta_eq : delta =ᶠ[nhds s] alpha := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    simp only [delta, gamma, alpha, sqReparam, lExp]
    rw [Real.sqrt_sq hr.le]
  have hdeltaInf : ContMDiffAt
      (modelWithCornersSelf Real Real) I ∞ delta s :=
    halphaInf.congr_of_eventuallyEq hdelta_eq
  have hdelta2 : ContMDiffAt
      (modelWithCornersSelf Real Real) I 2 delta s :=
    hdeltaInf.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) delta
        (fun r : Real ↦ lVelocity (I := I) delta r) s) s := by
    exact lVelocity_chartRepAt_diff (I := I) delta s hdelta2
  have hcurve : Set.EqOn alpha delta (Set.Ioi 0) := by
    intro r hr
    simp only [alpha, delta, gamma, sqReparam, lExp]
    rw [Real.sqrt_sq hr.le]
  have hfield : ∀ r ∈ Set.Ioi (0 : Real),
      (J r : E) = (Y (r ^ 2) : E) := by
    intro r hr
    simp only [J, Y, lExpJacobi_eq]
    rw [Real.sqrt_sq hr.le]
  have hregSq : HasLRegJacobiAt S T delta
      (fun r : Real ↦ Y (r ^ 2)) s :=
    lReg_jacobi_on (I := I) S T J (fun r : Real ↦ Y (r ^ 2)) s
      (Set.Ioi 0) isOpen_Ioi hs hcurve hfield hreg
  have hout := lJacobi_of_sq (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq (by simpa only [delta] using hA)
    (by simpa only [delta] using hregSq)
  simpa only [gamma, Y, hsq] using hout

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lEuler_var_full
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (s : Real) (hs : 0 < s) (ht : T - s ^ 2 ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u (s ^ 2)))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u (s ^ 2)) W 0) 0) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) (s ^ 2) (W u))
      (lJacobiPair S T (f 0)
          (fun tau ↦ lVelocity (I := I) (fun u ↦ f u tau) 0)
          (s ^ 2) (W 0) +
        lEulerPair S T (f 0) (s ^ 2)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u ↦ f u (s ^ 2)) W 0))
      0 := by
  classical
  let F : Real → Real → M := fun u r ↦ f u (r ^ 2)
  let gamma : Real → M := fun tau ↦ f 0 tau
  let Y : (tau : Real) → TangentSpace I (gamma tau) :=
    fun tau ↦ lVelocity (I := I) (fun u ↦ f u tau) 0
  let c : Real := 4 * s ^ 2
  have hF : IsSmoothVariation (I := I) F := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_fst.prodMk (contMDiff_snd.pow 2))
  have hFat : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ F q.1 q.2) (0, s) :=
    (hF : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
  have hWreg : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ F u s) W 0) 0 := by
    simpa only [F] using hW
  have hreg := lRegEuler_deriv (I := I) S T s F W hFat hWreg
  let DW : TangentSpace I (f 0 (s ^ 2)) :=
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
      (fun u ↦ f u (s ^ 2)) W 0
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : Nat) gamma := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt 𝓘(Real, Real) I gamma (r ^ 2) :=
    Filter.Eventually.of_forall (fun _ ↦
      hgamma.mdifferentiableAt (by norm_num))
  have hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2) := by
    apply Filter.Eventually.of_forall
    intro r
    simpa only [gamma, Y, lVelocity, varFst] using
      variationField_chartRep_differentiableAt
        (I := I) f hf (r ^ 2)
  have hF0 : ContMDiff 𝓘(Real, Real) I (8 : Nat) (F 0) := by
    exact (hF : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hF02 : ContMDiffAt 𝓘(Real, Real) I 2 (F 0) s :=
    hF0.contMDiffAt.of_le (by norm_num)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ lVelocity (I := I) (F 0) r) s) s := by
    exact lVelocity_chartRepAt_diff (I := I) (F 0) s hF02
  have hA_sq : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦ lVelocity (I := I) (sqReparam gamma) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ lVelocity (I := I) (F 0) r) s) s
    exact hA
  rcases lRegVar_reg (I := I) S T s F hF with
    ⟨_, _, hZraw⟩
  have hZ : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (sqReparam gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) (F 0)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ F v u) 0) r)
        s) s
    exact hZraw
  have hDY := lJacobiVel_sq_diff (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA_sq hZ
  have hpairRaw := lJacobiPair_sq (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA_sq hDY hZ (W 0)
  have hpair :
      c * lJacobiPair S T gamma Y (s ^ 2) (W 0) =
        lRegJacobiPair S T (F 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0) s (W 0) := by
    change c * lJacobiPair S T gamma Y (s ^ 2) (W 0) =
      lRegJacobiPair S T (sqReparam gamma)
        (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0) s (W 0)
    simpa only [c, F, gamma, Y] using hpairRaw
  have hcurve (u : Real) :
      ContMDiff 𝓘(Real, Real) I (8 : Nat) (f u) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have htail :
      c * lEulerPair S T gamma (s ^ 2) DW =
        lRegEulerPair S T (F 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u ↦ F u s) W 0) := by
    change c * lEulerPair S T gamma (s ^ 2) DW =
      lRegEulerPair S T (sqReparam gamma) s
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun u ↦ F u s) W 0)
    simpa only [c] using
      lRegEuler_sq (I := I) S T gamma s DW hs
        (hgamma.mdifferentiableAt (by norm_num))
        (lVelocity_chartRepAt_diff (I := I) gamma (s ^ 2)
          (hgamma.contMDiffAt.of_le (by norm_num)))
  have hscale (u : Real) :
      c * lEulerPair S T (f u) (s ^ 2) (W u) =
        lRegEulerPair S T (F u) s (W u) := by
    change c * lEulerPair S T (f u) (s ^ 2) (W u) =
      lRegEulerPair S T (sqReparam (f u)) s (W u)
    simpa only [c] using
      lRegEuler_sq (I := I) S T (f u) s (W u) hs
        ((hcurve u).mdifferentiableAt (by norm_num))
        (lVelocity_chartRepAt_diff (I := I) (f u) (s ^ 2)
          ((hcurve u).contMDiffAt.of_le (by norm_num)))
  have hfun :
      (fun u : Real ↦ lRegEulerPair S T (F u) s (W u)) =
        fun u : Real ↦ c * lEulerPair S T (f u) (s ^ 2) (W u) := by
    funext u
    exact (hscale u).symm
  have hscaled : HasDerivAt
      (fun u : Real ↦ c * lEulerPair S T (f u) (s ^ 2) (W u))
      (c * (lJacobiPair S T gamma Y (s ^ 2) (W 0) +
        lEulerPair S T gamma (s ^ 2) DW)) 0 := by
    rw [← hfun]
    simpa only [mul_add, hpair, htail] using hreg
  have hc : c ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs.ne')
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul, gamma, Y, DW] using
    hscaled.const_mul c⁻¹

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lEuler_var_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (tau : Real) (hpos : 0 < tau) (ht : T - tau ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u tau))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u tau) W 0) 0) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) tau (W u))
      (lJacobiPair S T (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0)
          tau (W 0) +
        lEulerPair S T (f 0) tau
          (covDerivAlong (I := I) (S.base.metric (T - tau))
            (fun u ↦ f u tau) W 0))
      0 := by
  generalize hsdef : Real.sqrt tau = s
  have hs : 0 < s := by
    rw [← hsdef]
    exact Real.sqrt_pos.2 hpos
  have hsq : s ^ 2 = tau := by
    rw [← hsdef]
    exact Real.sq_sqrt hpos.le
  cases hsq
  exact lEuler_var_full (I := I) S hS T f hf s hs ht W hW

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lEuler_var_geo
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (tau : Real) (hpos : 0 < tau) (ht : T - tau ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u tau))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u tau) W 0) 0)
    (hgeo : HasLEquationAt S T (f 0) tau) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) tau (W u))
      (lJacobiPair S T (f 0)
        (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0)
        tau (W 0))
      0 := by
  have hfull := lEuler_var_deriv (I := I)
    S hS T f hf tau hpos ht W hW
  have hzero :
      lEulerPair S T (f 0) tau
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (fun u ↦ f u tau) W 0) = 0 :=
    hgeo.2.2 _
  simpa only [hzero, add_zero] using hfull

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lEuler_var_sq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (s : Real) (hs : 0 < s) (ht : T - s ^ 2 ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u (s ^ 2)))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u (s ^ 2)) W 0) 0)
    (hgeo : HasLEquationAt S T (f 0) (s ^ 2)) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) (s ^ 2) (W u))
      (lJacobiPair S T (f 0)
        (fun tau ↦ lVelocity (I := I) (fun u ↦ f u tau) 0)
        (s ^ 2) (W 0))
      0 := by
  have hfull := lEuler_var_full (I := I) S hS T f hf s hs ht W hW
  have hzero :
      lEulerPair S T (f 0) (s ^ 2)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun u ↦ f u (s ^ 2)) W 0) = 0 :=
    hgeo.2.2 _
  simpa only [hzero, add_zero] using hfull

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lEulerInt_deriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLGeodesic S T (f 0) (Set.uIcc a b)) :
    HasDerivAt
      (fun u : Real =>
        ∫ tau in a..b,
          (-2 * Real.sqrt tau) *
            lEulerPair S T (f u) tau
              (lVelocity (I := I) (fun v : Real => f v tau) u))
      (∫ tau in a..b,
        (-2 * Real.sqrt tau) *
          lJacobiPair S T (f 0)
            (fun r : Real =>
              lVelocity (I := I) (fun u : Real => f u r) 0)
            tau
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | 0 < p.2 ∧ T - p.2 ∈ D.regular}
  let F : Real → Real → Real := fun u tau =>
    (-2 * Real.sqrt tau) *
      lEulerPair S T (f u) tau
        (lVelocity (I := I) (fun v : Real => f v tau) u)
  let dF : Real → Real → Real := fun u tau =>
    fderiv Real (fun p : Real × Real => F p.1 p.2) (u, tau) (1, 0)
  let J : Real → Real := fun tau =>
    (-2 * Real.sqrt tau) *
      lJacobiPair S T (f 0)
        (fun r : Real =>
          lVelocity (I := I) (fun u : Real => f u r) 0)
        tau (lVelocity (I := I) (fun u : Real => f u tau) 0)
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hUopen : IsOpen U := by
    change IsOpen
      ({p : Real × Real | 0 < p.2} ∩
        {p : Real × Real | T - p.2 ∈ D.regular})
    exact (isOpen_lt continuous_const continuous_snd).inter
      (D.regular_isOpen.preimage (continuous_const.sub continuous_snd))
  have hFJoint : ContDiffOn Real 1
      (fun p : Real × Real => F p.1 p.2) U := by
    simpa only [F, U] using lEuler_var_c1 S hS T f hf
  have hFContJoint : ContinuousOn
      (fun p : Real × Real => F p.1 p.2) U :=
    hFJoint.continuousOn
  have hfdCont : ContinuousOn
      (fderiv Real (fun p : Real × Real => F p.1 p.2)) U :=
    hFJoint.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdFJoint : ContinuousOn
      (fun p : Real × Real => dF p.1 p.2) U := by
    simpa only [dF] using hfdCont.clm_apply continuousOn_const
  have hFCont (u : Real) : ContinuousOn (F u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => (u, tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hFContJoint.comp hmap
    intro tau htau
    exact ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
  have hdFCont (u : Real) : ContinuousOn (dF u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => (u, tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdFJoint.comp hmap
    intro tau htau
    exact ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
  have hFDiff : DifferentiableOn Real
      (fun p : Real × Real => F p.1 p.2) U :=
    hFJoint.differentiableOn (by norm_num)
  have hFDeriv (u tau : Real) (htau : tau ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real => F z tau) (dF u tau) u := by
    have hpU : (u, tau) ∈ U :=
      ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
    have hFAt : DifferentiableAt Real
        (fun p : Real × Real => F p.1 p.2) (u, tau) :=
      (hFDiff (u, tau) hpU).differentiableAt (hUopen.mem_nhds hpU)
    simpa only [dF] using Aux2.hasDerivAt_slice_fst
      (fun z s : Real => F z s) u tau hFAt
  let K : Set (Real × Real) :=
    Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ⟨lt_of_lt_of_le hpos hp.2.1, ht p.2 hp.2⟩
  obtain ⟨C, hC⟩ :=
    hKcompact.bddAbove_image (hdFJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dF p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hs : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hFmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (F u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u =>
      (hFCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hFint : IntervalIntegrable (F 0) MeasureTheory.volume a b :=
    (hFCont 0).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (dF 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdFCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ tau ∂MeasureTheory.volume,
      tau ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dF u tau‖ ≤ (fun _ : Real => C₀) tau :=
    Filter.Eventually.of_forall fun tau htau u hu =>
      hC₀ (u, tau) ⟨hu, Set.uIoc_subset_uIcc htau⟩
  have hboundInt : IntervalIntegrable (fun _ : Real => C₀)
      MeasureTheory.volume a b :=
    continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ tau ∂MeasureTheory.volume,
      tau ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real => F z tau) (dF u tau) u :=
    Filter.Eventually.of_forall fun tau htau u _ =>
      hFDeriv u tau (Set.uIoc_subset_uIcc htau)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := dF) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real => C₀) hs hFmeas hFint hF'meas
      hbound hboundInt hdiff
  have hJEq : Set.EqOn (dF 0) J (Set.uIcc a b) := by
    intro tau htau
    let W : (u : Real) → TangentSpace I (f u tau) := fun u =>
      lVelocity (I := I) (fun v : Real => f v tau) u
    have hslice : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real => f u tau) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
          (fun u : Real => (u, tau)) :=
        contMDiff_id.prodMk contMDiff_const
      have hcomp := (hf : ContMDiff _ _ (8 : ℕ) _).comp hincl
      exact hcomp.contMDiffAt.of_le (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real => f u tau) W 0) 0 := by
      change DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u tau)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ f v tau) u) 0) 0
      exact lVelocity_chartRepAt_diff (I := I) (fun u : Real ↦ f u tau) 0 hslice
    have hpoint := lEuler_var_geo (I := I)
      S hS T f hf tau (hgeo.pos htau) (ht tau htau)
      W hW (hgeo.at htau)
    have hweighted : HasDerivAt (fun u : Real => F u tau) (J tau) 0 := by
      simpa only [F, J, W] using
        hpoint.const_mul (-2 * Real.sqrt tau)
    exact (hFDeriv 0 tau htau).unique hweighted
  have hint : (∫ tau in a..b, dF 0 tau) =
      ∫ tau in a..b, J tau :=
    intervalIntegral.integral_congr hJEq
  rw [hint] at hparam
  simpa only [F, J] using hparam.2

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lLength_second_jac
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLGeodesic S T (f 0) (Set.uIcc a b))
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real =>
        deriv (fun v : Real =>
          lLength S T (fun tau : Real => f v tau) a b) u)
      (∫ tau in a..b,
        (-2 * Real.sqrt tau) *
          lJacobiPair S T (f 0)
            (fun r : Real =>
              lVelocity (I := I) (fun u : Real => f u r) 0)
            tau
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      0 := by
  let L : Real → Real := fun u =>
    lLength S T (fun tau : Real => f u tau) a b
  let Eul : Real → Real := fun u =>
    ∫ tau in a..b,
      (-2 * Real.sqrt tau) *
        lEulerPair S T (f u) tau
          (lVelocity (I := I) (fun v : Real => f v tau) u)
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hderivEq (u : Real) : deriv L u = Eul u := by
    let fu : Real → Real → M := fun v tau => f (u + v) tau
    have hfu : IsSmoothVariation (I := I) fu := by
      exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfu0 : fu 0 = f u := by
      funext tau
      simp only [fu, add_zero]
    have hYshift (tau : Real) :
        lVelocity (I := I) (fun v : Real => fu v tau) 0 =
          lVelocity (I := I) (fun v : Real => f v tau) u := by
      simpa only [fu, lVelocity, varFst] using
        varFst_shift (I := I) f hf u tau
    have hYa :
        lVelocity (I := I) (fun v : Real => fu v a) 0 = 0 := by
      have hconst : (fun v : Real => fu v a) = fun _ : Real => f 0 a := by
        funext v
        exact hfixa (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hYb :
        lVelocity (I := I) (fun v : Real => fu v b) 0 = 0 := by
      have hconst : (fun v : Real => fu v b) = fun _ : Real => f 0 b := by
        funext v
        exact hfixb (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hshift := lLength_euler S hS T fu hfu a b hpos ht
    rw [hYa, hYb] at hshift
    rw [hfu0] at hshift
    have hshift' : HasDerivAt (fun v : Real => L (u + v)) (Eul u) 0 := by
      simpa [L, Eul, fu, hYshift] using hshift
    have hderiv := hshift'.deriv
    rw [deriv_comp_const_add L u 0, add_zero] at hderiv
    exact hderiv
  have hEul := lEulerInt_deriv (I := I) S hS T f hf a b hgeo
  have hfun : (fun u : Real => deriv L u) = Eul :=
    funext hderivEq
  rw [hfun]
  simpa only [L, Eul] using hEul

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lVarMetric_c2
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) (u : Real) :
    ContDiffOn Real 2
      (fun p : Real × Real =>
        (S.base.metric (T - p.1)).inner (f u p.2)
          (lVelocity (I := I) (fun v : Real => f v p.2) u)
          (lVelocity (I := I) (fun v : Real => f v p.2) u))
      {p : Real × Real | T - p.1 ∈ D.regular} := by
  have hswap : IsSmoothVariation (I := I)
      (fun a b : Real => f b a) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hYone : ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) (7 : ℕ)
      (fun tau : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f u tau)
          (lVelocity (I := I) (fun v : Real => f v tau) u) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real => f b a) hswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : ℕ)
        (fun tau : Real => (tau, u)))
    simpa only [lVelocity, Function.comp_def, id_eq] using hcomp
  have hYall : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) (7 : ℕ)
      (fun p : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f u p.2)
          (lVelocity (I := I) (fun v : Real => f v p.2) u) :
            TangentBundle I M)) := by
    have hcomp := hYone.comp
      (contMDiff_snd : ContMDiff
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real) (7 : ℕ)
        (fun p : Real × Real => p.2))
    simpa only [Function.comp_def] using hcomp
  have hbaseAll : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : ℕ)
      (fun p : Real × Real => f u p.2) := by
    exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_const.prodMk contMDiff_snd)
  intro p hp
  have hbaseAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real => f u q.2) p :=
    hbaseAll.contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.1, f u q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_fst).prodMk hbaseAt
  have hmetric₀ := hG.metricCLMSmoothAt
    (t := T - p.1) (x := f u p.2) (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f u q.2) ((S.base.metric (T - q.1)).inner (f u q.2))) p := by
    simpa only [SolutionOn.family_metric, Function.comp_def] using
      (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hY : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f u q.2)
          (lVelocity (I := I) (fun v : Real => f v q.2) u) :
            TangentBundle I M)) p :=
    hYall.contMDiffAt.of_le (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hY hY
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (S.base.metric (T - q.1)).inner (f u q.2)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    convert htotal.2 using 1 ; rfl
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real =>
        (S.base.metric (T - q.1)).inner (f u q.2)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lVarNorm_c2
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) (u : Real) :
    ContDiffOn Real 2
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (f u tau)
          (lVelocity (I := I) (fun v : Real => f v tau) u)
          (lVelocity (I := I) (fun v : Real => f v tau) u))
      {tau : Real | T - tau ∈ D.regular} := by
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let Q : Real × Real → Real := fun p =>
    (S.base.metric (T - p.1)).inner (f u p.2)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
  have hQ : ContDiffOn Real 2 Q
      {p : Real × Real | T - p.1 ∈ D.regular} := by
    simpa only [Q] using lVarMetric_c2 S T f hG hf u
  have hdiag : ContDiffOn Real 2
      (fun tau : Real => (tau, tau)) V :=
    contDiffOn_id.prodMk contDiffOn_id
  have hout := hQ.comp hdiag (fun tau htau => htau)
  simpa only [Q, V, Function.comp_def] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lVarRicci_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (u : Real) :
    ContDiffOn Real 1
      (fun tau : Real =>
        S.ricciAt (T - tau) (f u tau)
          (vec2
            (lVelocity (I := I) (fun v : Real => f v tau) u)
            (lVelocity (I := I) (fun v : Real => f v tau) u)))
      {tau : Real | T - tau ∈ D.regular} := by
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let W : Set (Real × Real) :=
    {p : Real × Real | T - p.1 ∈ D.regular}
  let Q : Real × Real → Real := fun p =>
    (S.base.metric (T - p.1)).inner (f u p.2)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
  let dQ : Real × Real → Real := fun p =>
    fderiv Real Q p (1, 0)
  let raw : Real → Real := fun tau => dQ (tau, tau) / 2
  let ric : Real → Real := fun tau =>
    S.ricciAt (T - tau) (f u tau)
      (vec2
        (lVelocity (I := I) (fun v : Real => f v tau) u)
        (lVelocity (I := I) (fun v : Real => f v tau) u))
  have hWopen : IsOpen W :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_fst)
  have hQ2 : ContDiffOn Real 2 Q W := by
    simpa only [Q, W] using
      lVarMetric_c2 S T f hS.smoothMetric hf u
  have hdQ : ContDiffOn Real 1 dQ W := by
    have hfd : ContDiffOn Real 1 (fderiv Real Q) W :=
      hQ2.fderiv_of_isOpen hWopen (by norm_num)
    simpa only [dQ] using hfd.clm_apply contDiffOn_const
  have hdiag : ContDiffOn Real 1 (fun tau : Real => (tau, tau)) V :=
    contDiffOn_id.prodMk contDiffOn_id
  have hdDiag : ContDiffOn Real 1 (fun tau : Real => dQ (tau, tau)) V :=
    hdQ.comp hdiag (fun tau htau => htau)
  have hraw : ContDiffOn Real 1 raw V := by
    simpa only [raw] using hdDiag.div_const 2
  have hQDiff : DifferentiableOn Real Q W :=
    hQ2.differentiableOn (by norm_num)
  have heq : Set.EqOn ric raw V := by
    intro tau htau
    have hpW : (tau, tau) ∈ W := htau
    have hQAt : DifferentiableAt Real Q (tau, tau) :=
      (hQDiff (tau, tau) hpW).differentiableAt
        (hWopen.mem_nhds hpW)
    have hslice : HasDerivAt
        (fun s : Real => Q (s, tau)) (dQ (tau, tau)) tau := by
      simpa only [dQ] using Aux2.hasDerivAt_slice_fst
        (fun s r : Real => Q (s, r)) tau tau hQAt
    let Y : TangentSpace I (f u tau) :=
      lVelocity (I := I) (fun v : Real => f v tau) u
    have hmetric := metricDerivAt (I := I) S hS
      (⟨T - tau, htau⟩ :
        DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (f u tau) Y Y
    have hsub := (hasDerivAt_id (x := tau)).const_sub T
    have htime := hmetric.comp tau hsub
    have htimeQ : HasDerivAt (fun s : Real => Q (s, tau))
        (2 * S.ricciAt (T - tau) (f u tau) (vec2 Y Y)) tau := by
      simpa only [Q, Y, SolutionOn.family_metric, Function.comp_def,
        id_eq, mul_neg, neg_mul, neg_neg, mul_one] using htime
    have hdQEq :
        dQ (tau, tau) =
          2 * S.ricciAt (T - tau) (f u tau) (vec2 Y Y) :=
      hslice.unique htimeQ
    dsimp only [ric, raw]
    rw [hdQEq]
    ring
  have hout : ContDiffOn Real 1 ric V :=
    hraw.congr (fun tau htau => heq htau)
  simpa only [ric, V] using hout

omit [InnerProductSpace Real E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lVarJacobiVel_diff
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (tau : Real) (hpos : 0 < tau) (ht : T - tau ∈ D.regular) :
    DifferentiableAt Real
      (chartRepAt (I := I) (f 0)
        (lJacobiVel S T (f 0)
          (fun r : Real =>
            lVelocity (I := I) (fun u : Real => f u r) 0)) tau) tau := by
  let s : Real := Real.sqrt tau
  let F : Real → Real → M := fun u r => f u (r ^ 2)
  let gamma : Real → M := f 0
  let Y : (r : Real) → TangentSpace I (gamma r) := fun r =>
    lVelocity (I := I) (fun u : Real => f u r) 0
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  have hsq : s ^ 2 = tau := Real.sq_sqrt hpos.le
  have ht_sq : T - s ^ 2 ∈ D.regular := by
    simpa only [hsq] using ht
  have hF : IsSmoothVariation (I := I) F := by
    exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_fst.prodMk (contMDiff_snd.pow 2))
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : ℕ) gamma := by
    exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt 𝓘(Real, Real) I gamma (r ^ 2) :=
    Filter.Eventually.of_forall (fun _ =>
      hgamma.mdifferentiableAt (by norm_num))
  have hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2) := by
    apply Filter.Eventually.of_forall
    intro r
    simpa only [gamma, Y, lVelocity, varFst] using
      variationField_chartRep_differentiableAt
        (I := I) f hf (r ^ 2)
  have hF0 : ContMDiff 𝓘(Real, Real) I (8 : ℕ) (F 0) := by
    exact (hF : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hF02 : ContMDiffAt 𝓘(Real, Real) I 2 (F 0) s :=
    hF0.contMDiffAt.of_le (by norm_num)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real => lVelocity (I := I) (F 0) r) s) s := by
    exact lVelocity_chartRepAt_diff (I := I) (F 0) s hF02
  have hA_sq : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real ↦ lVelocity (I := I) (sqReparam gamma) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ lVelocity (I := I) (F 0) r) s) s
    exact hA
  rcases lRegVar_reg (I := I) S T s F hF with ⟨_, _, hZraw⟩
  have hZ : DifferentiableAt Real
      (chartRepAt (I := I) (sqReparam gamma)
        (fun r : Real =>
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (sqReparam gamma) (fun u : Real => Y (u ^ 2)) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) (F 0)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ F v u) 0) r)
        s) s
    exact hZraw
  have hout := lJacobiVel_sq_diff (I := I) S hS T gamma Y s hs ht_sq
    hgamma_sq hY_sq hA_sq hZ
  simpa only [gamma, Y, hsq] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lVarInner_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (u : Real) :
    ContDiffOn Real 1
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (f u tau)
          (lJacobiVel S T (f u)
            (fun r : Real =>
              lVelocity (I := I) (fun v : Real => f v r) u) tau)
          (lVelocity (I := I) (fun v : Real => f v tau) u))
      {tau : Real | T - tau ∈ D.regular} := by
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let gamma : Real → M := f u
  let Y : ∀ tau, TangentSpace I (gamma tau) := fun tau =>
    lVelocity (I := I) (fun v : Real => f v tau) u
  let N : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (gamma tau) (Y tau) (Y tau)
  let dN : Real → Real := fun tau => fderiv Real N tau 1
  let R : Real → Real := fun tau =>
    S.ricciAt (T - tau) (gamma tau) (vec2 (Y tau) (Y tau))
  let raw : Real → Real := fun tau => (dN tau - 2 * R tau) / 2
  let inner : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (gamma tau)
      (lJacobiVel S T gamma Y tau) (Y tau)
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have hN2 : ContDiffOn Real 2 N V := by
    simpa only [N, gamma, Y, V] using
      lVarNorm_c2 S T f hS.smoothMetric hf u
  have hdN : ContDiffOn Real 1 dN V := by
    have hfd : ContDiffOn Real 1 (fderiv Real N) V :=
      hN2.fderiv_of_isOpen hVopen (by norm_num)
    simpa only [dN] using hfd.clm_apply contDiffOn_const
  have hR : ContDiffOn Real 1 R V := by
    simpa only [R, gamma, Y, V] using lVarRicci_c1 S hS T f hf u
  have hraw : ContDiffOn Real 1 raw V := by
    simpa only [raw] using (hdN.sub (contDiffOn_const.mul hR)).div_const 2
  have hNDiff : DifferentiableOn Real N V :=
    hN2.differentiableOn (by norm_num)
  have heq : Set.EqOn inner raw V := by
    intro tau htau
    have hNAt : DifferentiableAt Real N tau :=
      (hNDiff tau htau).differentiableAt (hVopen.mem_nhds htau)
    have hNderiv : HasDerivAt N (dN tau) tau := by
      simpa only [dN] using hNAt.hasFDerivAt.hasDerivAt
    have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau := by
      have hcurve : ContMDiff 𝓘(Real, Real) I (8 : ℕ) gamma := by
        exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
          (contMDiff_const.prodMk contMDiff_id)
      exact hcurve.mdifferentiableAt (by norm_num)
    let fu : Real → Real → M := fun a r => f (u + a) r
    have hfu : IsSmoothVariation (I := I) fu := by
      exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfu0 : fu 0 = gamma := by
      funext r
      simp only [fu, gamma, add_zero]
    have hYshift (r : Real) :
        lVelocity (I := I) (fun a : Real => fu a r) 0 = Y r := by
      simpa only [fu, Y, lVelocity, varFst] using
        varFst_shift (I := I) f hf u r
    have hYfun :
        (fun r : Real =>
          lVelocity (I := I) (fun a : Real => fu a r) 0) = Y :=
      funext hYshift
    have hY : DifferentiableAt Real
        (chartRepAt (I := I) gamma Y tau) tau := by
      have hout : DifferentiableAt Real
          (chartRepAt (I := I) (fu 0)
            (fun r : Real =>
              lVelocity (I := I) (fun a : Real => fu a r) 0) tau) tau := by
        simpa only [lVelocity, chartRepAt_apply] using
          variationField_chartRep_differentiableAt
            (I := I) fu hfu tau
      rw [hfu0, hYfun] at hout
      exact hout
    have hinner := lInner_deriv S hS T gamma Y Y tau htau
      hgamma hY hY
    have hdNEq :
        dN tau =
          ((S.base.metric (T - tau)).inner (gamma tau)
              (lJacobiVel S T gamma Y tau) (Y tau) +
            (S.base.metric (T - tau)).inner (gamma tau)
              (Y tau) (lJacobiVel S T gamma Y tau)) +
            2 * R tau := by
      exact hNderiv.unique (by
        simpa only [N, R, lJacobiVel] using hinner)
    have hsymm :
        (S.base.metric (T - tau)).inner (gamma tau)
            (Y tau) (lJacobiVel S T gamma Y tau) =
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVel S T gamma Y tau) (Y tau) :=
      (S.base.metric (T - tau)).symm _ _ _
    dsimp only [inner, raw]
    rw [hdNEq, hsymm]
    ring
  have hout : ContDiffOn Real 1 inner V :=
    hraw.congr (fun tau htau => heq htau)
  simpa only [inner, gamma, Y, V] using hout

noncomputable def lIndexInt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (tau : Real) : Real :=
  let t := T - tau
  let g := S.base.metric t
  let cov := S.base.connection t
  let X := lVelocity (I := I) gamma tau
  let DY := lJacobiVel S T gamma Y tau
  let DW := lJacobiVel S T gamma W tau
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 cov (S.ricci t) (gamma tau)
  Real.sqrt tau *
    (g.inner (gamma tau) DY DW -
      S.base.rm04 t (gamma tau) (vec4 (Y tau) X X (W tau)) +
      (1 / 2 : Real) *
        hessianSec (I := I) cov (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t) (gamma tau)
          (vec2 (Y tau) (W tau)) +
      dRic (vec3 X (Y tau) (W tau)) -
      dRic (vec3 (Y tau) X (W tau)) -
      dRic (vec3 (W tau) X (Y tau)))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lIndexInt_symm
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (tau : Real) :
    lIndexInt S T gamma Y W tau =
      lIndexInt S T gamma W Y tau := by
  let t := T - tau
  let g := S.base.metric t
  let x := gamma tau
  let X := lVelocity (I := I) gamma tau
  let DY := lJacobiVel S T gamma Y tau
  let DW := lJacobiVel S T gamma W tau
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection t) (S.ricci t) x
  have hinner : g.inner x DY DW = g.inner x DW DY :=
    g.symm x DY DW
  have hreal : rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) (S.base.rm04 t) := by
    change rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g)
      (metricRm04 (I := I) (M := M) g)
    rw [show metricRm04 (I := I) (M := M) g =
      (metricCurvData (I := I) (M := M) g).rm04 by rfl]
    exact (metricCurvData (I := I) (M := M) g).rm04Realizes
  have hpair :=
    rm04PairSymmAt_of_leviCivita_realizes
      (I := I) g (S.base.rm04 t) hreal (x := x)
  have hinput :=
    rm04InputSkewAt_of_leviCivita_realizes
      (I := I) g (S.base.rm04 t) hreal (x := x)
  have houtput :=
    rm04OutputSkewAt_of_leviCivita_realizes
      (I := I) g (S.base.rm04 t) hreal (x := x)
  have hcurv :
      S.base.rm04 t x (vec4 (Y tau) X X (W tau)) =
        S.base.rm04 t x (vec4 (W tau) X X (Y tau)) := by
    linarith [hpair (Y tau) X X (W tau),
      hinput (W tau) X (Y tau) X,
      houtput (W tau) X (Y tau) X]
  have hhess :
      hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t) x
          (vec2 (Y tau) (W tau)) =
        hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t) x
          (vec2 (W tau) (Y tau)) := by
    simpa only [g, t, SolutionFamily.connection] using
      DifferentialGeometry.Geometry.Connection.hessSymm
        (I := I) (M := M) g (S.scalar t)
        (scalarSmoothOfSol (I := I) S t) (Y tau) (W tau)
  have hdRic :
      dRic (vec3 X (Y tau) (W tau)) =
        dRic (vec3 X (W tau) (Y tau)) := by
    simpa only [dRic, g, t, x, SolutionFamily.connection,
      SolutionFamily.ricci, SolutionOn.ricci, metricCov] using
      DifferentialGeometry.Geometry.Curvature.metricNablaSymm
        (I := I) (M := M) g x X (Y tau) (W tau)
  simp only [lIndexInt]
  rw [hinner, hcurv, hhess, hdRic]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lIndexInt_self
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) :
    lIndexInt S T gamma Y Y tau =
      let t := T - tau
      let g := S.base.metric t
      let cov := S.base.connection t
      let X := lVelocity (I := I) gamma tau
      let DY := lJacobiVel S T gamma Y tau
      let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
        2 cov (S.ricci t) (gamma tau)
      Real.sqrt tau *
        (g.inner (gamma tau) DY DY -
          S.base.rm04 t (gamma tau) (vec4 (Y tau) X X (Y tau)) +
          (1 / 2 : Real) *
            hessianSec (I := I) cov (metricCov_smooth (I := I) g)
              (S.scalar t) (scalarSmoothOfSol (I := I) S t) (gamma tau)
              (vec2 (Y tau) (Y tau)) +
          dRic (vec3 X (Y tau) (Y tau)) -
          2 * dRic (vec3 (Y tau) X (Y tau))) := by
  simp only [lIndexInt]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lIndex_balance
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) (hpos : 0 < tau) :
    2 * lIndexInt S T gamma Y W tau +
        2 * (Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau)) =
      (2 * Real.sqrt tau) *
          (((S.base.metric (T - tau)).inner (gamma tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
                (lJacobiVel S T gamma Y) tau) (W tau) +
            (S.base.metric (T - tau)).inner (gamma tau)
              (lJacobiVel S T gamma Y tau)
              (lJacobiVel S T gamma W tau)) +
            2 * S.ricciAt (T - tau) (gamma tau)
              (vec2 (lJacobiVel S T gamma Y tau) (W tau))) +
        (1 / Real.sqrt tau) *
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVel S T gamma Y tau) (W tau) := by
  have hsqrt_ne : Real.sqrt tau ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  simp only [lIndexInt, lJacobiPair, lJacobiVel]
  field_simp [hsqrt_ne, ne_of_gt hpos]
  rw [Real.sq_sqrt hpos.le]
  ring

noncomputable def lIndex
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (a b : Real) : Real :=
  ∫ tau in a..b, lIndexInt S T gamma Y W tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lIndex_symm
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real) :
    lIndex S T gamma Y W a b =
      lIndex S T gamma W Y a b := by
  apply intervalIntegral.integral_congr
  intro tau _
  exact lIndexInt_symm (I := I) S T gamma Y W tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
@[simp] theorem lIndex_self
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (a : Real) :
    lIndex S T gamma Y W a a = 0 := by
  simp [lIndex]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lIndex_add_adj
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (a b c : Real)
    (hab : IntervalIntegrable (lIndexInt S T gamma Y W)
      MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (lIndexInt S T gamma Y W)
      MeasureTheory.volume b c) :
    lIndex S T gamma Y W a b + lIndex S T gamma Y W b c =
      lIndex S T gamma Y W a c := by
  simpa [lIndex] using intervalIntegral.integral_add_adjacent_intervals hab hbc

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_green
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hDY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma (lJacobiVel S T gamma Y) tau) tau)
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real ↦
        ((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
              (lJacobiVel S T gamma Y) tau) (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVel S T gamma Y tau)
            (lJacobiVel S T gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau)
            (vec2 (lJacobiVel S T gamma Y tau) (W tau)))
      MeasureTheory.volume a b)
    (hJint : IntervalIntegrable
      (fun tau : Real ↦ Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau))
      MeasureTheory.volume a b)
    (hIint : IntervalIntegrable (lIndexInt S T gamma Y W)
      MeasureTheory.volume a b) :
    lIndex S T gamma Y W a b =
      Real.sqrt b * (S.base.metric (T - b)).inner (gamma b)
          (lJacobiVel S T gamma Y b) (W b) -
        Real.sqrt a * (S.base.metric (T - a)).inner (gamma a)
          (lJacobiVel S T gamma Y a) (W a) -
        ∫ tau in a..b,
          Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau) := by
  let DY : ∀ tau, TangentSpace I (gamma tau) := lJacobiVel S T gamma Y
  let U : Real → Real := fun tau ↦
    (S.base.metric (T - tau)).inner (gamma tau) (DY tau) (W tau)
  let P : Real → Real := fun tau ↦
    ((S.base.metric (T - tau)).inner (gamma tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma DY tau)
        (W tau) +
      (S.base.metric (T - tau)).inner (gamma tau) (DY tau)
        (lJacobiVel S T gamma W tau)) +
      2 * S.ricciAt (T - tau) (gamma tau) (vec2 (DY tau) (W tau))
  let Q : Real → Real := fun tau ↦ (1 / Real.sqrt tau) * U tau
  let J : Real → Real := fun tau ↦
    Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau)
  let G : Real → Real := lIndexInt S T gamma Y W
  let B : Real :=
    Real.sqrt b * U b - Real.sqrt a * U a
  have hP : IntervalIntegrable P MeasureTheory.volume a b := by
    simpa only [P, DY, lJacobiVel] using hPint
  have hPw : IntervalIntegrable
      (fun tau : Real ↦ (2 * Real.sqrt tau) * P tau)
      MeasureTheory.volume a b :=
    hP.continuousOn_mul (continuousOn_const.mul continuousOn_id.sqrt)
  have hUcont : ContinuousOn U (Set.uIcc a b) := by
    intro tau htau
    simpa only [U, DY] using
      (lInner_deriv S hS T gamma DY W tau (ht tau htau)
        (hgamma tau htau) (hDY tau htau) (hW tau htau)).continuousAt.continuousWithinAt
  have hInvcont : ContinuousOn (fun tau : Real ↦ 1 / Real.sqrt tau)
      (Set.uIcc a b) :=
    continuousOn_const.div continuousOn_id.sqrt (fun tau htau ↦
      ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le hpos htau.1)))
  have hQ : IntervalIntegrable Q MeasureTheory.volume a b := by
    exact (hInvcont.mul hUcont).intervalIntegrable
  have hG : IntervalIntegrable G MeasureTheory.volume a b := by
    simpa only [G] using hIint
  have hJ : IntervalIntegrable J MeasureTheory.volume a b := by
    simpa only [J] using hJint
  have hparts :
      (∫ tau in a..b, (2 * Real.sqrt tau) * P tau) =
        2 * B - ∫ tau in a..b, Q tau := by
    have hraw := lInner_parts S hS T gamma DY W a b hpos ht hgamma hDY hW hP
    simp only [P, Q, U, B, DY, lJacobiVel] at hraw ⊢
    linarith
  have hpoint : ∀ tau ∈ Set.uIcc a b,
      2 * G tau + 2 * J tau =
        (2 * Real.sqrt tau) * P tau + Q tau := by
    intro tau htau
    simpa only [G, J, P, Q, U, DY] using
      lIndex_balance (I := I) S T gamma Y W tau
        (lt_of_lt_of_le hpos htau.1)
  have hint :
      (∫ tau in a..b, (2 * G tau + 2 * J tau)) =
        ∫ tau in a..b, ((2 * Real.sqrt tau) * P tau + Q tau) :=
    intervalIntegral.integral_congr hpoint
  rw [intervalIntegral.integral_add (hG.const_mul 2) (hJ.const_mul 2),
    intervalIntegral.integral_add hPw hQ] at hint
  simp only [intervalIntegral.integral_const_mul] at hint
  rw [hparts] at hint
  unfold lIndex
  simpa only [G, J, B, U, DY] using (by linarith :
    (∫ tau in a..b, G tau) = B - ∫ tau in a..b, J tau)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_zero_ends
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hDY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma (lJacobiVel S T gamma Y) tau) tau)
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real ↦
        ((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
              (lJacobiVel S T gamma Y) tau) (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVel S T gamma Y tau)
            (lJacobiVel S T gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau)
            (vec2 (lJacobiVel S T gamma Y tau) (W tau)))
      MeasureTheory.volume a b)
    (hJint : IntervalIntegrable
      (fun tau : Real ↦ Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau))
      MeasureTheory.volume a b)
    (hIint : IntervalIntegrable (lIndexInt S T gamma Y W)
      MeasureTheory.volume a b)
    (hWa : W a = 0) (hWb : W b = 0) :
    lIndex S T gamma Y W a b =
      -∫ tau in a..b,
        Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau) := by
  have hgreen := lIndex_green (I := I) S hS T gamma Y W a b hpos ht
    hgamma hDY hW hPint hJint hIint
  rw [hWa, hWb] at hgreen
  simpa only [map_zero, mul_zero, neg_zero, zero_sub] using hgreen

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_jacobi
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hjac : IsLJacobi S T gamma Y (Set.uIcc a b))
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real ↦
        ((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
              (lJacobiVel S T gamma Y) tau) (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVel S T gamma Y tau)
            (lJacobiVel S T gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau)
            (vec2 (lJacobiVel S T gamma Y tau) (W tau)))
      MeasureTheory.volume a b)
    (hIint : IntervalIntegrable (lIndexInt S T gamma Y W)
      MeasureTheory.volume a b) :
    lIndex S T gamma Y W a b =
      Real.sqrt b * (S.base.metric (T - b)).inner (gamma b)
          (lJacobiVel S T gamma Y b) (W b) -
        Real.sqrt a * (S.base.metric (T - a)).inner (gamma a)
          (lJacobiVel S T gamma Y a) (W a) := by
  have hJzero : ∀ tau ∈ Set.uIcc a b,
      Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau) = 0 := by
    intro tau htau
    rw [(hjac tau htau).2.2.2 (W tau), mul_zero]
  have hJint : IntervalIntegrable
      (fun tau : Real ↦ Real.sqrt tau *
        lJacobiPair S T gamma Y tau (W tau))
      MeasureTheory.volume a b := by
    rw [intervalIntegrable_congr
      (f := fun tau : Real ↦ Real.sqrt tau *
        lJacobiPair S T gamma Y tau (W tau))
      (g := fun _ : Real ↦ (0 : Real)) (by
        intro tau htau
        exact hJzero tau (Set.uIoc_subset_uIcc htau))]
    exact intervalIntegrable_const
  have hgreen := lIndex_green (I := I) S hS T gamma Y W a b hpos ht
    (fun tau htau ↦ (hjac tau htau).1)
    (fun tau htau ↦ (hjac tau htau).2.2.1)
    hW hPint hJint hIint
  have hJintegral :
      (∫ tau in a..b,
        Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau)) = 0 := by
    calc
      _ = ∫ _tau in a..b, (0 : Real) :=
        intervalIntegral.integral_congr hJzero
      _ = 0 := by simp
  rw [hJintegral] at hgreen
  simpa only [sub_zero] using hgreen

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lLength_second_var
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLGeodesic S T (f 0) (Set.uIcc a b))
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real =>
        deriv (fun v : Real =>
          lLength S T (fun tau : Real => f v tau) a b) u)
      (2 * lIndex S T (f 0)
        (fun tau : Real =>
          lVelocity (I := I) (fun u : Real => f u tau) 0)
        (fun tau : Real =>
          lVelocity (I := I) (fun u : Real => f u tau) 0) a b)
      0 := by
  let gamma : Real → M := f 0
  let Y : (tau : Real) → TangentSpace I (gamma tau) := fun tau =>
    lVelocity (I := I) (fun u : Real => f u tau) 0
  let DY : (tau : Real) → TangentSpace I (gamma tau) :=
    lJacobiVel S T gamma Y
  let U : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (gamma tau) (DY tau) (Y tau)
  let P : Real → Real := fun tau =>
    ((S.base.metric (T - tau)).inner (gamma tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma DY tau)
        (Y tau) +
      (S.base.metric (T - tau)).inner (gamma tau) (DY tau) (DY tau)) +
      2 * S.ricciAt (T - tau) (gamma tau) (vec2 (DY tau) (Y tau))
  let J : Real → Real := fun tau =>
    Real.sqrt tau * lJacobiPair S T gamma Y tau (Y tau)
  let G : Real → Real := lIndexInt S T gamma Y Y
  let Q : Real → Real := fun tau => (1 / Real.sqrt tau) * U tau
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let A : Set (Real × Real) :=
    {p : Real × Real | 0 < p.2 ∧ T - p.2 ∈ D.regular}
  let Eul : Real × Real → Real := fun p =>
    (-2 * Real.sqrt p.2) *
      lEulerPair S T (f p.1) p.2
        (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
  let dEul : Real → Real := fun tau =>
    fderiv Real Eul (0, tau) (1, 0)
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau := by
    intro tau htau
    simpa only [gamma] using hgeo.mdiffAt htau
  have hY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma Y tau) tau := by
    intro tau _
    simpa only [gamma, Y, lVelocity, varFst] using
      variationField_chartRep_differentiableAt
        (I := I) f hf tau
  have hDY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma DY tau) tau := by
    intro tau htau
    simpa only [gamma, Y, DY] using
      lVarJacobiVel_diff (I := I) S hS T f hf tau
        (hgeo.pos htau) (ht tau htau)
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have hU1 : ContDiffOn Real 1 U V := by
    simpa only [U, DY, gamma, Y, V] using
      lVarInner_c1 (I := I) S hS T f hf 0
  have hUcont : ContinuousOn U (Set.uIcc a b) :=
    hU1.continuousOn.mono (fun tau htau => ht tau htau)
  have hdUcont : ContinuousOn (deriv U) (Set.uIcc a b) :=
    (hU1.continuousOn_deriv_of_isOpen hVopen (by norm_num)).mono
      (fun tau htau => ht tau htau)
  have hdUEq : ∀ tau ∈ Set.uIcc a b, deriv U tau = P tau := by
    intro tau htau
    have hinner := lInner_deriv S hS T gamma DY Y tau (ht tau htau)
      (hgamma tau htau) (hDY tau htau) (hY tau htau)
    simpa only [U, P, DY, lJacobiVel] using hinner.deriv
  have hPcont : ContinuousOn P (Set.uIcc a b) :=
    hdUcont.congr (fun tau htau => (hdUEq tau htau).symm)
  have hPint : IntervalIntegrable P MeasureTheory.volume a b :=
    hPcont.intervalIntegrable
  have hAopen : IsOpen A := by
    change IsOpen
      ({p : Real × Real | 0 < p.2} ∩
        {p : Real × Real | T - p.2 ∈ D.regular})
    exact (isOpen_lt continuous_const continuous_snd).inter
      (D.regular_isOpen.preimage (continuous_const.sub continuous_snd))
  have hEul1 : ContDiffOn Real 1 Eul A := by
    simpa only [Eul, A] using lEuler_var_c1 (I := I) S hS T f hf
  have hEulDiff : DifferentiableOn Real Eul A :=
    hEul1.differentiableOn (by norm_num)
  have hdEulJoint : ContinuousOn
      (fun p : Real × Real => fderiv Real Eul p (1, 0)) A := by
    exact (hEul1.continuousOn_fderiv_of_isOpen hAopen (by norm_num)).clm_apply
      continuousOn_const
  have hdEulCont : ContinuousOn dEul (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => ((0 : Real), tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdEulJoint.comp hmap
    intro tau htau
    exact ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
  have hEulSlice : ∀ tau ∈ Set.uIcc a b,
      HasDerivAt (fun u : Real => Eul (u, tau)) (dEul tau) 0 := by
    intro tau htau
    have hpA : ((0 : Real), tau) ∈ A :=
      ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
    have hEulAt : DifferentiableAt Real Eul (0, tau) :=
      (hEulDiff (0, tau) hpA).differentiableAt (hAopen.mem_nhds hpA)
    simpa only [dEul] using Aux2.hasDerivAt_slice_fst
      (fun u s : Real => Eul (u, s)) 0 tau hEulAt
  have hdEulEq : ∀ tau ∈ Set.uIcc a b, dEul tau = -2 * J tau := by
    intro tau htau
    let W : (u : Real) → TangentSpace I (f u tau) := fun u =>
      lVelocity (I := I) (fun v : Real => f v tau) u
    have hslice : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real => f u tau) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
          (fun u : Real => (u, tau)) :=
        contMDiff_id.prodMk contMDiff_const
      have hcomp := (hf : ContMDiff _ _ (8 : ℕ) _).comp hincl
      exact hcomp.contMDiffAt.of_le (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real => f u tau) W 0) 0 := by
      change DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u tau)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ f v tau) u) 0) 0
      exact lVelocity_chartRepAt_diff (I := I) (fun u : Real ↦ f u tau) 0 hslice
    have hpoint := lEuler_var_geo (I := I) S hS T f hf tau
      (hgeo.pos htau) (ht tau htau) W hW (hgeo.at htau)
    have hweighted : HasDerivAt (fun u : Real => Eul (u, tau))
        ((-2 * Real.sqrt tau) * lJacobiPair S T gamma Y tau (Y tau)) 0 := by
      simpa only [Eul, W, gamma, Y] using
        hpoint.const_mul (-2 * Real.sqrt tau)
    have heq := (hEulSlice tau htau).unique hweighted
    rw [heq]
    simp only [J]
    ring
  have hJcont : ContinuousOn J (Set.uIcc a b) := by
    have hraw : ContinuousOn (fun tau : Real => (-1 / 2 : Real) * dEul tau)
        (Set.uIcc a b) := continuousOn_const.mul hdEulCont
    apply hraw.congr
    intro tau htau
    change J tau = (-1 / 2 : Real) * dEul tau
    rw [hdEulEq tau htau]
    ring
  have hJint : IntervalIntegrable J MeasureTheory.volume a b :=
    hJcont.intervalIntegrable
  have hinvSqrt : ContinuousOn (fun tau : Real => 1 / Real.sqrt tau)
      (Set.uIcc a b) :=
    continuousOn_const.div continuousOn_id.sqrt (fun tau htau =>
      ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le hpos htau.1)))
  have hQcont : ContinuousOn Q (Set.uIcc a b) := by
    exact hinvSqrt.mul hUcont
  have hpoint : ∀ tau ∈ Set.uIcc a b,
      2 * G tau + 2 * J tau =
        (2 * Real.sqrt tau) * P tau + Q tau := by
    intro tau htau
    simpa only [G, J, P, Q, U, DY] using
      lIndex_balance (I := I) S T gamma Y Y tau
        (lt_of_lt_of_le hpos htau.1)
  let Graw : Real → Real := fun tau =>
    (((2 * Real.sqrt tau) * P tau + Q tau) - 2 * J tau) / 2
  have hGrawCont : ContinuousOn Graw (Set.uIcc a b) := by
    exact ((((continuousOn_const.mul continuousOn_id.sqrt).mul hPcont).add
      hQcont).sub (continuousOn_const.mul hJcont)).div_const 2
  have hGeq : Set.EqOn G Graw (Set.uIcc a b) := by
    intro tau htau
    dsimp only [Graw]
    linarith [hpoint tau htau]
  have hGcont : ContinuousOn G (Set.uIcc a b) :=
    hGrawCont.congr (fun tau htau => hGeq htau)
  have hIint : IntervalIntegrable G MeasureTheory.volume a b :=
    hGcont.intervalIntegrable
  have hYa : Y a = 0 := by
    have hconst : (fun u : Real => f u a) = fun _ : Real => f 0 a := by
      funext u
      exact hfixa u
    simp only [Y]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hYb : Y b = 0 := by
    have hconst : (fun u : Real => f u b) = fun _ : Real => f 0 b := by
      funext u
      exact hfixb u
    simp only [Y]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hzero := lIndex_zero_ends (I := I) S hS T gamma Y Y a b hpos ht
    hgamma hDY hY (by simpa only [P, DY] using hPint)
    (by simpa only [J] using hJint) (by simpa only [G] using hIint) hYa hYb
  have hcoef :
      (∫ tau in a..b,
        (-2 * Real.sqrt tau) * lJacobiPair S T gamma Y tau (Y tau)) =
        2 * lIndex S T gamma Y Y a b := by
    calc
      _ = ∫ tau in a..b, (-2 : Real) * J tau := by
        apply intervalIntegral.integral_congr
        intro tau _
        simp only [J]
        ring
      _ = (-2 : Real) * ∫ tau in a..b, J tau := by
        rw [intervalIntegral.integral_const_mul]
      _ = 2 * lIndex S T gamma Y Y a b := by
        rw [hzero]
        ring
  have hsecond := lLength_second_jac (I := I)
    S hS T f hf a b hgeo hfixa hfixb
  rw [show
    (∫ tau in a..b,
      (-2 * Real.sqrt tau) *
        lJacobiPair S T (f 0)
          (fun r : Real =>
            lVelocity (I := I) (fun u : Real => f u r) 0)
          tau (lVelocity (I := I) (fun u : Real => f u tau) 0)) =
      2 * lIndex S T gamma Y Y a b by
        simpa only [gamma, Y] using hcoef] at hsecond
  simpa only [gamma, Y] using hsecond

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
