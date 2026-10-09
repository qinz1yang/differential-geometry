import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativity
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointGerms
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.MovingEndpointSecondVariation
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Minimizer
import DifferentialGeometry.Geometry.Comparison.Variation.Field.Realization
set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section finiteFamily

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff _root_.Topology BigOperators

universe uι uM uE uH

variable {ι : Type uι} [Fintype ι]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
  {D : ι → RealTimeInterval}

theorem sum_lRegularizedIndex_nonneg_of_isLocalMin_sum_action
    (S : (i : ι) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ) (a b : ι → ℝ)
    (f : (i : ι) → ℝ → ℝ → M i)
    (hf : ∀ i, IsSmoothVariation (I := I) (f i))
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (f i 0) (uIcc (a i) (b i)))
    (hmin : IsLocalMin
      (fun e => ∑ i, lRegularizedAction (S i) T (f i e) (a i) (b i)) 0)
    (hboundary : (∑ i,
      (((S i).base.metric (T - (b i) ^ 2)).inner (f i 0 (b i))
        (covDerivAlong (I := I) ((S i).base.metric (T - (b i) ^ 2))
          (fun e => f i e (b i))
          (fun e => lVelocity (I := I) (fun z => f i z (b i)) e) 0)
        (lVelocity (I := I) (f i 0) (b i)) -
      ((S i).base.metric (T - (a i) ^ 2)).inner (f i 0 (a i))
        (covDerivAlong (I := I) ((S i).base.metric (T - (a i) ^ 2))
          (fun e => f i e (a i))
          (fun e => lVelocity (I := I) (fun z => f i z (a i)) e) 0)
        (lVelocity (I := I) (f i 0) (a i)))) = 0) :
    0 ≤ ∑ i, lRegularizedIndex (S i) T (f i 0)
      (fun r => lVelocity (I := I) (fun e => f i e r) 0)
      (fun r => lVelocity (I := I) (fun e => f i e r) 0) (a i) (b i) := by
  let L (i : ι) (e : ℝ) := lRegularizedAction (S i) T (f i e) (a i) (b i)
  let Q (i : ι) := lRegularizedIndex (S i) T (f i 0)
    (fun r => lVelocity (I := I) (fun e => f i e r) 0)
    (fun r => lVelocity (I := I) (fun e => f i e r) 0) (a i) (b i)
  let A (i : ι) (r : ℝ) := ((S i).base.metric (T - r ^ 2)).inner (f i 0 r)
    (covDerivAlong (I := I) ((S i).base.metric (T - r ^ 2))
      (fun e => f i e r) (fun e => lVelocity (I := I) (fun z => f i z r) e) 0)
    (lVelocity (I := I) (f i 0) r)
  let F (e : ℝ) := ∑ i, L i e
  have hC (i : ι) : ContDiff ℝ 2 (L i) :=
    contDiff_lRegularizedAction (S i) (hS i) T (f i) (hf i) (a i) (b i)
      (fun r hr => (hgeo i r hr).1)
  have hDiff (i : ι) (e : ℝ) : DifferentiableAt ℝ (L i) e :=
    (hC i).differentiable (by norm_num) e
  have hfirst : HasDerivAt F (∑ i, deriv (L i) 0) 0 :=
    HasDerivAt.fun_sum (fun i _ => (hDiff i 0).hasDerivAt)
  have hfirst0 : HasDerivAt F 0 0 :=
    hfirst.congr_deriv (hmin.hasDerivAt_eq_zero hfirst)
  have hderiv : deriv F = fun e => ∑ i, deriv (L i) e := by
    funext e
    exact deriv_fun_sum (fun i _ => hDiff i e)
  have hsecond (i : ι) :
      HasDerivAt (deriv (L i)) (2 * Q i + A i (b i) - A i (a i)) 0 :=
    lRegularizedAction_second_variation_moving_endpoints
      (S i) (hS i) T (f i) (hf i) (a i) (b i) (hgeo i)
  have hsum : HasDerivAt (deriv F)
      (∑ i, (2 * Q i + A i (b i) - A i (a i))) 0 := by
    rw [hderiv]
    exact HasDerivAt.fun_sum (fun i _ => hsecond i)
  have hsum_eq : (∑ i, (2 * Q i + A i (b i) - A i (a i))) = 2 * ∑ i, Q i := by
    calc
      (∑ i, (2 * Q i + A i (b i) - A i (a i))) =
          (∑ i, (2 * Q i + (A i (b i) - A i (a i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * (∑ i, Q i) + ∑ i, (A i (b i) - A i (a i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * ∑ i, Q i := by rw [hboundary]; ring
  have hnonneg := second_deriv_nonneg_of_isLocalMin hmin hfirst0
    (hsum.congr_deriv hsum_eq)
  change 0 ≤ ∑ i, Q i
  linarith

end finiteFamily

end DifferentialGeometry.PDE.RicciFlow.Perelman
