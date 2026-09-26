import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedIntervalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D : RealTimeInterval}

theorem lRegularizedAccel_localPullback
    (S : SolutionOn (I := J) (M := N) D) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (T s : ℝ) (x : M) (A : TangentSpace I x) :
    mfderiv I J f x (lRegularizedAccel (S.localPullback f hf) T s x A) =
      lRegularizedAccel S T s (f x) (mfderiv I J f x A) := by
  let t := T - s ^ 2
  let g := S.base.metric t
  let SP := S.localPullback f hf
  let d := hf.mfderivToContinuousLinearEquiv (by simp) x
  let Yback : TangentSpace J (f x) → TangentSpace I x := d.symm
  have hY (Y : TangentSpace J (f x)) : mfderiv I J f x (Yback Y) = Y := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact d.apply_symm_apply Y
  have hscalar : SP.scalar t = S.scalar t ∘ f := by
    funext y
    exact S.localPullback_scalar f hf t y
  have hgrad : mfderiv I J f x (gradientFun (localPullMetric g f hf) (SP.scalar t) x) =
      gradientFun g (S.scalar t) (f x) := by
    rw [hscalar, gradientFun_localPull g f hf (S.scalar t) x
      ((scalarSmoothOfSolution S t).contMDiffAt.mdifferentiableAt (by simp))]
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact d.apply_symm_apply _
  have hric (Y : TangentSpace J (f x)) : SP.ricciAt t x (vec2 (Yback Y) A) =
      S.ricciAt t (f x) (vec2 Y (mfderiv I J f x A)) := by
    change metricRicciAt (localPullMetric g f hf) x (vec2 (Yback Y) A) =
      metricRicciAt g (f x) (vec2 Y (mfderiv I J f x A))
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor,
      ricciTensor_localPull, hY]
  apply (metricFlatEquiv g (f x)).injective
  ext Y
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply]
  calc
    g.inner (f x) (mfderiv I J f x (lRegularizedAccel SP T s x A)) Y =
        g.inner (f x) Y (mfderiv I J f x (lRegularizedAccel SP T s x A)) := g.symm _ _ _
    _ = (SP.base.metric t).inner x (Yback Y) (lRegularizedAccel SP T s x A) := by
      change _ = (localPullMetric g f hf).inner x (Yback Y) (lRegularizedAccel SP T s x A)
      rw [localPullMetric_inner, hY]
    _ = 2 * s ^ 2 * (SP.base.metric t).inner x (gradientFun (SP.base.metric t) (SP.scalar t) x) (Yback Y) -
        4 * s * SP.ricciAt t x (vec2 (Yback Y) A) := by
      exact lRegularizedAccel_inner SP T s x A (Yback Y)
    _ = 2 * s ^ 2 * g.inner (f x) (gradientFun g (S.scalar t) (f x)) Y -
        4 * s * S.ricciAt t (f x) (vec2 Y (mfderiv I J f x A)) := by
      change 2 * s ^ 2 * (localPullMetric g f hf).inner x
        (gradientFun (localPullMetric g f hf) (SP.scalar t) x) (Yback Y) - _ = _
      rw [localPullMetric_inner, hgrad, hY, hric]
    _ = g.inner (f x) Y (lRegularizedAccel S T s (f x) (mfderiv I J f x A)) :=
      (lRegularizedAccel_inner S T s (f x) (mfderiv I J f x A) Y).symm
    _ = g.inner (f x) (lRegularizedAccel S T s (f x) (mfderiv I J f x A)) Y := g.symm _ _ _

theorem IsLRegularizedGeodesicOn.comp_of_localPullMetric
    {D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (Q : SolutionOn (I := J) (M := N) D') (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    {T : ℝ} {α : ℝ → M} {K : Set ℝ} (hK : IsOpen K)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hclock : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    (hα : IsLRegularizedGeodesicOn S T α K) :
    IsLRegularizedGeodesicOn Q T (f ∘ α) K := by
  intro r hr
  have hαsmooth : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ α r :=
    (hα.contMDiffOn hS hK).contMDiffAt (hK.mem_nhds hr)
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) J ∞ (f ∘ α) r :=
    hf.contMDiff.contMDiffAt.comp r hαsmooth
  have hvelocity : lVelocity (I := J) (f ∘ α) r =
      mfderiv I J f (α r) (lVelocity (I := I) α r) := by
    unfold lVelocity
    rw [mfderiv_comp r (hf.contMDiff.mdifferentiableAt (by simp))
      (hα r hr).2.1]
    rfl
  refine ⟨hclock r hr, hcomp.mdifferentiableAt (by simp), ?_, ?_⟩
  · exact differentiableAt_chartRepAt_curveVelocity (hcomp.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  · have hnat := covDerivAlong_velocity_map_of_local_isometry_on
      (S.base.metric (T - r ^ 2)) (Q.base.metric (T - r ^ 2)) isOpen_univ
      (hf.isLocalDiffeomorphOn (s := univ))
      (fun x _ v w => by rw [hmetric r hr, localPullMetric_inner]) α (mem_univ _) hαsmooth
    have hacc : lRegularizedAccel S T r (α r) (lVelocity α r) =
        lRegularizedAccel (Q.localPullback f hf) T r (α r) (lVelocity α r) := by
      unfold lRegularizedAccel SolutionOn.scalar SolutionFamily.scalar
      rw [hmetric r hr]
      rfl
    change mfderiv I J f (α r)
      (covDerivAlong (S.base.metric (T - r ^ 2)) α (fun t => lVelocity α t) r) =
      covDerivAlong (Q.base.metric (T - r ^ 2)) (f ∘ α) (fun t => lVelocity (I := J) (f ∘ α) t) r at hnat
    rw [(hα r hr).2.2.2, hacc, lRegularizedAccel_localPullback, ← hvelocity] at hnat
    exact hnat.symm

theorem IsLRegularizedCurveOn.comp_of_localPullMetric
    {D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (Q : SolutionOn (I := J) (M := N) D') (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    {T : ℝ} {α : ℝ → M} {K : Set ℝ} (hK : IsOpen K) (hzero : (0 : ℝ) ∈ K)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hclock : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    {x : M} {Z : TangentSpace I x} (hα : IsLRegularizedCurveOn S T α K x Z) :
    IsLRegularizedCurveOn Q T (f ∘ α) K (f x) (mfderiv I J f x Z) := by
  refine ⟨congrArg f hα.1, ?_, hα.2.2.comp_of_localPullMetric S hS Q f hf hK hmetric hclock⟩
  have hvelocity : lVelocity (I := J) (f ∘ α) 0 =
      mfderiv I J f (α 0) (lVelocity (I := I) α 0) := by
    unfold lVelocity
    rw [mfderiv_comp 0 (hf.contMDiff.mdifferentiableAt (by simp)) (hα.2.2 0 hzero).2.1]
    rfl
  rw [hvelocity, hα.2.1, hα.1]
  exact map_nsmul (mfderiv I J f x) 2 Z

theorem lRegularizedCurve_eqOn_comp_of_localPullMetric
    {D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (Q : SolutionOn (I := J) (M := N) D') (hQ : IsSolutionOn Q)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    {T : ℝ} {α : ℝ → M} {K : Set ℝ} (hK : IsOpen K) (hconn : IsPreconnected K)
    (hzero : (0 : ℝ) ∈ K)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hclock : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    {x : M} {Z : TangentSpace I x} (hα : IsLRegularizedCurveOn S T α K x Z) :
    K ⊆ lRegularizedDomain Q T (f x) (mfderiv I J f x Z) ∧
      EqOn (lRegularizedCurve Q T (f x) (mfderiv I J f x Z)) (f ∘ α) K := by
  have hmap := hα.comp_of_localPullMetric S hS Q f hf hK hzero hmetric hclock
  refine ⟨fun r hr => ⟨f ∘ α, K, hK, hconn, hzero, hr, hmap⟩, ?_⟩
  exact lRegularizedCurve_eqOn Q hQ T hK hconn hzero hmap

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff
variable {A E F H G X Y : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 [TopologicalSpace H] [TopologicalSpace G]
 {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
 [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
 [TopologicalSpace Y] [ChartedSpace G Y] [IsManifold J ∞ Y] [T2Space Y]
 {D D' : RealTimeInterval}

theorem lRegularizedGeodesicFamily_eqOn_of_localPullMetric
    (S : SolutionOn (I := I) (M := X) D) (hS : IsSolutionOn S)
    (Q : SolutionOn (I := J) (M := Y) D') (hQ : IsSolutionOn Q)
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (T : ℝ)
    {α : A × ℝ → Y} {β : A × ℝ → X} {U : Set A} {K : Set ℝ} {t0 : ℝ}
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht0 : t0 ∈ K)
    (hβ : ∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (a, r)) K)
    (hα : ∀ a ∈ U, IsLRegularizedGeodesicOn Q T (fun r => α (a, r)) K)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hclock : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    (hpos : ∀ a ∈ U, f (β (a, t0)) = α (a, t0))
    (hvel : ∀ a ∈ U, mfderiv I J f (β (a, t0))
      (lVelocity (I := I) (fun r => β (a, r)) t0) = lVelocity (I := J) (fun r => α (a, r)) t0) :
    EqOn (fun p : A × ℝ => f (β p)) α (U ×ˢ K) := by
  rintro ⟨a, r⟩ ⟨ha, hr⟩
  have hmap := (hβ a ha).comp_of_localPullMetric S hS Q f hf hK hmetric hclock
  have hphase : lVelocity (I := J) (f ∘ (fun r => β (a, r))) t0 =
      lVelocity (I := J) (fun r => α (a, r)) t0 := by
    unfold lVelocity
    rw [mfderiv_comp t0 ((hf _).contMDiffAt.mdifferentiableAt (by simp)) (hβ a ha t0 ht0).2.1]
    exact hvel a ha
  have heq := lRegularizedSolution_eqOn Q hQ T hK hconn ht0 hK hconn ht0 hmap
    (hα a ha) (hpos a ha) hphase
  exact heq ⟨hr, hr⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
