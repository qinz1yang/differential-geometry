import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PartialDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalIterCov
import DifferentialGeometry.Geometry.Operator.Gradient.PullbackAt
import DifferentialGeometry.Geometry.Operator.Hessian.IteratedCovariantDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Defs
import DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian (chartRep_congr_curve covDerivAlong_congr_curve)
open DifferentialGeometry.Tensor0SBundle

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D D' : RealTimeInterval}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [IsManifold J ∞ N] [T2Space N] in
theorem lVelocity_comp_of_isLocalDiffeomorph {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    {γ : ℝ → M} {s : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s) :
    lVelocity (I := J) (f ∘ γ) s = mfderiv I J f (γ s) (lVelocity (I := I) γ s) := by
  unfold lVelocity
  rw [mfderiv_comp s ((hf (γ s)).mdifferentiableAt (by simp)) hγ]
  rfl

omit [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless] [T2Space N] in
private theorem inner_localPullMetric_eq {g : SmoothRiemannianMetric I M}
    {h : SmoothRiemannianMetric J N} {f : M → N} {hf : IsLocalDiffeomorph I J ∞ f}
    (hg : g = localPullMetric h f hf) (x : M) (v w : TangentSpace I x) :
    h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = g.inner x v w := by
  rw [hg, localPullMetric_inner]

private theorem scalar_eq_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} {hf : IsLocalDiffeomorph I J ∞ f} {t : ℝ}
    (hg : S.base.metric t = localPullMetric (S'.base.metric t) f hf) :
    S.scalar t = S'.scalar t ∘ f := by
  funext y
  change metricScalarAt (S.base.metric t) y = metricScalarAt (S'.base.metric t) (f y)
  rw [hg, metricScalarAt_localPull]

private theorem ricciAt_eq_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} {hf : IsLocalDiffeomorph I J ∞ f} {t : ℝ}
    (hg : S.base.metric t = localPullMetric (S'.base.metric t) f hf)
    (x : M) (v w : TangentSpace I x) :
    S.ricciAt t x (vec2 v w) =
      S'.ricciAt t (f x) (vec2 (mfderiv I J f x v) (mfderiv I J f x w)) := by
  change metricRicciAt (S.base.metric t) x (vec2 v w) =
    metricRicciAt (S'.base.metric t) (f x) (vec2 (mfderiv I J f x v) (mfderiv I J f x w))
  rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor, hg,
    ricciTensor_localPull]

theorem mfderiv_lRegularizedAccel_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T s : ℝ}
    (hg : S.base.metric (T - s ^ 2) = localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (x : M) (A : TangentSpace I x) :
    mfderiv I J f x (lRegularizedAccel S T s x A) =
      lRegularizedAccel S' T s (f x) (mfderiv I J f x A) := by
  let g' := S'.base.metric (T - s ^ 2)
  have hsurj : Function.Surjective (mfderiv I J f x) := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hf.mfderivToContinuousLinearEquiv (by simp) x).surjective
  apply (metricFlatEquiv g' (f x)).injective
  ext Y'
  obtain ⟨Y, rfl⟩ := hsurj Y'
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, g'.symm, g'.symm (f x) _ (mfderiv I J f x Y),
    inner_localPullMetric_eq hg, lRegularizedAccel_inner, lRegularizedAccel_inner,
    inner_gradientFun, inner_gradientFun, scalar_eq_comp_of_localPullMetric S S' hg,
    mvfderiv_comp_apply x ((scalarSmoothOfSolution S' _).mdifferentiableAt (by simp))
      ((hf x).mdifferentiableAt (by simp)), ricciAt_eq_of_localPullMetric S S' hg]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [T2Space M] [T2Space N] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mdifferentiableAt_of_isLocalDiffeomorph_comp
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {γ : ℝ → M} {s : ℝ}
    (hγ : ContinuousAt γ s) (hfγ : MDifferentiableAt 𝓘(ℝ, ℝ) J (f ∘ γ) s) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := by
  obtain ⟨Φ, hx, hEq⟩ := hf (γ s)
  have hsrc : ∀ᶠ r in 𝓝 s, γ r ∈ Φ.source := hγ.preimage_mem_nhds (Φ.open_source.mem_nhds hx)
  have hΦγ : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun r => Φ (γ r)) s :=
    hfγ.congr_of_eventuallyEq (by
      filter_upwards [hsrc] with r hr
      exact (hEq hr).symm)
  have hsymm : MDifferentiableAt J I Φ.symm (Φ (γ s)) :=
    (Φ.symm.contMDiffOn_toFun.contMDiffAt
      (Φ.open_target.mem_nhds (Φ.map_source' hx))).mdifferentiableAt (by simp)
  refine (hsymm.comp s hΦγ).congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with r hr
  exact (Φ.left_inv' hr).symm

theorem IsLRegularizedGeodesicOn.comp_of_localPullMetric
    {S : SolutionOn (I := I) (M := M) D} {S' : SolutionOn (I := J) (M := N) D'}
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T : ℝ} {γ : ℝ → M} {K : Set ℝ}
    (hg : ∀ s ∈ K, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular → T - s ^ 2 ∈ D'.regular)
    (hγ : ∀ s ∈ K, ∀ᶠ r in 𝓝 s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r)
    (h : IsLRegularizedGeodesicOn S T γ K) :
    IsLRegularizedGeodesicOn S' T (f ∘ γ) K := by
  intro s hs
  obtain ⟨ht, hmd, hvel, hacc⟩ := h s hs
  have hvelEv : ∀ᶠ r in 𝓝 s, (lVelocity (I := J) (f ∘ γ) r : F) =
      mfderiv I J f (γ r) (lVelocity (I := I) γ r) := by
    filter_upwards [hγ s hs] with r hr
    rw [lVelocity_comp_of_isLocalDiffeomorph hf hr]
  refine ⟨hreg s hs ht, ((hf (γ s)).mdifferentiableAt (by simp)).comp s hmd, ?_, ?_⟩
  · exact (chartRep_congr_curve (I := J) _ _ (Eventually.of_forall fun _ => rfl)
      (hvelEv.mono fun _ h => h.symm)).differentiableAt_iff.mp
      (differentiableAt_chartRepAt_comp_of_isLocalDiffeomorph hf γ _ hmd hvel)
  · have hnat := mfderiv_covDerivAlong_of_isLocalDiffeomorph (S.base.metric (T - s ^ 2))
      (S'.base.metric (T - s ^ 2)) hf (inner_localPullMetric_eq (hg s hs)) γ
      (fun r => lVelocity (I := I) γ r) hmd hvel
    rw [hacc, mfderiv_lRegularizedAccel_of_localPullMetric S S' hf (hg s hs)] at hnat
    rw [lVelocity_comp_of_isLocalDiffeomorph hf hmd]
    exact ((covDerivAlong_congr_curve (I := J) _ _ _
      (Eventually.of_forall fun _ => rfl) hvelEv).trans hnat.symm)

theorem IsLRegularizedGeodesicOn.of_comp_localPullMetric
    {S : SolutionOn (I := I) (M := M) D} {S' : SolutionOn (I := J) (M := N) D'}
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T : ℝ} {γ : ℝ → M} {K : Set ℝ}
    (hg : ∀ s ∈ K, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D'.regular → T - s ^ 2 ∈ D.regular)
    (hγ : ∀ s ∈ K, ∀ᶠ r in 𝓝 s, ContinuousAt γ r)
    (hfγ : ∀ s ∈ K, ∀ᶠ r in 𝓝 s, MDifferentiableAt 𝓘(ℝ, ℝ) J (f ∘ γ) r)
    (h : IsLRegularizedGeodesicOn S' T (f ∘ γ) K) :
    IsLRegularizedGeodesicOn S T γ K := by
  intro s hs
  obtain ⟨ht, hmd, hvel, hacc⟩ := h s hs
  have hγd : ∀ᶠ r in 𝓝 s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r := by
    filter_upwards [hγ s hs, hfγ s hs] with r hr hr'
    exact mdifferentiableAt_of_isLocalDiffeomorph_comp hf hr hr'
  have hvelEv : ∀ᶠ r in 𝓝 s, (lVelocity (I := J) (f ∘ γ) r : F) =
      mfderiv I J f (γ r) (lVelocity (I := I) γ r) := by
    filter_upwards [hγd] with r hr
    rw [lVelocity_comp_of_isLocalDiffeomorph hf hr]
  have hγs : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := hγd.self_of_nhds
  have hW := (chartRep_congr_curve (I := J) _ _ (Eventually.of_forall fun _ => rfl)
    hvelEv).differentiableAt_iff.mp hvel
  have hvelγ := (mdifferentiableAt_and_differentiableAt_chartRepAt_of_isLocalDiffeomorph_comp
    hf γ (fun r => lVelocity (I := I) γ r) hγs.continuousAt hmd hW).2
  refine ⟨hreg s hs ht, hγs, hvelγ, ?_⟩
  have hnat := mfderiv_covDerivAlong_of_isLocalDiffeomorph (S.base.metric (T - s ^ 2))
    (S'.base.metric (T - s ^ 2)) hf (inner_localPullMetric_eq (hg s hs)) γ
    (fun r => lVelocity (I := I) γ r) hγs hvelγ
  have hcov := (covDerivAlong_congr_curve (I := J) (S'.base.metric (T - s ^ 2)) _ _
    (Eventually.of_forall fun _ => rfl) hvelEv).symm.trans hacc
  rw [lVelocity_comp_of_isLocalDiffeomorph hf hγs] at hcov
  change _ = lRegularizedAccel S' T s (f (γ s)) _ at hcov
  rw [← mfderiv_lRegularizedAccel_of_localPullMetric S S' hf (hg s hs)] at hcov
  have hinj : Function.Injective (mfderiv I J f (γ s)) := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hf.mfderivToContinuousLinearEquiv (by simp) (γ s)).injective
  exact hinj (hnat.trans hcov)

theorem isLRegularizedGeodesicOn_comp_iff_of_localPullMetric
    {S : SolutionOn (I := I) (M := M) D} {S' : SolutionOn (I := J) (M := N) D'}
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T : ℝ} {γ : ℝ → M} {K : Set ℝ}
    (hK : IsOpen K) (hγ : ContinuousOn γ K)
    (hg : ∀ s ∈ K, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular ↔ T - s ^ 2 ∈ D'.regular) :
    IsLRegularizedGeodesicOn S' T (f ∘ γ) K ↔ IsLRegularizedGeodesicOn S T γ K := by
  constructor
  · intro h
    refine h.of_comp_localPullMetric hf hg (fun s hs => (hreg s hs).2) (fun s hs => ?_)
      (fun s hs => ?_)
    · filter_upwards [hK.mem_nhds hs] with r hr
      exact hγ.continuousAt (hK.mem_nhds hr)
    · filter_upwards [hK.mem_nhds hs] with r hr
      exact (h r hr).2.1
  · intro h
    refine h.comp_of_localPullMetric hf hg (fun s hs => (hreg s hs).1) (fun s hs => ?_)
    filter_upwards [hK.mem_nhds hs] with r hr
    exact (h r hr).2.1

theorem IsLRegularizedCurveOn.comp_of_localPullMetric
    {S : SolutionOn (I := I) (M := M) D} {S' : SolutionOn (I := J) (M := N) D'}
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T : ℝ} {γ : ℝ → M} {K : Set ℝ}
    {x : M} {Z : TangentSpace I x} (hK : IsOpen K) (h0 : (0 : ℝ) ∈ K)
    (hg : ∀ s ∈ K, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular → T - s ^ 2 ∈ D'.regular)
    (h : IsLRegularizedCurveOn S T γ K x Z) :
    IsLRegularizedCurveOn S' T (f ∘ γ) K (f x) (mfderiv I J f x Z) := by
  obtain ⟨h0γ, hv0, hgeo⟩ := h
  refine ⟨by simp [h0γ], ?_, hgeo.comp_of_localPullMetric hf hg hreg fun s hs => ?_⟩
  · subst h0γ
    rw [lVelocity_comp_of_isLocalDiffeomorph hf (hgeo 0 h0).2.1, hv0]
    exact map_nsmul (mfderiv I J f (γ 0)) 2 Z
  · filter_upwards [hK.mem_nhds hs] with r hr
    exact (hgeo r hr).2.1

theorem lRegularizedAction_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T a b : ℝ} {γ : ℝ → M}
    (hg : ∀ s ∈ uIcc a b, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (hγ : ∀ s ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s) :
    lRegularizedAction S' T (f ∘ γ) a b = lRegularizedAction S T γ a b := by
  unfold lRegularizedAction
  refine intervalIntegral.integral_congr fun s hs => ?_
  simp only [lRegularizedLagrangian, lVelocity_comp_of_isLocalDiffeomorph hf (hγ s hs),
    inner_localPullMetric_eq (hg s hs), scalar_eq_comp_of_localPullMetric S S' (hg s hs),
    Function.comp_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] [T2Space N] in
private theorem vec2_map (f : M → N) (x : M) (u w : TangentSpace I x) :
    (fun i => mfderiv I J f x (vec2 u w i)) =
      vec2 (mfderiv I J f x u) (mfderiv I J f x w) := by
  funext i
  fin_cases i <;> rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] [T2Space N] in
private theorem vec3_map (f : M → N) (x : M) (u v w : TangentSpace I x) :
    (fun i => mfderiv I J f x (vec3 u v w i)) =
      vec3 (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) := by
  funext i
  fin_cases i <;> rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] [T2Space N] in
private theorem vec4_map (f : M → N) (x : M) (a b c d : TangentSpace I x) :
    (fun i => mfderiv I J f x (vec4 a b c d i)) =
      vec4 (mfderiv I J f x a) (mfderiv I J f x b) (mfderiv I J f x c)
        (mfderiv I J f x d) := by
  funext i
  fin_cases i <;> rfl

omit [I.Boundaryless] [J.Boundaryless] in
private theorem rm04_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} {hf : IsLocalDiffeomorph I J ∞ f} {t : ℝ}
    (hg : S.base.metric t = localPullMetric (S'.base.metric t) f hf)
    (x : M) (a b c d : TangentSpace I x) :
    S'.base.rm04 t (f x) (vec4 (mfderiv I J f x a) (mfderiv I J f x b)
      (mfderiv I J f x c) (mfderiv I J f x d)) = S.base.rm04 t x (vec4 a b c d) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  change metricRm04 (S'.base.metric t) (f x) _ = metricRm04 (S.base.metric t) x _
  rw [metricRm04_apply, metricRm04_apply, hg,
    DifferentialGeometry.Geometry.Tensor.metricRm04At_localPullMetric, vec4_map]

private theorem nablaRicci_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} {hf : IsLocalDiffeomorph I J ∞ f} {t : ℝ}
    (hg : S.base.metric t = localPullMetric (S'.base.metric t) f hf)
    (x : M) (u v w : TangentSpace I x) :
    totalNabla0SFun (𝕜 := ℝ) 2 (S'.base.connection t) (S'.ricci t) (f x)
        (vec3 (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w)) =
      totalNabla0SFun (𝕜 := ℝ) 2 (S.base.connection t) (S.ricci t) x (vec3 u v w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have key := DifferentialGeometry.Geometry.Tensor.iter_cov_localPullMetric
    (S'.base.metric t) f hf (r := 2) (metricRicci (localPullMetric (S'.base.metric t) f hf))
    (metricRicci (S'.base.metric t)) (fun y v => by
      rw [metricRicci_apply, metricRicci_apply]
      exact DifferentialGeometry.Geometry.Tensor.metricRicciAt_localPullMetric _ f hf y v)
    1 x (vec3 u v w)
  rw [← hg, vec3_map] at key
  exact key.symm

private theorem hessianScalar_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} {hf : IsLocalDiffeomorph I J ∞ f} {t : ℝ}
    (hg : S.base.metric t = localPullMetric (S'.base.metric t) f hf)
    (x : M) (u w : TangentSpace I x) :
    hessianSec (S'.base.connection t) (metricCov_smooth (S'.base.metric t)) (S'.scalar t)
        (scalarSmoothOfSolution S' t) (f x) (vec2 (mfderiv I J f x u) (mfderiv I J f x w)) =
      hessianSec (S.base.connection t) (metricCov_smooth (S.base.metric t)) (S.scalar t)
        (scalarSmoothOfSolution S t) x (vec2 u w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 2 N := IsManifold.of_le (n := ∞) (by decide)
  let g := S.base.metric t
  let g' := S'.base.metric t
  let A := DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField g (metricRicci g)
  let B := DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField g' (metricRicci g')
  have hA : ∀ y, A y Fin.elim0 = S.scalar t y := by
    intro y
    rw [DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField_apply,
      metricTraceFirstTwo0STensor_apply, traceFirstTwo_elim0, metricRicci_apply]
    rfl
  have hB : ∀ y, B y Fin.elim0 = S'.scalar t y := by
    intro y
    rw [DifferentialGeometry.Tensor.RSTensor.metricTraceFirstTwoField_apply,
      metricTraceFirstTwo0STensor_apply, traceFirstTwo_elim0, metricRicci_apply]
    rfl
  have hAB : ∀ (y : M) (v : Fin 0 → TangentSpace I y),
      A y v = B (f y) (fun i => mfderiv I J f y (v i)) := by
    intro y v
    rw [show v = Fin.elim0 from Subsingleton.elim _ _, hA,
      show (fun i => mfderiv I J f y ((Fin.elim0 : Fin 0 → TangentSpace I y) i)) = Fin.elim0
        from Subsingleton.elim _ _, hB, scalar_eq_comp_of_localPullMetric S S' hg]
    rfl
  have key := DifferentialGeometry.Geometry.Tensor.iter_cov_localPullMetric g' f hf A B hAB 2 x
    (vec2 u w)
  rw [← hg, vec2_map] at key
  have e1 := CanonicalNeighborhood.iterCov_zeroTensor_two_eq_hessianSec g A (S.scalar t)
    (scalarSmoothOfSolution S t) hA
  have e2 := CanonicalNeighborhood.iterCov_zeroTensor_two_eq_hessianSec g' B (S'.scalar t)
    (scalarSmoothOfSolution S' t) hB
  change hessianSec (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric g') _
      (S'.scalar t) _ (f x) _ =
    hessianSec (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric g) _
      (S.scalar t) _ x _
  rw [← e1, ← e2]
  exact key.symm

theorem lRegularizedIndexIntegrand_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T s : ℝ}
    (hg : S.base.metric (T - s ^ 2) = localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    {γ : ℝ → M} (Y W : ∀ r, TangentSpace I (γ r)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (hY : DifferentiableAt ℝ (chartRepAt (I := I) γ Y s) s)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) γ W s) s) :
    lRegularizedIndexIntegrand S' T (f ∘ γ) (fun r => mfderiv I J f (γ r) (Y r))
        (fun r => mfderiv I J f (γ r) (W r)) s =
      lRegularizedIndexIntegrand S T γ Y W s := by
  have hmet := inner_localPullMetric_eq hg
  have hDY : covDerivAlong (S'.base.metric (T - s ^ 2)) (f ∘ γ)
      (fun r => mfderiv I J f (γ r) (Y r)) s =
      mfderiv I J f (γ s) (covDerivAlong (S.base.metric (T - s ^ 2)) γ Y s) :=
    (mfderiv_covDerivAlong_of_isLocalDiffeomorph _ _ hf hmet γ Y hγ hY).symm
  have hDW : covDerivAlong (S'.base.metric (T - s ^ 2)) (f ∘ γ)
      (fun r => mfderiv I J f (γ r) (W r)) s =
      mfderiv I J f (γ s) (covDerivAlong (S.base.metric (T - s ^ 2)) γ W s) :=
    (mfderiv_covDerivAlong_of_isLocalDiffeomorph _ _ hf hmet γ W hγ hW).symm
  simp only [lRegularizedIndexIntegrand]
  rw [hDY, hDW, lVelocity_comp_of_isLocalDiffeomorph hf hγ, Function.comp_apply]
  change (1 / 2 : ℝ) * ((S'.base.metric (T - s ^ 2)).inner (f (γ s)) _ _ -
      S'.base.rm04 (T - s ^ 2) (f (γ s)) _) + _ + _ = _
  rw [hmet, rm04_of_localPullMetric S S' hg, hessianScalar_of_localPullMetric S S' hg,
    nablaRicci_of_localPullMetric S S' hg, nablaRicci_of_localPullMetric S S' hg,
    nablaRicci_of_localPullMetric S S' hg]

theorem lRegularizedIndex_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T a b : ℝ}
    {γ : ℝ → M} (Y W : ∀ r, TangentSpace I (γ r))
    (hg : ∀ s ∈ uIcc a b, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (hγ : ∀ s ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (hY : ∀ s ∈ uIcc a b, DifferentiableAt ℝ (chartRepAt (I := I) γ Y s) s)
    (hW : ∀ s ∈ uIcc a b, DifferentiableAt ℝ (chartRepAt (I := I) γ W s) s) :
    lRegularizedIndex S' T (f ∘ γ) (fun r => mfderiv I J f (γ r) (Y r))
        (fun r => mfderiv I J f (γ r) (W r)) a b =
      lRegularizedIndex S T γ Y W a b :=
  intervalIntegral.integral_congr fun s hs =>
    lRegularizedIndexIntegrand_comp_of_localPullMetric S S' hf (hg s hs) Y W (hγ s hs)
      (hY s hs) (hW s hs)

theorem HasLRegularizedJacobiAt.comp_of_localPullMetric
    {S : SolutionOn (I := I) (M := M) D} {S' : SolutionOn (I := J) (M := N) D'}
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T s : ℝ}
    (hg : S.base.metric (T - s ^ 2) = localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    {γ : ℝ → M} {Y : ∀ r, TangentSpace I (γ r)}
    (hY : ∀ᶠ r in 𝓝 s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r ∧
      DifferentiableAt ℝ (chartRepAt (I := I) γ Y r) r)
    (h : HasLRegularizedJacobiAt S T γ Y s) :
    HasLRegularizedJacobiAt S' T (f ∘ γ) (fun r => mfderiv I J f (γ r) (Y r)) s := by
  obtain ⟨hγ, hYs, hDY, hpair⟩ := h
  let g := S.base.metric (T - s ^ 2)
  let g' := S'.base.metric (T - s ^ 2)
  have hmet := inner_localPullMetric_eq hg
  have hDev : ∀ᶠ r in 𝓝 s, (covDerivAlong g' (f ∘ γ)
      (fun r => mfderiv I J f (γ r) (Y r)) r : F) =
      mfderiv I J f (γ r) (covDerivAlong g γ Y r) := by
    filter_upwards [hY] with r hr
    exact (mfderiv_covDerivAlong_of_isLocalDiffeomorph g g' hf hmet γ Y hr.1 hr.2).symm
  have hD2 : covDerivAlong g' (f ∘ γ)
      (fun r => covDerivAlong g' (f ∘ γ) (fun r => mfderiv I J f (γ r) (Y r)) r) s =
      mfderiv I J f (γ s) (covDerivAlong g γ (fun r => covDerivAlong g γ Y r) s) :=
    (covDerivAlong_congr_curve (I := J) g' _ _ (Eventually.of_forall fun _ => rfl) hDev).trans
      (mfderiv_covDerivAlong_of_isLocalDiffeomorph g g' hf hmet γ _ hγ hDY).symm
  have hsurj : Function.Surjective (mfderiv I J f (γ s)) := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hf.mfderivToContinuousLinearEquiv (by simp) (γ s)).surjective
  refine ⟨((hf (γ s)).mdifferentiableAt (by simp)).comp s hγ,
    differentiableAt_chartRepAt_comp_of_isLocalDiffeomorph hf γ Y hγ hYs, ?_, ?_⟩
  · exact (chartRep_congr_curve (I := J) _ _ (Eventually.of_forall fun _ => rfl)
      (hDev.mono fun _ h => h.symm)).differentiableAt_iff.mp
      (differentiableAt_chartRepAt_comp_of_isLocalDiffeomorph hf γ _ hγ hDY)
  · intro W'
    obtain ⟨W, rfl⟩ := hsurj W'
    rw [← hpair W]
    simp only [lRegularizedJacobiPair]
    rw [hD2, hDev.self_of_nhds, lVelocity_comp_of_isLocalDiffeomorph hf hγ, Function.comp_apply]
    change (S'.base.metric (T - s ^ 2)).inner (f (γ s)) _ _ + _ - _ + _ + _ = _
    rw [hmet, rm04_of_localPullMetric S S' hg, hessianScalar_of_localPullMetric S S' hg,
      nablaRicci_of_localPullMetric S S' hg, ← ricciAt_eq_of_localPullMetric S S' hg]

theorem IsLRegularizedJacobi.comp_of_localPullMetric
    {S : SolutionOn (I := I) (M := M) D} {S' : SolutionOn (I := J) (M := N) D'}
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T : ℝ} {γ : ℝ → M}
    {Y : ∀ r, TangentSpace I (γ r)} {K : Set ℝ} (hK : IsOpen K)
    (hg : ∀ s ∈ K, S.base.metric (T - s ^ 2) =
      localPullMetric (S'.base.metric (T - s ^ 2)) f hf)
    (h : IsLRegularizedJacobi S T γ Y K) :
    IsLRegularizedJacobi S' T (f ∘ γ) (fun r => mfderiv I J f (γ r) (Y r)) K := by
  intro s hs
  refine (h s hs).comp_of_localPullMetric hf (hg s hs) ?_
  filter_upwards [hK.mem_nhds hs] with r hr
  exact ⟨(h r hr).1, (h r hr).2.1⟩

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ F]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] in
theorem lGram_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T τ : ℝ}
    (hg : S.base.metric (T - τ) = localPullMetric (S'.base.metric (T - τ)) f hf)
    (γ : ℝ → M) (Y : ι → ∀ r, TangentSpace I (γ r)) :
    lGram S' T (f ∘ γ) (fun i r => mfderiv I J f (γ r) (Y i r)) τ = lGram S T γ Y τ := by
  ext i j
  exact inner_localPullMetric_eq hg _ _ _

omit [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless] [T2Space N] in
theorem lJacobianDensity_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T τ : ℝ}
    (hg : S.base.metric (T - τ) = localPullMetric (S'.base.metric (T - τ)) f hf)
    (γ : ℝ → M) (Y : ι → ∀ r, TangentSpace I (γ r)) :
    lJacobianDensity S' T (f ∘ γ) (fun i r => mfderiv I J f (γ r) (Y i r)) τ =
      lJacobianDensity S T γ Y τ := by
  unfold lJacobianDensity
  rw [lGram_comp_of_localPullMetric S S' hf hg]

omit [Fintype ι] [DecidableEq ι] in
theorem lGramDeriv_comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := J) (M := N) D')
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) {T τ : ℝ}
    (hg : S.base.metric (T - τ) = localPullMetric (S'.base.metric (T - τ)) f hf)
    {γ : ℝ → M} (Y : ι → ∀ r, TangentSpace I (γ r)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ τ)
    (hY : ∀ i, DifferentiableAt ℝ (chartRepAt (I := I) γ (Y i) τ) τ) :
    lGramDeriv S' T (f ∘ γ) (fun i r => mfderiv I J f (γ r) (Y i r)) τ =
      lGramDeriv S T γ Y τ := by
  have hmet := inner_localPullMetric_eq hg
  have hD (i : ι) : covDerivAlong (S'.base.metric (T - τ)) (f ∘ γ)
      (fun r => mfderiv I J f (γ r) (Y i r)) τ =
      mfderiv I J f (γ τ) (covDerivAlong (S.base.metric (T - τ)) γ (Y i) τ) :=
    (mfderiv_covDerivAlong_of_isLocalDiffeomorph _ _ hf hmet γ (Y i) hγ (hY i)).symm
  ext i j
  simp only [lGramDeriv, Matrix.of_apply]
  rw [hD i, hD j]
  change (S'.base.metric (T - τ)).inner (f (γ τ)) _ _ +
      (S'.base.metric (T - τ)).inner (f (γ τ)) _ _ +
      2 * S'.ricciAt (T - τ) (f (γ τ)) _ = _
  rw [hmet, hmet, ← ricciAt_eq_of_localPullMetric S S' hg]

end Gram

end DifferentialGeometry.PDE.RicciFlow.Perelman

section

open scoped Manifold ContDiff

variable {E H₁ H₂ M₁ M₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I₁ : ModelWithCorners ℝ E H₁} {I₂ : ModelWithCorners ℝ E H₂}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

theorem DifferentialGeometry.Integral.Measure.paramDensity_comp_of_inner_eq
    (g : SmoothRiemannianMetric I₁ M₁) (h : SmoothRiemannianMetric I₂ M₂)
    {f : M₁ → M₂} {Ψ : E → M₁} {w : E} (hf : MDifferentiableAt I₁ I₂ f (Ψ w))
    (hΨ : MDifferentiableAt 𝓘(ℝ, E) I₁ Ψ w)
    (hmet : ∀ v v' : TangentSpace I₁ (Ψ w),
      h.inner (f (Ψ w)) (mfderiv I₁ I₂ f (Ψ w) v) (mfderiv I₁ I₂ f (Ψ w) v') =
        g.inner (Ψ w) v v') :
    paramDensity h (f ∘ Ψ) w = paramDensity g Ψ w := by
  simp only [paramDensity_apply]
  congr 2
  ext i j
  have hc (v : E) : (mfderiv 𝓘(ℝ, E) I₂ (f ∘ Ψ) w v : E) =
      mfderiv I₁ I₂ f (Ψ w) (mfderiv 𝓘(ℝ, E) I₁ Ψ w v) := mfderiv_comp_apply w hf hΨ v
  exact (congrArg₂ (fun a b : E => h.inner (f (Ψ w)) a b) (hc _) (hc _)).trans (hmet _ _)

end
