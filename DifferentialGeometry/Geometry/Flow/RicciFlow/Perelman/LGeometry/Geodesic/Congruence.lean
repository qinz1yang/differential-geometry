import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsLRegularizedGeodesicOn.congr_of_eventuallyEq
    {S : SolutionOn (I := I) (M := M) D} {T : ℝ}
    {alpha beta : ℝ → M} {J : Set ℝ}
    (ha : IsLRegularizedGeodesicOn S T alpha J)
    (heq : ∀ r ∈ J, beta =ᶠ[𝓝 r] alpha) :
    IsLRegularizedGeodesicOn S T beta J := by
  intro r hr
  have heq := heq r hr
  have hvel : ∀ᶠ t in 𝓝 r,
      lVelocity (I := I) beta t = lVelocity (I := I) alpha t := by
    filter_upwards [heq.eventuallyEq_nhds] with t ht
    unfold lVelocity
    rw [ht.mfderiv_eq]
    rfl
  have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
    (fun t => lVelocity (I := I) beta t) (fun t => lVelocity (I := I) alpha t)
    heq hvel
  have hacc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (S.base.metric (T - r ^ 2))
    (fun t => lVelocity (I := I) beta t) (fun t => lVelocity (I := I) alpha t)
    heq hvel
  have h := ha r hr
  refine ⟨h.1, h.2.1.congr_of_eventuallyEq heq, ?_, ?_⟩
  · exact h.2.2.1.congr_of_eventuallyEq hrep
  · rw [hacc, h.2.2.2, heq.eq_of_nhds, hvel.self_of_nhds]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D₁ D₂ : RealTimeInterval}

theorem IsLRegularizedGeodesicOn.congr_metric
    {S₁ : SolutionOn (I := I) (M := M) D₁} {S₂ : SolutionOn (I := I) (M := M) D₂}
    {T : ℝ} {α : ℝ → M} {J : Set ℝ}
    (hα : IsLRegularizedGeodesicOn S₁ T α J)
    (hregular : ∀ s ∈ J, T - s ^ 2 ∈ D₂.regular)
    (hmetric : ∀ s ∈ J, S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) :
    IsLRegularizedGeodesicOn S₂ T α J := by
  intro s hs
  have h := hα s hs
  refine ⟨hregular s hs, h.2.1, h.2.2.1, ?_⟩
  have heq : lRegularizedAccel S₁ T s (α s) (lVelocity (I := I) α s) =
      lRegularizedAccel S₂ T s (α s) (lVelocity (I := I) α s) := by
    have hscalar : S₁.scalar (T - s ^ 2) = S₂.scalar (T - s ^ 2) := by
      change (fun x => metricScalarAt (S₁.base.metric (T - s ^ 2)) x) =
        (fun x => metricScalarAt (S₂.base.metric (T - s ^ 2)) x)
      rw [hmetric s hs]
    simp only [lRegularizedAccel, hmetric s hs, hscalar]
  rw [← hmetric s hs, ← heq]
  exact h.2.2.2

theorem IsLRegularizedCurveOn.congr_metric
    {S₁ : SolutionOn (I := I) (M := M) D₁} {S₂ : SolutionOn (I := I) (M := M) D₂}
    {T : ℝ} {α : ℝ → M} {J : Set ℝ} {x : M} {Z : TangentSpace I x}
    (hα : IsLRegularizedCurveOn S₁ T α J x Z)
    (hregular : ∀ s ∈ J, T - s ^ 2 ∈ D₂.regular)
    (hmetric : ∀ s ∈ J, S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2)) :
    IsLRegularizedCurveOn S₂ T α J x Z :=
  ⟨hα.1, hα.2.1, hα.2.2.congr_metric hregular hmetric⟩

theorem mem_lRegularizedDomain_and_curve_eq_of_metric_eqOn
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂) (hS₂ : IsSolutionOn S₂)
    (T : ℝ) (x : M) (Z : TangentSpace I x)
    {J : Set ℝ} (hJ : IsOpen J) (hJconn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hregular : ∀ s ∈ J, T - s ^ 2 ∈ D₂.regular)
    (hmetric : ∀ s ∈ J, S₁.base.metric (T - s ^ 2) = S₂.base.metric (T - s ^ 2))
    {s : ℝ} (hsJ : s ∈ J) (hs : s ∈ lRegularizedDomain S₁ T x Z) :
    s ∈ lRegularizedDomain S₂ T x Z ∧
      lRegularizedCurve S₂ T x Z s = lRegularizedCurve S₁ T x Z s := by
  obtain ⟨K, hK, hKconn, h0K, hsK, hα⟩ := lRegularizedChosen_spec S₁ T x Z hs
  have hKI : IsOpen (K ∩ J) := hK.inter hJ
  have hKIconn : IsPreconnected (K ∩ J) :=
    (hKconn.ordConnected.inter hJconn.ordConnected).isPreconnected
  have h0KI : (0 : ℝ) ∈ K ∩ J := ⟨h0K, h0J⟩
  have hsKI : s ∈ K ∩ J := ⟨hsK, hsJ⟩
  have hαI : IsLRegularizedCurveOn S₁ T (lRegularizedChosen S₁ T x Z hs) (K ∩ J) x Z :=
    ⟨hα.1, hα.2.1, fun q hq => hα.2.2 q hq.1⟩
  have hβ := hαI.congr_metric (fun q hq => hregular q hq.2) (fun q hq => hmetric q hq.2)
  refine ⟨⟨lRegularizedChosen S₁ T x Z hs, K ∩ J, hKI, hKIconn, h0KI, hsKI, hβ⟩, ?_⟩
  exact (lRegularizedCurve_eqOn S₂ hS₂ T hKI hKIconn h0KI hβ hsKI).trans
    (lRegularizedCurve_of_mem hs).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
