import DifferentialGeometry.Geometry.Comparison.Variation.IntervalNormBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedIntervalExtension


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped ContDiff Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_lRegularizedGeodesic_interval_variation_norm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval},
      ∀ (S : SolutionOn (I := I) (M := M) D),
      IsSolutionOn (I := I) S → ∀ (g : SmoothRiemannianMetric I M) (T : ℝ)
      (alpha beta : ℝ → M) (c b : ℝ), 0 < c → c < b →
      IsLRegularizedGeodesicOn S T alpha (Ioc 0 b) →
      IsGeodesicAt (I := I) g beta 0 →
      beta 0 = alpha b →
      ∃ f : ℝ → ℝ → M,
        IsSmoothVariation (I := I) f ∧
        EqOn (f 0) alpha (Icc c b) ∧
        IsLRegularizedGeodesicOn S T (f 0) (Icc c b) ∧
        (∀ u, f u =ᶠ[𝓝 c] alpha) ∧
        (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta ∧
        lVelocity (I := I) (f 0) b = lVelocity (I := I) alpha b ∧
        ∃ chi : ℝ → ℝ, ContDiff ℝ ∞ chi ∧
          chi =ᶠ[𝓝 c] 0 ∧ chi b = 1 ∧
          (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧
        ∃ V : ∀ t, TangentSpace I (f 0 t),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (f 0 t) (V t) : TangentBundle I M)) ∧
          (∀ t ∈ Icc c b, covDerivAlong (I := I) g (f 0) V t = 0) ∧
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f 0 b) (V b) : TangentBundle I M) =
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) : TangentBundle I M) ∧
          (∀ t ∈ Icc c b,
            g.inner (f 0 t) (V t) (V t) =
              g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ∧
        let Y : ∀ t, TangentSpace I (f 0 t) :=
          fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
        (∀ t ∈ Icc c b, Y t = (chi t * ((t - c) / (b - c))) • V t) ∧
        (∀ t ∈ Icc c b,
          covDerivAlong (I := I) g (f 0) Y t =
            (deriv chi t * ((t - c) / (b - c)) + chi t / (b - c)) • V t) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤
            Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t)
            (covDerivAlong (I := I) g (f 0) Y t)
            (covDerivAlong (I := I) g (f 0) Y t)) ≤
            C / (b - c) * Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_smooth_interval_variation_with_geodesic_endpoint_norm_bounds
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H _ I _ M _ _ _ _ D S hS g T alpha beta c b hc hcb halpha hbeta hbeta0
  obtain ⟨gamma, hgamma, hgammaGeo, hgammaEq, hgammaGerms, hgammaVel⟩ :=
    exists_global_lRegularizedGeodesic_smooth_extension_on_Icc S hS T hc hcb halpha
  have hgammaGerm : gamma =ᶠ[𝓝 c] alpha := hgammaGerms c ⟨le_rfl, hcb⟩
  have hbmem : b ∈ Icc c b := ⟨hcb.le, le_rfl⟩
  have hbetaGamma : beta 0 = gamma b := hbeta0.trans (hgammaEq hbmem).symm
  obtain ⟨f, hf, hcenter, hfix, hterminal, chi, hchi, hchiGerm, hchiEnd,
      hchiRange, V, hVtotal, hVpar, hVterminal, hVnorm, hY, hDY, hYbound, hDYbound⟩ :=
    hproducer g gamma beta c b hcb hgamma hbeta hbetaGamma
  refine ⟨f, hf, ?_, ?_, ?_, hterminal, ?_, chi, hchi, hchiGerm, hchiEnd,
    hchiRange, V, hVtotal, hVpar, hVterminal, hVnorm, hY, hDY, hYbound, hDYbound⟩
  · intro t ht
    exact (hcenter t ht).self_of_nhds.trans (hgammaEq ht)
  · intro t ht
    exact lRegularizedData_congr S T t (hcenter t ht) (hgammaGeo t ht)
  · intro u
    exact (hfix u).trans hgammaGerm
  · unfold lVelocity at hgammaVel ⊢
    rw [(hcenter b hbmem).mfderiv_eq]
    exact hgammaVel

theorem exists_lRegularizedGeodesic_interval_variation_norm_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SolutionOn (I := I) (M := M) D),
      IsSolutionOn (I := I) S → ∀ (g : SmoothRiemannianMetric I M) (T : ℝ)
      (alpha beta : ℝ → M) (c b : ℝ), 0 < c → c < b →
      IsLRegularizedGeodesicOn S T alpha (Ioc 0 b) →
      IsGeodesicAt (I := I) g beta 0 →
      beta 0 = alpha b →
      ∃ f : ℝ → ℝ → M,
        IsSmoothVariation (I := I) f ∧
        EqOn (f 0) alpha (Icc c b) ∧
        IsLRegularizedGeodesicOn S T (f 0) (Icc c b) ∧
        (∀ u, f u =ᶠ[𝓝 c] alpha) ∧
        (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta ∧
        lVelocity (I := I) (f 0) b = lVelocity (I := I) alpha b ∧
        ∃ chi : ℝ → ℝ, ContDiff ℝ ∞ chi ∧
          chi =ᶠ[𝓝 c] 0 ∧ chi b = 1 ∧
          (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) ∧
        ∃ V : ∀ t, TangentSpace I (f 0 t),
          ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
            (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (f 0 t) (V t) : TangentBundle I M)) ∧
          (∀ t ∈ Icc c b, covDerivAlong (I := I) g (f 0) V t = 0) ∧
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f 0 b) (V b) : TangentBundle I M) =
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)) : TangentBundle I M) ∧
          (∀ t ∈ Icc c b,
            g.inner (f 0 t) (V t) (V t) =
              g.inner (beta 0) (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ∧
        let Y : ∀ t, TangentSpace I (f 0 t) :=
          fun t ↦ mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)
        (∀ t ∈ Icc c b, Y t = (chi t * ((t - c) / (b - c))) • V t) ∧
        (∀ t ∈ Icc c b,
          covDerivAlong (I := I) g (f 0) Y t =
            (deriv chi t * ((t - c) / (b - c)) + chi t / (b - c)) • V t) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t) (Y t) (Y t)) ≤
            Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) ∧
        (∀ t ∈ Icc c b,
          Real.sqrt (g.inner (f 0 t)
            (covDerivAlong (I := I) g (f 0) Y t)
            (covDerivAlong (I := I) g (f 0) Y t)) ≤
            C / (b - c) * Real.sqrt (g.inner (beta 0)
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)))) := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_lRegularizedGeodesic_interval_variation_norm_bounds
  exact ⟨C, hC, hproducer⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
