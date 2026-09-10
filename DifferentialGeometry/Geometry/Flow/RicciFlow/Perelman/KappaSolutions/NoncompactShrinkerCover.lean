import DifferentialGeometry.Geometry.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance upstreamNoncompactShrinkerSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

private local instance upstreamNoncompactShrinkerC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem complete_noncompact_three_shrinker_universal_cover_fibres
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : isGradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0) :
    ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M,
      (∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w + a * b) ∧
      ((∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔ q = p) ∨
        (∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, p.2)) ∨
        (∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, -p.2))) := by
  sorry

theorem complete_noncompact_three_shrinker_universal_cover_cylinder
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : isGradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0) :
    ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M,
      ∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w + a * b := by
  obtain ⟨Psi, hmetric, _⟩ := complete_noncompact_three_shrinker_universal_cover_fibres
    g f hsigma hdim hcomplete hsoliton hnonflat
  exact ⟨Psi, hmetric⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
