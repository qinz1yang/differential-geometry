import DifferentialGeometry.Geometry.Comparison.Variation.TwistedEnergy
import DifferentialGeometry.Geometry.Comparison.Variation.GeodesicEndpoints

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem exists_minimizer_excluding_positive_parallel_twisted_variations
    (g : SmoothRiemannianMetric I M) (F : M → M) (hF : Continuous F)
    (hfree : ∀ x, F x ≠ x) :
    ∃ (L : ℝ) (γ : ℝ → M), 0 < L ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
      IsGeodesic (I := I) g γ ∧ IsTwistedPath F L γ ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      ∀ (ε : ℝ) (f : ℝ × ℝ → M), 0 < ε → ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ f →
        IsTwistedVariation F L ε (fun s t => f (s, t)) → (fun t => f (0, t)) = γ →
        HasGeodesicEquationAt (I := I) g (fun s => f (s, 0)) 0 →
        HasGeodesicEquationAt (I := I) g (fun s => f (s, L)) 0 →
        (∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g (fun t => f (0, t))
          (centralVariationField (I := I) (fun s t => f (s, t))) t = 0) →
        (∀ t ∈ Icc (0 : ℝ) L, 0 < centralCurvatureDensity (I := I) g (fun s t => f (s, t)) t) →
        False := by
  obtain ⟨L, γ, hL, hγ, hgeo, htwist, hspeed, _, htest⟩ :=
    exists_minimal_twisted_geodesic_with_derivative_test g F hF hfree
  refine ⟨L, γ, hL, hγ, hgeo, htwist, hspeed, ?_⟩
  intro ε f hε hf htw hcenter h0 h1 hpar hpos
  have hnonneg := (htest ε f univ hε isOpen_univ (subset_univ _)
    hf.contMDiffOn htw hcenter).2
  have hs : IsSmoothVariation (I := I) (fun s t => f (s, t)) := by
    unfold IsSmoothVariation
    have hh : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) f := hf.of_le (by decide)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hc : IsGeodesicOn (I := I) g (fun t => f (0, t)) (Icc 0 L) := by
    rw [hcenter]
    exact hgeo.isGeodesicOn _
  exact (not_lt_of_ge hnonneg)
    (secondVariation_curveEnergy_neg_of_parallel_geodesicEndpoints g (fun s t => f (s, t)) L
      hs hL hc h0 h1 hpar hpos)

end DifferentialGeometry.Geometry.Riemannian.Variation
