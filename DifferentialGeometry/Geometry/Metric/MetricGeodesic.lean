import DifferentialGeometry.Geometry.Metric.ShortGeodesicBounds








noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace


def metricShortGeodesic (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : M → M → ℝ → M :=
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
  shortGeodesic g hg



theorem metricShortGeodesic_spec (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    (∀ x y, metricShortGeodesic g x y 0 = x) ∧
    (∀ x y, riemannianEDistOf g x y ≠ ⊤ → metricShortGeodesic g x y 1 = y) ∧
    (∀ x t, metricShortGeodesic g x x t = x) ∧
    (∀ x y, riemannianEDistOf g x y ≠ ⊤ → ∀ t,
      Real.sqrt (g.inner (metricShortGeodesic g x y t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (metricShortGeodesic g x y) t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (metricShortGeodesic g x y) t 1)) =
          (riemannianEDistOf g x y).toReal) ∧
    ∃ (ρ : ℝ≥0) (W : Set (ℝ × (M × M))), 0 < ρ ∧ IsOpen W ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
        riemannianEDistOf g x y ≤ (ρ : ℝ≥0∞) → (t, (x, y)) ∈ W) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, E) ∞
        (fun p : ℝ × (M × M) => metricShortGeodesic g p.2.1 p.2.2 p.1) W := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
  exact ⟨shortGeodesic_zero g hg, fun _ _ h => shortGeodesic_one g hg h,
    shortGeodesic_self g hg, fun _ _ h t => shortGeodesic_speed g hg h t,
    exists_uniform_smooth_shortGeodesic g hg⟩

end DifferentialGeometry.Geometry
