import DifferentialGeometry.Geometry.Connection.SourceSectionPairing



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem sourceSectionCovariantDerivative_parameter_slice
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℝ × A → M)
    (W : ∀ p, TangentSpace 𝓘(ℝ, E) (F p)) (t : ℝ) (z v : A) :
    sourceSectionCovariantDerivative g F W (t, z) (0, v) =
      sourceSectionCovariantDerivative g (fun q => F (t, q)) (fun q => W (t, q)) z v := by
  have hline : (fun r : ℝ => (t, z) + r • (0, v)) = (fun r => (t, z + r • v)) := by
    funext r
    ext <;> simp
  change Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong g
    (F ∘ (fun r : ℝ => (t, z) + r • (0, v)))
    (fun r => W ((fun r : ℝ => (t, z) + r • (0, v)) r)) 0 = _
  rw [hline]
  rfl



theorem sourceSectionCovariantDerivative_congr
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : A → M)
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)} {z : A}
    (h : ∀ᶠ q in 𝓝 z, W q = Z q) (v : A) :
    sourceSectionCovariantDerivative g U W z v = sourceSectionCovariantDerivative g U Z z v := by
  apply Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
  have hl : Tendsto (fun r : ℝ => z + r • v) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun r : ℝ => z + r • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto (0 : ℝ)
  exact hl.eventually h

end DifferentialGeometry.Geometry
