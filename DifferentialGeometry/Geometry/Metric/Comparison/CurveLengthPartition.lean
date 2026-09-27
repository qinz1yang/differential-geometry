import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sum_toReal_riemannianEDistOf_le_arcLength (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) :
    (∑ i ∈ Finset.range n, (riemannianEDistOf g (γ (a i)) (γ (a (i + 1)))).toReal) ≤
      Geometry.Riemannian.Variation.arcLength g γ (a 0) (a n) := by
  let v : ℝ → TangentBundle I M := fun t =>
    ⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)⟩
  have hv : Continuous v :=
    (hγ.continuous_tangentMap le_rfl).comp
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const))
  let speed : ℝ → ℝ := fun t =>
    Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
  have hs : Continuous speed := ((metricQuad_cont g).comp hv).sqrt
  calc
    (∑ i ∈ Finset.range n, (riemannianEDistOf g (γ (a i)) (γ (a (i + 1)))).toReal)
        ≤ ∑ i ∈ Finset.range n, ∫ t in (a i)..(a (i + 1)), speed t := by
      apply Finset.sum_le_sum
      intro i _
      have hab : a i ≤ a (i + 1) := ha (Nat.le_succ i)
      have hdist := riemannianEDistOf_le_arcLength g hab hγ.contMDiffOn
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
      have hnonneg : 0 ≤ Geometry.Riemannian.Variation.arcLength g γ (a i) (a (i + 1)) :=
        intervalIntegral.integral_nonneg hab (fun t _ => Real.sqrt_nonneg _)
      rw [ENNReal.toReal_ofReal hnonneg] at h
      exact h
    _ = Geometry.Riemannian.Variation.arcLength g γ (a 0) (a n) :=
      intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hs.intervalIntegrable _ _)

end DifferentialGeometry
