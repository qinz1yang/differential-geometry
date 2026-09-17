import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.ComponentSubsequence

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem metricCovDeriv_component_tendsto_of_uniform_bounds
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf R : SmoothRiemannianMetric I M)
    (hbound : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : ℝ,
      ∀ k : ℕ, ∀ x ∈ K, metricCovDerivNorm q (gSeq k) R x ≤ C)
    (hinner : ∀ x : M, Tendsto (fun k => (gSeq k).inner x) atTop (𝓝 (gInf.inner x)))
    (q : ℕ) (x : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (slots : Fin (q + 2) → Fin (Module.finrank ℝ E)) :
    Tendsto (fun k => component0S basis (metricCovDeriv (gSeq k) R q x) slots)
      atTop (𝓝 (component0S basis (metricCovDeriv gInf R q x) slots)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  apply tendsto_of_subseq_tendsto
  intro rho hrho
  obtain ⟨tau, _, htau⟩ := componentConvergence_covDeriv_of_chartCInf R gSeq hbound
    rho gInf (fun x => (hinner x).comp hrho) q x basis slots
  exact ⟨tau, htau⟩

theorem metricCovDerivNorm_tendsto_of_uniform_bounds
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf R : SmoothRiemannianMetric I M)
    (hbound : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : ℝ,
      ∀ k : ℕ, ∀ x ∈ K, metricCovDerivNorm q (gSeq k) R x ≤ C)
    (hinner : ∀ x : M, Tendsto (fun k => (gSeq k).inner x) atTop (𝓝 (gInf.inner x)))
    (q : ℕ) (x : M) :
    Tendsto (fun k => metricCovDerivNorm q (gSeq k) R x) atTop
      (𝓝 (metricCovDerivNorm q gInf R x)) := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormal_basis R x
  have hinv := metricInverseInBasis_of_orthonormal R basis horth
  have hnorm (g : SmoothRiemannianMetric I M) :
      metricCovDerivNorm q g R x = Real.sqrt
        (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I x)),
          (component0S basis (metricCovDeriv g R q x) slots) ^ 2) := by
    rw [metricCovDerivNorm, normSq0S_identity_eq_sum_sq R x (q + 2) basis hinv]
  simp only [hnorm]
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  apply tendsto_finsetSum
  intro slots _
  exact (metricCovDeriv_component_tendsto_of_uniform_bounds gSeq gInf R hbound hinner
    q x basis slots).pow 2

end DifferentialGeometry.CheegerGromovCompactness
