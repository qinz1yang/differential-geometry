import DifferentialGeometry.Analysis.Calculus.LipschitzConvolution
import Mathlib.Topology.MetricSpace.Lipschitz

open scoped ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem LipschitzOnWith.exists_contDiff_lipschitz_approx
    {f : E → ℝ} {s : Set E} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith C g ∧
      ∀ x ∈ s, dist (g x) (f x) < ε := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_real
  obtain ⟨g, hg, hgL, hlim⟩ := hF.exists_contDiff_lipschitz_tendstoUniformly
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp hlim ε hε).exists
  refine ⟨g n, hg n, hgL n, ?_⟩
  intro x hx
  rw [hEq hx]
  exact (dist_comm (g n x) (F x)).trans_lt (hn x)
