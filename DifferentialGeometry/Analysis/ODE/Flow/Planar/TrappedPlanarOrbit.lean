import DifferentialGeometry.Analysis.ODE.Flow.Planar.PlanarFlowBox
import DifferentialGeometry.Topology.Flow.TransverseReturns

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem exists_transverse_returns_of_frequent_visits
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ x t, HasDerivAt (fun s ↦ φ s x) (v (φ t x)) t)
    {K : Set ℂ} (hK : IsCompact K) (hnz : ∀ x ∈ K, v x ≠ 0)
    {z : ℂ} (hfreq : ∃ᶠ t in atTop, φ t z ∈ K) :
    ∃ x ∈ K, ∃ ε > 0, ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, e p = φ p.2 (x + p.1 • (Complex.I * v x))) ∧
      ∀ T : ℝ, ∃ t ≥ T, ∃ u ∈ Ioo (-ε) ε,
        φ t z = x + u • (Complex.I * v x) := by
  obtain ⟨x, hx, hcluster⟩ := hK.exists_mapClusterPt_of_frequently hfreq
  obtain ⟨ε, hε, e, hsource, he, heinv, heq⟩ :=
    exists_smooth_planar_flowBox φ hv hderiv (hnz x hx)
  have hzero : e (0, 0) = x := by
    rw [heq]
    simp only [zero_smul, add_zero, φ.map_zero_apply]
  have hxTarget : x ∈ e.target := hzero ▸ e.map_source (by
    rw [hsource]
    exact ⟨⟨neg_neg_of_pos hε, hε⟩, ⟨neg_neg_of_pos hε, hε⟩⟩)
  have hvisits : ∀ T : ℝ, ∃ t ≥ T, φ t z ∈ e.target :=
    frequently_atTop.mp (mapClusterPt_iff_frequently.mp hcluster e.target
      (e.open_target.mem_nhds hxTarget))
  exact ⟨x, hx, ε, hε, e, hsource, he, heinv, heq,
    DifferentialGeometry.Topology.Flow.exists_transverse_hit_after φ e hsource heq hvisits⟩

theorem exists_transverse_returns_of_trapped_orbit
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ x t, HasDerivAt (fun s ↦ φ s x) (v (φ t x)) t)
    {K : Set ℂ} (hK : IsCompact K) (hnz : ∀ x ∈ K, v x ≠ 0)
    {z : ℂ} (hstay : ∀ t ≥ 0, φ t z ∈ K) :
    ∃ x ∈ K, ∃ ε > 0, ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, e p = φ p.2 (x + p.1 • (Complex.I * v x))) ∧
      ∀ T : ℝ, ∃ t ≥ T, ∃ u ∈ Ioo (-ε) ε,
        φ t z = x + u • (Complex.I * v x) := by
  exact exists_transverse_returns_of_frequent_visits φ hv hderiv hK hnz
    (((eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ hstay t ht)).frequently)

end DifferentialGeometry.Analysis
