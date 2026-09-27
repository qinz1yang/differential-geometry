import DifferentialGeometry.Analysis.ODE.Flow.Planar.PlanarTransverseNonreturn
import DifferentialGeometry.Analysis.ODE.Flow.Planar.TrappedPlanarOrbit

open Set Filter
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem eventually_not_mem_isCompact
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    {K : Set ℂ} (hK : IsCompact K) (z : ℂ) :
    ∀ᶠ t in atTop, φ t z ∉ K := by
  by_contra h
  obtain ⟨x, _, ε, _, e, hsource, _, _, he, hreturns⟩ :=
    exists_transverse_returns_of_frequent_visits φ hv hderiv hK (fun x _ ↦ hnz x) h
  let σ : ℝ →ᵃ[ℝ] ℂ := AffineMap.const ℝ ℝ x +
    (LinearMap.toSpanSingleton ℝ ℂ (Complex.I * v x)).toAffineMap
  obtain ⟨s, _, a, ha, hsa⟩ := hreturns 0
  obtain ⟨t, ht, b, hb, htb⟩ := hreturns (s + 1)
  have hhit : φ (t - s) (σ a) = σ b := by
    change φ (t - s) (x + a • (Complex.I * v x)) = x + b • (Complex.I * v x)
    rw [← hsa, ← φ.map_add, sub_add_cancel]
    exact htb
  apply not_mem_transverse_segment_of_pos φ hv.continuous hnz hderiv σ e hsource he ha
    (by linarith : 0 < t - s)
  exact ⟨b, hb, hhit.symm⟩

theorem exists_time_ge_not_mem_isCompact
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    {K : Set ℂ} (hK : IsCompact K) (z : ℂ) (T : ℝ) :
    ∃ t ≥ T, φ t z ∉ K :=
  frequently_atTop.mp (eventually_not_mem_isCompact φ hv hnz hderiv hK z).frequently T

end DifferentialGeometry.Analysis
