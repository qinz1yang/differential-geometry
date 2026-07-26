import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatEarlyFlux
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatEarlyFluxSeries
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammCarl
import DifferentialGeometry.Analysis.Parabolic.Euclidean.QuantCover

/-!
# The early divergence arm in the Koch--Lamm source space

This file inserts the canonical quantitative Euclidean cover and the
dimension-only shell series into the global early first-derivative heat
estimate.  It then converts the local `L²` arm of `KLSource1` to the exact
gradient-Carleson input, leaving a bound linear in the Koch--Lamm radius.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every heat shell has the canonical heat-scale cover with the cardinality
used by the global shell estimate. -/
theorem fluxShell_cover {t : ℝ} (ht : 0 < t) (x : V) (k : ℕ) :
    ∃ s : Finset V,
      s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V ∧
        fluxShell t x k ⊆ ⋃ c ∈ s, Metric.ball c (heatScale t) := by
  obtain ⟨s, hcard, hcover⟩ :=
    exists_shell_cover x (heatScale_pos ht) k
  refine ⟨s, hcard, fun y hy ↦ hcover ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact hy.2.le

/-- The initial-half divergence potential is bounded linearly by the local
`L²` radius of a Koch--Lamm flux. -/
theorem kl1_early_norm {T t : ℝ} {A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f : ℝ × V → F) (x : V)
    (h : KLSource1 T A₂ Aₚ f) :
    ‖heatEarly1 t w f x‖ₑ ≤
      ENNReal.ofReal ‖w‖ * earlyFluxC V * (A₂ : ℝ≥0∞) *
        fluxShellSeries (Module.finrank ℝ V) := by
  have hsum :
      (∑' k : ℕ, ENNReal.ofReal
        ((5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V *
          ((k + 1 : ℕ) : ℝ) *
            Real.exp (-(4 : ℝ)⁻¹ * (k : ℝ)))) ≤
        fluxShellSeries (Module.finrank ℝ V) := by
    rfl
  have hb := heatEarly1_norm ht htT w f x
    (fluxShell_cover ht x) hsum (kl1_to_gradCarl h)
  have hsqrt :
      (((A₂ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) = (A₂ : ℝ≥0∞) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hsqrt] at hb
  exact hb

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
