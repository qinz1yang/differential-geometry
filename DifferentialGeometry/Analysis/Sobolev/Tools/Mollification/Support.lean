import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic
import Mathlib.Topology.MetricSpace.Thickening


noncomputable section

namespace DifferentialGeometry.Analysis.Sobolev

open MeasureTheory Metric Set
open scoped Pointwise Convolution

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem mollifyEps_nonneg {ε : ℝ} (hε : 0 < ε)
    {u : E → ℝ} (hu : ∀ x, 0 ≤ u x) (x : E) :
    0 ≤ mollifyEps hε u x := by
  rw [mollifyEps_apply]
  exact integral_nonneg fun y => mul_nonneg (mollifierEps_nonneg hε y) (hu (x - y))

theorem tsupport_mollifyEps_subset_cthickening {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) :
    tsupport (mollifyEps hε u) ⊆ cthickening ε (tsupport u) := by
  apply closure_minimal _ isClosed_cthickening
  have hs : Function.support (mollifyEps hε u) ⊆
      Function.support (mollifierEps hε) + Function.support u :=
    support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hs hx
  apply mem_cthickening_of_dist_le (y + z) z ε (tsupport u) (subset_closure hz)
  have hyε := mollifierEps_support_subset_closedBall_eps hε hy
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hyε

theorem exists_isCompact_tsupport_mollifyEps_subset
    {u : E → ℝ} (hu : HasCompactSupport u)
    {Ω : Set E} (hΩ : IsOpen Ω) (huΩ : tsupport u ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧
      tsupport u ⊆ K ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ δ →
        tsupport (mollifyEps hε u) ⊆ K := by
  obtain ⟨δ, hδ, hδΩ⟩ := hu.exists_cthickening_subset_open hΩ huΩ
  refine ⟨δ, hδ, cthickening δ (tsupport u), hu.cthickening, hδΩ,
    self_subset_cthickening _, ?_⟩
  intro ε hε hεδ
  exact (tsupport_mollifyEps_subset_cthickening hε u).trans
    (cthickening_mono hεδ (tsupport u))

end DifferentialGeometry.Analysis.Sobolev
