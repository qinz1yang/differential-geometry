import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LipschitzOnWith

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : ℝ≥0} {f : X → E} {s : Set X}

theorem finrank_le_dimH_of_image_has_interior (hf : LipschitzOnWith K f s)
    (himage : (interior (f '' s)).Nonempty) :
    (Module.finrank ℝ E : ℝ≥0∞) ≤ dimH s := by
  rw [← Real.dimH_of_nonempty_interior himage]
  exact hf.dimH_image_le

theorem finrank_le_of_image_contains_ball (hf : LipschitzOnWith K f s)
    {y : E} {r : ℝ} {n : ℕ} (hr : 0 < r) (hball : Metric.ball y r ⊆ f '' s)
    (hdim : dimH s ≤ n) : Module.finrank ℝ E ≤ n := by
  have hmem : y ∈ interior (f '' s) := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hball)
  exact_mod_cast (hf.finrank_le_dimH_of_image_has_interior ⟨y, hmem⟩).trans hdim

end LipschitzOnWith
