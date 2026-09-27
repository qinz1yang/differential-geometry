import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.MetricSpace.Lipschitz









noncomputable section

open Filter Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]


theorem norm_differential_le_of_norm_sub_le {u : E → F} {v : E → G}
    {du : E →L[ℝ] F} {dv : E →L[ℝ] G} {x : E} {L : ℝ}
    (hu : HasFDerivAt u du x) (hv : HasFDerivAt v dv x)
    (h : ∀ y, ‖v y - v x‖ ≤ L * ‖u y - u x‖) (w : E) :
    ‖dv w‖ ≤ L * ‖du w‖ := by
  have hdu := (hu.lim w tendsto_norm_atTop_atTop).norm
  have hdv := (hv.lim w tendsto_norm_atTop_atTop).norm
  apply le_of_tendsto_of_tendsto hdv (tendsto_const_nhds.mul hdu)
  apply Filter.Eventually.of_forall
  intro t
  simpa only [norm_smul, mul_left_comm] using
    mul_le_mul_of_nonneg_left (h (x + t⁻¹ • w)) (norm_nonneg t)


theorem norm_differential_comp_le {u : E → F} {f : F → G}
    {du : E →L[ℝ] F} {dcomp : E →L[ℝ] G} {x : E} {L : ℝ≥0}
    (hu : HasFDerivAt u du x) (hcomp : HasFDerivAt (f ∘ u) dcomp x)
    (hf : LipschitzWith L f) (w : E) : ‖dcomp w‖ ≤ L * ‖du w‖ :=
  norm_differential_le_of_norm_sub_le hu hcomp (fun y => hf.norm_sub_le (u y) (u x)) w


theorem differential_comp_eq_zero_of_eq_zero {u : E → F} {f : F → G}
    {du : E →L[ℝ] F} {dcomp : E →L[ℝ] G} {x : E} {L : ℝ≥0}
    (hu : HasFDerivAt u du x) (hcomp : HasFDerivAt (f ∘ u) dcomp x)
    (hf : LipschitzWith L f) {w : E} (hw : du w = 0) : dcomp w = 0 := by
  have h := norm_differential_comp_le hu hcomp hf w
  simpa [hw] using h

end DifferentialGeometry.Analysis
