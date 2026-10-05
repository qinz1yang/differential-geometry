import DifferentialGeometry.Analysis.Calculus.Cutoff.SymmetricCutoff
import Mathlib.Tactic

/-!
The actual smoothTransition profile is nondecreasing and strictly increasing across its open
transition interval. Its twice nested half-to-one gate loses the exact plateau after every
positive marker perturbation below one half. Only this concrete profile is asserted here.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

noncomputable def retainedMarkerGate (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - 1 / 2) / (1 - 1 / 2))

theorem smoothTransition_profile :
    ContDiff ℝ ∞ Real.smoothTransition ∧ Monotone Real.smoothTransition ∧
      (∀ t : ℝ, t ≤ 0 → Real.smoothTransition t = 0) ∧
      (∀ t : ℝ, 1 ≤ t → Real.smoothTransition t = 1) ∧
      StrictMonoOn Real.smoothTransition (Ioo 0 1) := by
  refine ⟨Real.smoothTransition.contDiff, Real.smoothTransition.monotone, ?_, ?_, ?_⟩
  · exact fun t ht => Real.smoothTransition.zero_of_nonpos ht
  · exact fun t ht => Real.smoothTransition.one_of_one_le ht
  · exact DifferentialGeometry.Analysis.smoothTransition_strictMonoOn.mono
      (fun t ht => ⟨ht.1.le, ht.2.le⟩)

theorem retained_marker_nested_lt_one {h : ℝ} (hh : 0 < h) (hhalf : h < 1 / 2) :
    0 < retainedMarkerGate (1 - h) ∧ retainedMarkerGate (1 - h) < 1 ∧
      retainedMarkerGate (retainedMarkerGate (1 - h)) < 1 := by
  have hinner : ((1 - h) - 1 / 2) / (1 - 1 / 2) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num <;> linarith
  have hpos : 0 < retainedMarkerGate (1 - h) :=
    Real.smoothTransition.pos_of_pos hinner.1
  have hlt : retainedMarkerGate (1 - h) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one hinner.2
  refine ⟨hpos, hlt, ?_⟩
  apply Real.smoothTransition.lt_one_of_lt_one
  norm_num
  linarith

theorem exists_small_nested_plateau_failure {ε : ℝ} (hε : 0 < ε) :
    ∃ h, 0 < h ∧ h < ε ∧ h < 1 / 2 ∧
      retainedMarkerGate (retainedMarkerGate (1 - h)) < 1 := by
  let h := min ε (1 / 2) / 2
  have hpos : 0 < h := half_pos (lt_min hε (by norm_num))
  have hεlt : h < ε := by
    dsimp [h]
    linarith [min_le_left ε (1 / 2), lt_min hε (by norm_num : (0 : ℝ) < 1 / 2)]
  have hhalf : h < 1 / 2 := by
    dsimp [h]
    linarith [min_le_right ε (1 / 2), lt_min hε (by norm_num : (0 : ℝ) < 1 / 2)]
  exact ⟨h, hpos, hεlt, hhalf, (retained_marker_nested_lt_one hpos hhalf).2.2⟩

end DifferentialGeometry.Geometry.Collapse
