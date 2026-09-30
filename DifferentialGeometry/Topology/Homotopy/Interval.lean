import Mathlib.Topology.UnitInterval

namespace DifferentialGeometry.Topology.Homotopy

open unitInterval

def icoToI (t : Set.Ico (0 : ℝ) 1) : I :=
  Set.inclusion Set.Ico_subset_Icc_self t

@[simp]
theorem icoToI_apply (t : Set.Ico (0 : ℝ) 1) : (icoToI t : ℝ) = (t : ℝ) :=
  rfl

theorem continuous_icoToI : Continuous (icoToI : Set.Ico (0 : ℝ) 1 → I) :=
  continuous_inclusion Set.Ico_subset_Icc_self

end DifferentialGeometry.Topology.Homotopy
