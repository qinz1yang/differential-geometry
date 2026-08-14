import Mathlib.Topology.UnitInterval

namespace DifferentialGeometry.Topology.Homotopy

open unitInterval

def icoToI (t : Set.Ico (0 : ℝ) 1) : I :=
  ⟨(t : ℝ), ⟨t.2.1, le_of_lt t.2.2⟩⟩

@[simp]
theorem icoToI_apply (t : Set.Ico (0 : ℝ) 1) : (icoToI t : ℝ) = (t : ℝ) :=
  rfl

theorem continuous_icoToI : Continuous (icoToI : Set.Ico (0 : ℝ) 1 → I) := by
  exact Continuous.subtype_mk continuous_subtype_val (fun t => ⟨t.2.1, le_of_lt t.2.2⟩)

end DifferentialGeometry.Topology.Homotopy
