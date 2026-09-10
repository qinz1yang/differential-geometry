import DifferentialGeometry.Topology.Morse.ClosedEulerCharacteristic
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace Poincare.Homology
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] [CompactSpace M]

include I

theorem finiteHomologyType_of_compact_boundaryless_manifold (K : Type) [Field K] :
    finiteHomologyType K (TopCat.of M) := by
  cases subsingleton_or_nontrivial E
  · exact finiteHomologyType_of_subsingleton_model K I M
  · obtain ⟨_,_,_,_,_,hχ⟩ := Poincare.Morse.exists_morse_eulerChar I (M := M)
    exact (hχ K).1

theorem eulerChar_eq_of_compact_boundaryless_manifold
    (K L : Type) [Field K] [Field L] : eulerChar K (TopCat.of M) = eulerChar L (TopCat.of M) := by
  cases subsingleton_or_nontrivial E
  · exact (eulerChar_of_subsingleton_model K I M).trans (eulerChar_of_subsingleton_model L I M).symm
  · obtain ⟨_,_,_,_,_,hχ⟩ := Poincare.Morse.exists_morse_eulerChar I (M := M)
    exact (hχ K).2.trans (hχ L).2.symm

end Poincare.Homology
