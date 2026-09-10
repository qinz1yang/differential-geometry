import DifferentialGeometry.Topology.Morse.EulerCharacteristic

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace Poincare.Homology
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [CompactSpace M]

include n

theorem finiteHomologyType_of_compact_manifold_withBoundary (K : Type) [Field K] :
    finiteHomologyType K (TopCat.of M) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  obtain ⟨_,_,_,_,_,_,_,_,hχ⟩ := Poincare.Morse.exists_relative_morse_eulerChar (n := m) (M := M)
  exact (hχ K).1

theorem eulerChar_eq_of_compact_manifold_withBoundary
    (K L : Type) [Field K] [Field L] : eulerChar K (TopCat.of M) = eulerChar L (TopCat.of M) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  obtain ⟨_,_,_,_,_,_,_,_,hχ⟩ := Poincare.Morse.exists_relative_morse_eulerChar (n := m) (M := M)
  exact (hχ K).2.trans (hχ L).2.symm

end Poincare.Homology
