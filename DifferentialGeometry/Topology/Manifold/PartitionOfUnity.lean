import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open Set Manifold
open scoped Manifold Topology ContDiff

namespace SmoothPartitionOfUnity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_isSubordinate_chartAt_source_inter_interior :
    ∃ rho : SmoothPartitionOfUnity M I M univ,
      rho.IsSubordinate (fun x => (chartAt H x).source) ∧
      ∀ x ∈ I.interior M, tsupport (rho x) ⊆ I.interior M := by
  classical
  let U : M → Set M := fun x => if x ∈ I.interior M then
    (chartAt H x).source ∩ I.interior M else (chartAt H x).source
  have hUopen (x : M) : IsOpen (U x) := by
    dsimp only [U]
    split_ifs
    · exact (chartAt H x).open_source.inter (I.isOpen_interior (by simp : (∞ : WithTop ℕ∞) ≠ 0))
    · exact (chartAt H x).open_source
  have hUcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    apply mem_iUnion_of_mem x
    dsimp only [U]
    split_ifs with hx
    · exact ⟨mem_chart_source H x, hx⟩
    · exact mem_chart_source H x
  obtain ⟨rho, hrho⟩ := exists_isSubordinate I isClosed_univ U hUopen hUcover
  refine ⟨rho, ?_, ?_⟩
  · intro x y hy
    have h := hrho x hy
    dsimp only [U] at h
    split_ifs at h
    · exact h.1
    · exact h
  · intro x hx y hy
    have h := hrho x hy
    dsimp only [U] at h
    rw [if_pos hx] at h
    exact h.2

end SmoothPartitionOfUnity
