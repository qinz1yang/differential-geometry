import DifferentialGeometry.Topology.Manifold.RegularNeighborhood
import Mathlib.Topology.Compactness.SigmaCompact

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_regular_superlevel_compact_exhaustion (K : CompactExhaustion M) :
    ∃ (D : CompactExhaustion M) (f : ℕ → M → ℝ) (r : ℕ → ℝ), ∀ n,
      D n = {x | r n ≤ f n x} ∧
      K (2 * n) ⊆ interior (D n) ∧ D n ⊆ interior (K (2 * n + 1)) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (f n) ∧ HasCompactSupport (f n) ∧
      tsupport (f n) ⊆ interior (K (2 * n + 1)) ∧
      (∀ x, 0 ≤ f n x) ∧ (∀ x ∈ K (2 * n), 1 ≤ f n x) ∧ r n ∈ Ioo (0 : ℝ) 1 ∧
      interior (D n) = {x | r n < f n x} ∧
      closure {x | r n < f n x} = D n ∧
      frontier (D n) = {x | f n x = r n} ∧
      ∀ x, f n x = r n → mfderiv I 𝓘(ℝ, ℝ) (f n) x ≠ 0 := by
  have h (n : ℕ) := exists_compact_regular_superlevel_between (I := I)
    (K.isCompact (2 * n)) isOpen_interior (K.subset_interior_succ (2 * n))
  choose f r hf hc hs hn hk hr hd hki hdu hi hcl hfr hreg using h
  let D : CompactExhaustion M :=
    { toFun := fun n => {x | r n ≤ f n x}
      isCompact' := hd
      subset_interior_succ' := by
        intro n x hx
        apply hki (n + 1)
        apply K.subset (show 2 * n + 1 ≤ 2 * (n + 1) by omega)
        exact interior_subset (hdu n hx)
      iUnion_eq' := by
        apply iUnion_eq_univ_iff.mpr
        intro x
        obtain ⟨n, hx⟩ := K.exists_mem x
        exact ⟨n, interior_subset (hki n (K.subset (by omega) hx))⟩ }
  exact ⟨D, f, r, fun n =>
    ⟨rfl, hki n, hdu n, hf n, hc n, hs n, hn n, hk n, hr n, hi n, hcl n, hfr n, hreg n⟩⟩

end DifferentialGeometry.Topology.Manifold
