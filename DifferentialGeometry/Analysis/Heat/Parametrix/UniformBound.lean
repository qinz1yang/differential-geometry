import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Compactness.Compact

noncomputable section

open Set

namespace DifferentialGeometry.Analysis.HeatEquation

theorem exists_uniform_linear_time_bound_of_compact_cover
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {U : X → Set X} (hU : ∀ x ∈ K, IsOpen (U x))
    (hcover : K ⊆ ⋃ x ∈ K, U x) {F : ℝ → X → ℝ} {T : ℝ}
    (hlocal : ∀ x ∈ K, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Ioc 0 T, ∀ y ∈ U x, abs (F t y) ≤ t * C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ y ∈ K, abs (F t y) ≤ t * C := by
  classical
  rcases eq_empty_or_nonempty K with rfl | hKne
  · refine ⟨0, le_rfl, ?_⟩
    simp
  obtain ⟨s, hs_sub, hs_fin, hs⟩ := hK.elim_finite_subcover_image (b := K) (c := U)
    (fun x hx => hU x hx) hcover
  let t : Finset X := hs_fin.toFinset
  have hs_nonempty : s.Nonempty := by
    obtain ⟨y, hy⟩ := hKne
    have hy' := hs hy
    rw [mem_iUnion] at hy'
    obtain ⟨x, hy'⟩ := hy'
    rw [mem_iUnion] at hy'
    obtain ⟨hx, _⟩ := hy'
    exact ⟨x, hx⟩
  have ht_nonempty : t.Nonempty := hs_fin.toFinset_nonempty.mpr hs_nonempty
  have ht_mem : ∀ x ∈ t, x ∈ K := by
    intro x hx
    exact hs_sub (hs_fin.mem_toFinset.mp hx)
  choose C hC hbound using fun x hx => hlocal x hx
  let C' : X → ℝ := fun x => if hx : x ∈ K then C x hx else 0
  let C₀ : ℝ := t.sup' ht_nonempty C'
  refine ⟨C₀, ?_, ?_⟩
  · obtain ⟨x, hx, hEq⟩ := Finset.exists_mem_eq_sup' ht_nonempty C'
    have hxK : x ∈ K := hs_sub (hs_fin.mem_toFinset.mp hx)
    rw [show C₀ = C' x by simp only [C₀, hEq]]
    simp only [C', dif_pos hxK]
    exact hC x hxK
  · intro t ht y hy
    have hy' := hs hy
    rw [mem_iUnion] at hy'
    obtain ⟨x, hy'⟩ := hy'
    rw [mem_iUnion] at hy'
    obtain ⟨hx, hyx⟩ := hy'
    have hxK : x ∈ K := hs_sub hx
    have hCx : C' x = C x hxK := dif_pos hxK
    calc
      abs (F t y) ≤ t * C' x := by rw [hCx]; exact hbound x hxK t ht y hyx
      _ ≤ t * C₀ := mul_le_mul_of_nonneg_left
        (Finset.le_sup' C' (hs_fin.mem_toFinset.mpr hx)) ht.1.le

end DifferentialGeometry.Analysis.HeatEquation
