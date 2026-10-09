import DifferentialGeometry.Topology.PiecewiseLinear.Section34ArcFamilyPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskBoundaryPseudoIsotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_PL_cellular_disk_pseudoisotopy
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] [Finite κ] {D : ι → Set E} {r : ι → (Fin 3 → ℝ) → E}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hinter : ∀ i j, i ≠ j → D i ∩ D j ⊆ r i '' stdSimplexBoundary 2)
    {A : κ → Set E} {γ : κ → ℝ → E}
    (hγ : ∀ e, IsPLHomeomorphOn (γ e) (Icc 0 1) (A e))
    (hAinter : ∀ e f, e ≠ f → A e ∩ A f ⊆ {γ e 0, γ e 1})
    (edges : ι → Finset κ)
    (hboundary : ∀ i, r i '' stdSimplexBoundary 2 = ⋃ e ∈ edges i, A e)
    (hincident : ∀ e, ∃ i, e ∈ edges i)
    {u : E → E} (hu : ∀ i, IsPLHomeomorphOn u (D i) (D i))
    (huA : ∀ e, IsPLHomeomorphOn u (A e) (A e))
    (hzero : ∀ e, u (γ e 0) = γ e 0) (hone : ∀ e, u (γ e 1) = γ e 1) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ ((⋃ i, D i) ×ˢ Icc (0 : ℝ) 1)
        ((⋃ i, D i) ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ⋃ i, D i, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ ⋃ i, D i, Φ (x, 1) = (u x, 1)) ∧
      (∀ i, Φ '' (D i ×ˢ Icc (0 : ℝ) 1) = D i ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ e, Φ '' (A e ×ˢ Icc (0 : ℝ) 1) = A e ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ e, ∀ t ∈ Icc (0 : ℝ) 1,
        Φ (γ e 0, t) = (γ e 0, t) ∧ Φ (γ e 1, t) = (γ e 1, t) := by
  have hgraph : (⋃ i, r i '' stdSimplexBoundary 2) = ⋃ e, A e := by
    apply Subset.antisymm
    · refine iUnion_subset fun i => ?_
      rw [hboundary i]
      exact iUnion₂_subset fun e _ => subset_iUnion A e
    · refine iUnion_subset fun e => ?_
      obtain ⟨i, hi⟩ := hincident e
      intro x hx
      apply mem_iUnion.mpr
      exact ⟨i, (hboundary i).symm.subset (mem_iUnion₂.mpr ⟨e, hi, hx⟩)⟩
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨA, hΨends⟩ :=
    exists_PL_arc_family_pseudoisotopy hγ hAinter huA hzero hone
  have hΨrim (i : ι) : Ψ '' ((r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) =
      (r i '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1 := by
    rw [hboundary i]
    simp only [iUnion_prod_const, image_iUnion, hΨA]
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦΨ, hΦD⟩ :=
    exists_PL_disk_family_pseudoisotopy_with_prescribed_sides hr hinter hu
      (hgraph.symm ▸ hΨ) hΨrim (hgraph.symm ▸ hΨ0) (hgraph.symm ▸ hΨ1)
  rw [hgraph] at hΦΨ
  refine ⟨Φ, hΦ, hΦ0, hΦ1, hΦD, ?_, ?_⟩
  · intro e
    exact (hΦΨ.mono (prod_mono (subset_iUnion A e) Subset.rfl)).image_eq.trans (hΨA e)
  · intro e t ht
    exact ⟨(hΦΨ ⟨mem_iUnion.mpr ⟨e, (hγ e).bijOn.mapsTo (by norm_num)⟩, ht⟩).trans
      (hΨends e t ht).1,
      (hΦΨ ⟨mem_iUnion.mpr ⟨e, (hγ e).bijOn.mapsTo (by norm_num)⟩, ht⟩).trans
        (hΨends e t ht).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
