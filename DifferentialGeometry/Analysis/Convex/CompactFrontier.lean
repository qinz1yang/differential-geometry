import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen

open Set Topology Metric

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem IsCompact.subset_of_frontier_subset_convex_open {C W : Set E}
    (hC : IsCompact C) (hW : Convex ℝ W) (hWo : IsOpen W) (hCW : frontier C ⊆ W) : C ⊆ W := by
  intro x hx
  by_contra hxW
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hx⟩, hC.ne_univ⟩
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hW hWo hxW
  have hzW := hCW hz
  have hpos : 0 < f x - f z := sub_pos.mpr (hf z hzW)
  obtain ⟨y, hyC, hmax⟩ := hC.exists_isMaxOn ⟨x, hx⟩ f.continuous.continuousOn
  have hybd : y ∈ frontier C := by
    refine ⟨subset_closure hyC, ?_⟩
    intro hyint
    have hcont : Continuous (fun t : ℝ => y + t • (x - z)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hnear : (fun t : ℝ => y + t • (x - z)) ⁻¹' C ∈ 𝓝 (0 : ℝ) := by
      apply hcont.continuousAt.preimage_mem_nhds
      simpa only [zero_smul, add_zero] using mem_interior_iff_mem_nhds.mp hyint
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hy' : y + (δ / 2) • (x - z) ∈ C := hball (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith)
    have hle : f (y + (δ / 2) • (x - z)) ≤ f y := hmax hy'
    have hcalc : f (y + (δ / 2) • (x - z)) = f y + (δ / 2) * (f x - f z) := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hcalc] at hle
    have hmul := mul_pos (half_pos hδ) hpos
    linarith
  exact (not_lt_of_ge (hmax hx)) (hf y (hCW hybd))

theorem IsCompact.subset_of_frontier_subset_convex_closed {C W : Set E}
    (hC : IsCompact C) (hW : Convex ℝ W) (hWc : IsClosed W) (hCW : frontier C ⊆ W) : C ⊆ W := by
  rw [← hWc.closure_eq, Metric.closure_eq_iInter_thickening]
  exact subset_iInter₂ fun δ hδ => IsCompact.subset_of_frontier_subset_convex_open hC
    (hW.thickening δ) Metric.isOpen_thickening (hCW.trans (Metric.self_subset_thickening hδ W))

theorem IsCompact.eq_of_frontier_eq_convex_closed {C W : Set E}
    (hC : IsCompact C) (hCi : (interior C).Nonempty)
    (hW : Convex ℝ W) (hWc : IsClosed W) (hfront : frontier C = frontier W) : C = W := by
  have hCW : C ⊆ W := IsCompact.subset_of_frontier_subset_convex_closed hC hW hWc
    (hfront ▸ hWc.frontier_subset)
  have hCWint := interior_mono hCW
  have hWi : (interior W).Nonempty := hCi.mono hCWint
  have hcover : interior W ⊆ interior C ∪ Cᶜ := by
    intro x hx
    by_cases hxC : x ∈ C
    · apply Or.inl
      by_contra hxint
      have hxfront : x ∈ frontier C := ⟨subset_closure hxC, hxint⟩
      exact (hfront ▸ hxfront).2 hx
    · exact Or.inr hxC
  have hWCint : interior W ⊆ interior C :=
    hW.interior.isPreconnected.subset_left_of_subset_union isOpen_interior
      hC.isClosed.isOpen_compl
      (disjoint_left.mpr (fun _ hx hxC => hxC (interior_subset hx))) hcover
      (hCi.mono fun _ hx => ⟨hCWint hx, hx⟩)
  apply Subset.antisymm hCW
  have hcl := hW.closure_interior_eq_closure_of_nonempty_interior hWi
  rw [hWc.closure_eq] at hcl
  rw [← hcl]
  exact closure_minimal (hWCint.trans interior_subset) hC.isClosed

theorem IsCompact.subset_of_frontier_subset_of_convex_image
    {X : Type*} [TopologicalSpace X] {C W : Set X} (hC : IsCompact C)
    (h : X ≃ₜ E) (hW : Convex ℝ (h '' W)) (hWc : IsClosed W) (hCW : frontier C ⊆ W) : C ⊆ W := by
  have hfront : frontier (h '' C) ⊆ h '' W := by
    rw [← h.image_frontier]
    exact image_mono hCW
  have hsub := IsCompact.subset_of_frontier_subset_convex_closed (hC.image h.continuous)
    hW (h.isClosedMap _ hWc) hfront
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hsub (mem_image_of_mem h hx)
  exact h.injective hyx ▸ hy

omit [Nontrivial E] in
theorem IsCompact.exists_mem_frontier_add_smul {C : Set E} (hC : IsCompact C)
    {p x : E} (hx : x ∈ C) (hxp : x ≠ p) :
    ∃ r : ℝ, 1 ≤ r ∧ p + r • (x - p) ∈ frontier C := by
  let f : ℝ → E := fun r => p + r • (x - p)
  have hf : IsClosedEmbedding f :=
    (Homeomorph.addLeft p).isClosedEmbedding.comp (isClosedEmbedding_smul_left (sub_ne_zero.mpr hxp))
  have hpre : IsCompact (f ⁻¹' C) := hf.isCompact_preimage hC
  have h1 : (1 : ℝ) ∈ f ⁻¹' C := by simpa only [mem_preimage, f, one_smul, add_sub_cancel] using hx
  obtain ⟨r, hr, hmax⟩ := hpre.exists_isMaxOn ⟨1, h1⟩ continuous_id.continuousOn
  refine ⟨r, hmax h1, subset_closure hr, ?_⟩
  intro hri
  have hnear : f ⁻¹' C ∈ 𝓝 r :=
    hf.continuous.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hri)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hr' : r + δ / 2 ∈ f ⁻¹' C := hball (by
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    linarith)
  have hle : r + δ / 2 ≤ r := hmax hr'
  linarith

end DifferentialGeometry.Analysis
