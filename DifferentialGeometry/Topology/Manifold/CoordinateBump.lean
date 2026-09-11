import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section
open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_coordinate_bump (φ : OpenPartialHomeomorph M E)
    (hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ φ φ.source) (a : E) (R : ℝ) (hR : 0 < R)
    (hball : closedBall a R ⊆ φ.target) :
    ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ x, 0 ≤ χ x) ∧
      support χ = φ.symm '' ball a R ∧
      (∀ x ∈ φ.symm '' ball a R, 0 < χ x) ∧
      tsupport χ ⊆ φ.symm '' closedBall a R ∧
      IsCompact (φ.symm '' closedBall a R) ∧
      φ.symm '' closedBall a R ⊆ φ.source := by
  let f : ContDiffBump a := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  let χ : M → ℝ := φ.source.indicator (f ∘ φ)
  have hsupp : support χ = φ.symm '' ball a R := by
    rw [show support χ = φ.source ∩ φ ⁻¹' ball a R by
      simp only [χ, support_indicator, support_comp_eq_preimage, f.support_eq]; rfl]
    exact (φ.symm_image_eq_source_inter_preimage (ball_subset_closedBall.trans hball)).symm
  have hcompact : IsCompact (φ.symm '' closedBall a R) :=
    (isCompact_closedBall a R).image_of_continuousOn (φ.continuousOn_symm.mono hball)
  have hsource : φ.symm '' closedBall a R ⊆ φ.source := by
    rintro x ⟨y, hy, rfl⟩
    exact φ.map_target (hball hy)
  have htsupp : tsupport χ ⊆ φ.symm '' closedBall a R := by
    rw [tsupport, hsupp]
    exact closure_minimal (image_mono ball_subset_closedBall) hcompact.isClosed
  have hnonneg (x : M) : 0 ≤ χ x := by
    exact indicator_nonneg (fun y _ => f.nonneg) x
  refine ⟨χ, ?_, hnonneg, hsupp, ?_, htsupp, hcompact, hsource⟩
  · apply contMDiff_of_tsupport
    intro x hx
    have hxs := hsource (htsupp hx)
    have heq : χ =ᶠ[𝓝 x] f ∘ φ :=
      (show EqOn χ (f ∘ φ) φ.source from eqOn_indicator).eventuallyEq_of_mem
        (φ.open_source.mem_nhds hxs)
    apply ContMDiffAt.congr_of_eventuallyEq _ heq
    exact f.contDiffAt.contMDiffAt.comp x
      ((hφ x hxs).contMDiffAt (φ.open_source.mem_nhds hxs))
  · intro x hx
    exact (hnonneg x).lt_of_ne' (by simpa only [← hsupp, mem_support] using hx)

end DifferentialGeometry.Topology.Manifold
