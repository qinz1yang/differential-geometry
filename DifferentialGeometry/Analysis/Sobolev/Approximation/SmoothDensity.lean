import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseHelpers
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuant

/-!
# Per-chart strong-support smooth approximation in `W^{1,p}_chart(M)`

For a closed manifold `M` modelled on a finite-dimensional real inner-product
space `E`, this file develops the per-chart **strong-support** approximation
needed to upgrade the Euclidean smooth-density theorem
`MemWkp.exists_smooth_compactSupport_approx` from a per-chart-target
approximation (with weak support inside `chartTargetEuclid α`) to a strong
support approximation supported strictly inside the chart-α image of an open
neighbourhood of `tsupport ρ_α`.

The strong support property — the approximant `χ_α` has
`tsupport χ_α ⊆ {y | η_α y = 1}` for a smooth cutoff `η_α` that is `1` on
the chart-α image of `tsupport ρ_α` — is what is needed to control cross-chart
contributions in the global smooth-density argument.

## Main definitions and results

* `chartImagePOUTsupport α` : the toEuclidean image
  `toEuclidean ∘ extChartAt I α '' tsupport ρ_α` of the closed support of
  the canonical partition of unity weight at `α`.
* `chartImagePOUTsupport_isCompact` : compactness on a closed `M`.
* `chartImagePOUTsupport_subset_target` : containment in `chartTargetEuclid α`.
* `chartPushed_eq_zero_off_chartImagePOUTsupport` : the chart-pushed function
  vanishes on the chart target outside `chartImagePOUTsupport α`.
* `exists_chartCutoff` : a smooth cutoff `η_α` that is `1` on a neighbourhood
  of `chartImagePOUTsupport α`, with `tsupport η_α ⊆ chartTargetEuclid α`.
* `chartCutoff_smul_chartPushed_eq_chartPushed` : on the chart target, the
  cutoff product `η_α · chartPushed g α u` equals `chartPushed g α u`
  pointwise (since `η_α = 1` on the support of `chartPushed g α u`).
* `chartCutoff_smul_chartPushed_memWkp` : `η · chartPushed g α u` is in the
  Euclidean `W^{1,p}` of the chart target whenever `‖η‖ ≤ C` and `‖∇η‖ ≤ C`
  on the chart target.
* `exists_smooth_strong_support_approx` : for each `α` and each
  `MemWkpChart` function `u`, there exists a smooth compactly-supported
  Euclidean approximant `χ_α` whose `tsupport` is contained in the chart
  target, with quantitative `W^{1,p}` closeness to `chartPushed g α u`.

These are stand-alone helper pieces of the chart-Sobolev smooth-density
machinery, useful for any per-chart approximation argument that needs the
strong support property.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The toEuclidean image of `extChartAt I α '' tsupport ρ_α` for the canonical
chart-atlas partition of unity. Compact on a closed manifold and contained in
`chartTargetEuclid α`, this is the natural compact "kernel" inside which the
chart-pushed function `chartPushed g α u` is supported (as a subset of the
chart target). -/
def chartImagePOUTsupport
    [T2Space M] [SigmaCompactSpace M] (α : M) : Set EuclN :=
  toEuclidean '' ((extChartAt I α) ''
    (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

/-- `chartImagePOUTsupport α` is compact on a closed manifold. -/
lemma chartImagePOUTsupport_isCompact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact (chartImagePOUTsupport (I := I) (M := M) α) := by
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_src : Tα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hTα_ext_src : Tα ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]
    exact hTα_chart_src hx
  have hcont_ext : ContinuousOn (extChartAt I α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_src
  have hImg_ext_compact : IsCompact ((extChartAt I α) '' Tα) :=
    hTα_compact.image_of_continuousOn hcont_ext
  exact hImg_ext_compact.image (toEuclidean (E := E)).continuous

/-- `chartImagePOUTsupport α` is contained in `chartTargetEuclid α`. -/
lemma chartImagePOUTsupport_subset_target
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    chartImagePOUTsupport (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  unfold chartImagePOUTsupport at hy
  obtain ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩ := hy
  have hx_chart : x ∈ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hx_supp
  have hx_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_chart
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hx_ext
  exact ⟨z, hz_target, hzy⟩

/-- The chart-pushed function vanishes pointwise on `chartTargetEuclid α`
outside `chartImagePOUTsupport α`. -/
lemma chartPushed_eq_zero_off_chartImagePOUTsupport
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0 :=
  chartPushed_support_subset_compact_in_target (I := I) (M := M) α u y
    hy_target hy_off

/-- For each chart `α` on a closed manifold, there exist a small radius `δ > 0`
and a smooth cutoff `η_α : EuclN → ℝ` such that:

* `η_α ≡ 1` on the closed `δ`-thickening of `chartImagePOUTsupport α`;
* `tsupport η_α ⊆ chartTargetEuclid α` (so the cutoff is supported in the
  chart target);
* `η_α` has compact support and takes values in `[0, 1]`;
* `η_α` is `C^∞`. -/
theorem exists_chartCutoff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (α : M) :
    ∃ (δ : ℝ) (η : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ (chartImagePOUTsupport (I := I) (M := M) α) ⊆
        chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Metric.cthickening δ
        (chartImagePOUTsupport (I := I) (M := M) α), η y = 1) ∧
      tsupport η ⊆ chartTargetEuclid (I := I) (M := M) α := by
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
    (d := Module.finrank ℝ E)
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartImagePOUTsupport_subset_target (I := I) (M := M) α)

omit [FiniteDimensional ℝ E] in
/-- A range bound `Set.range η ⊆ [0, 1]` gives `‖η x‖ ≤ 1` everywhere. -/
lemma norm_le_one_of_range_Icc
    {η : EuclN → ℝ}
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1) (x : EuclN) :
    ‖η x‖ ≤ 1 := by
  have hx : η x ∈ Set.Icc (0 : ℝ) 1 :=
    hη_range (Set.mem_range_self x)
  have h1 : 0 ≤ η x := hx.1
  have h2 : η x ≤ 1 := hx.2
  rw [Real.norm_of_nonneg h1]
  exact h2

omit [FiniteDimensional ℝ E] in
/-- A smooth function with compact support has a uniform bound on its gradient
norm `‖fderiv ℝ η x‖`, derived from continuity of `fderiv` and compactness of
`tsupport η`. -/
lemma exists_grad_bound_of_compactSupport_smooth
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_cpt : HasCompactSupport η) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ C := by
  classical
  have h_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have h_cont_fderiv : Continuous (fun x : EuclN => fderiv ℝ η x) :=
    hη_smooth.continuous_fderiv h_ne_zero
  have h_cont_norm : Continuous (fun x : EuclN => ‖fderiv ℝ η x‖) :=
    h_cont_fderiv.norm
  have h_zero_off : ∀ x : EuclN, x ∉ tsupport η → fderiv ℝ η x = 0 := by
    intro x hx
    have h_mem : (tsupport η)ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hx
    have h_eq : (η =ᶠ[𝓝 x] fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem h_mem
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq h_eq]
    simp
  set K : Set EuclN := tsupport η with hK_def
  have hK_compact : IsCompact K := hη_cpt
  have h_bdd : ∃ C : ℝ, ∀ x ∈ K, ‖fderiv ℝ η x‖ ≤ C := by
    by_cases hKn : K.Nonempty
    · obtain ⟨x₀, _hx₀K, hx₀_max⟩ :=
        hK_compact.exists_isMaxOn hKn h_cont_norm.continuousOn
      exact ⟨‖fderiv ℝ η x₀‖, fun x hx => hx₀_max hx⟩
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hKn ⟨x, hx⟩).elim
  obtain ⟨C₀, hC₀⟩ := h_bdd
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x ∈ K
  · exact (hC₀ x hx).trans (le_max_left _ _)
  · rw [h_zero_off x hx]
    simp only [norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)

/-- If `η_α ≡ 1` on the closed `δ`-thickening of `chartImagePOUTsupport α`,
and the chart-pushed function `chartPushed g α u` vanishes on the chart target
outside `chartImagePOUTsupport α`, then `η_α · chartPushed g α u` equals
`chartPushed g α u` pointwise on the chart target. -/
lemma chartCutoff_smul_chartPushed_eq_chartPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u : M → ℝ)
    {δ : ℝ} (_hδ_pos : 0 < δ)
    {η : EuclN → ℝ}
    (hη_one : ∀ y ∈ Metric.cthickening δ
      (chartImagePOUTsupport (I := I) (M := M) α), η y = 1) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      η y * chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y =
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y := by
  intro y hy
  by_cases hyKα : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · have hy_cthick : y ∈ Metric.cthickening δ
        (chartImagePOUTsupport (I := I) (M := M) α) :=
      Metric.self_subset_cthickening _ hyKα
    have hηy : η y = 1 := hη_one y hy_cthick
    rw [hηy]; ring
  · have hf_zero : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α u hy hyKα
    rw [hf_zero]; ring

/-- The cutoff-product `η · chartPushed g α u` is in `MemWkp 1 p` of the
chart target, given a uniform bound on `‖η‖` and `‖∇η‖` on the chart target. -/
lemma chartCutoff_smul_chartPushed_memWkp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound_zero : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α, ‖η x‖ ≤ C)
    (hη_bound_one : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖fderiv ℝ η x‖ ≤ C) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p
      (fun y => η y * chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hu_α := hu α
  refine DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
    (d := Module.finrank ℝ E) 1 hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hη_smooth (C := C) ?_ hu_α
  intro j hj x hx
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    exact hη_bound_zero x hx
  · rw [norm_iteratedFDeriv_one]
    exact hη_bound_one x hx

/-- For each `α` and each `MemWkpChart g 1 p u` function on a closed manifold,
the chart-pushed function `chartPushed g α u` admits a smooth Euclidean
approximant `χ_α` with:

* `tsupport χ_α ⊆ chartTargetEuclid α` (compact support inside the chart
  target);
* `χ_α` is `C^∞`;
* The `W^{1,p}` distance `wkpNorm 1 p (chartPushed g α u - χ_α)` is bounded
  by `ENNReal.ofReal ε_per`.

This is the per-chart input to the global smooth-density argument: the smooth
approximant inside the chart target exists with explicit quantitative bound.
-/
theorem exists_smooth_strong_support_approx
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    (α : M) (ε_per : ℝ) (hε_per : 0 < ε_per) :
    ∃ (χ : EuclN → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y =>
          chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y -
            χ y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal ε_per := by
  classical
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_smooth, hη_cpt, hη_range, hη_one,
    hη_supp⟩ :=
    exists_chartCutoff (I := I) (M := M) α
  have hη_norm_one : ∀ x : EuclN, ‖η x‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_range
  obtain ⟨Cη, _hCη_pos, hCη_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_smooth hη_cpt
  set C : ℝ := max Cη 1 with hC_def
  have hη_norm_C : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α, ‖η x‖ ≤ C :=
    fun x _ => (hη_norm_one x).trans (le_max_right _ _)
  have hη_grad_C : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖fderiv ℝ η x‖ ≤ C := fun x _ => (hCη_grad x).trans (le_max_left _ _)
  set ρ_α := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M with hρα_def
  set f_orig : EuclN → ℝ :=
    chartPushed (I := I) (M := M) ρ_α α u with hf_orig_def
  set f : EuclN → ℝ := fun y => η y * f_orig y with hf_def
  have hf_mem_W1p :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p f
        (chartTargetEuclid (I := I) (M := M) α) :=
    chartCutoff_smul_chartPushed_memWkp (I := I) (M := M) g hp_one hu α
      hη_smooth hη_norm_C hη_grad_C
  have hf_supp_subset : tsupport f ⊆ tsupport η :=
    tsupport_smul_subset_left η f_orig
  have hf_compact : HasCompactSupport f :=
    HasCompactSupport.intro hη_cpt (fun y hy => by
      change η y * f_orig y = 0
      have hy_off : y ∉ tsupport η := hy
      rw [image_eq_zero_of_notMem_tsupport hy_off]
      ring)
  have hf_supp_target : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hf_supp_subset.trans hη_supp
  have hf_eq_forig_on_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      f y = f_orig y :=
    chartCutoff_smul_chartPushed_eq_chartPushed (I := I) (M := M) α u
      hδ_pos hη_one
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_supp, hχ_close⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_smooth_compactSupport_approx
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      1 p hp_one hp_top
      hf_mem_W1p hf_compact hf_supp_target
      ε_per hε_per
  refine ⟨χ, hχ_smooth, hχ_compact, hχ_supp, ?_⟩
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_diff_eq : (fun y => f_orig y - χ y) =ᵐ[volume.restrict
      (chartTargetEuclid (I := I) (M := M) α)] (fun y => f y - χ y) := by
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have h_eq := hf_eq_forig_on_target y hy
    change f_orig y - χ y = f y - χ y
    rw [h_eq]
  have h_norm_eq : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => f_orig y - χ y) (chartTargetEuclid (I := I) (M := M) α) =
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => f y - χ y) (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      h_diff_eq
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => f_orig y - χ y) (chartTargetEuclid (I := I) (M := M) α) ≤
    ENNReal.ofReal ε_per
  rw [h_norm_eq]
  exact hχ_close

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
