import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section TopologicalParameter

variable {P : Type*} [TopologicalSpace P]

theorem tsupport_chartPullback_prod_subset_source [T2Space P] [T2Space M]
    (α : M) {φ : P × EuclN → ℝ} {s : Set P} (hφc : HasCompactSupport φ)
    (hφt : tsupport φ ⊆ s ×ˢ chartTargetEuclid (I := I) α) :
    tsupport (fun z : P × M =>
      chartPullback I α (fun y => φ (z.1, y)) z.2) ⊆
        s ×ˢ (chartAt H α).source := by
  have ht : tsupport φ ⊆ univ ×ˢ chartTargetEuclid (I := I) α :=
    fun z hz => ⟨mem_univ _, (hφt hz).2⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := tsupport_chartPullback_prod_subset α hφc ht hz
  refine ⟨(hφt hw).1, ?_⟩
  have hy := (hφt hw).2
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M) α] at hy
  simpa only [extChartAt_source] using (extChartAt I α).map_target hy

end TopologicalParameter

theorem exists_contMDiff_hasCompactSupport_chart_extension
    [T2Space M] [IsManifold I ∞ M]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (α : M) {ψ : P × E → ℝ} {s : Set P} {W : Set E}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ s ×ˢ W) (hWt : W ⊆ (extChartAt I α).target) :
    ∃ F : P × M → ℝ,
      ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞ F ∧
      HasCompactSupport F ∧ tsupport F ⊆ s ×ˢ (chartAt H α).source ∧
      (∀ z ∈ tsupport F, extChartAt I α z.2 ∈ W) ∧
      ∀ t y, y ∈ (extChartAt I α).target → F (t, (extChartAt I α).symm y) = ψ (t, y) := by
  let e := toEuclidean (E := E)
  let φ : P × EuclN → ℝ := fun z => ψ (z.1, e.symm z.2)
  have hφ : ContDiff ℝ ∞ φ := by
    simpa only [φ, Function.comp_def] using
      hψ.comp (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd))
  have hφc : HasCompactSupport φ := by
    have hc := hψc.comp_homeomorph ((Homeomorph.refl P).prodCongr e.symm.toHomeomorph)
    change HasCompactSupport (fun z : P × EuclN => ψ (z.1, e.symm z.2)) at hc
    exact hc
  have hφW : tsupport φ ⊆ s ×ˢ (e.symm ⁻¹' W) := by
    have ht := tsupport_comp_subset_preimage ψ
      (f := fun z : P × EuclN => (z.1, e.symm z.2))
      (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
    intro z hz
    exact hψs (ht hz)
  have hφs : tsupport φ ⊆ s ×ˢ chartTargetEuclid (I := I) α := by
    intro z hz
    refine ⟨(hφW hz).1, ?_⟩
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M) α]
    exact hWt (hφW hz).2
  have hφt : tsupport φ ⊆ univ ×ˢ chartTargetEuclid (I := I) α :=
    fun z hz => ⟨mem_univ _, (hφs hz).2⟩
  refine ⟨fun z => chartPullback I α (fun y => φ (z.1, y)) z.2,
    chartPullback_contMDiff_prod_of_hasCompactSupport α hφ hφc hφt,
    hasCompactSupport_chartPullback_prod α hφc hφt,
    tsupport_chartPullback_prod_subset_source α hφc hφs, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := tsupport_chartPullback_prod_subset α hφc hφt hz
    change extChartAt I α ((extChartAt I α).symm (e.symm w.2)) ∈ W
    rw [(extChartAt I α).right_inv (hWt (hφW hw).2)]
    exact (hφW hw).2
  · intro t y hy
    have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      simpa only [extChartAt_source] using (extChartAt I α).map_target hy
    change chartPullback I α (fun v => φ (t, v)) ((extChartAt I α).symm y) = ψ (t, y)
    rw [chartPullback_apply_of_mem α _ hx, (extChartAt I α).right_inv hy]
    exact congrArg (fun v => ψ (t, v)) (e.symm_apply_apply y)

end DifferentialGeometry.Analysis.Sobolev.Chart
