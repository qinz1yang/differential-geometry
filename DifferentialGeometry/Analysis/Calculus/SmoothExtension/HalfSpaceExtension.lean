import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_extension_across_halfSpace_boundary
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} {U : Set (E × ℝ)} {p : E}
    (hU : IsOpen U) (hp : (p, (0 : ℝ)) ∈ U)
    (hf : ContDiffOn ℝ ∞ f (U ∩ (univ ×ˢ Ici (0 : ℝ)))) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ (p, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
      ∃ g : E × ℝ → F, ContDiffOn ℝ ∞ g V ∧
        EqOn g f (V ∩ (univ ×ˢ Ici (0 : ℝ))) := by
  obtain ⟨A, J, hA, hpA, hJ, h0J, hAJ⟩ := mem_nhds_prod_iff'.mp (hU.mem_nhds hp)
  obtain ⟨r, hr, hrJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds h0J)
  let ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hstrip : A ×ˢ Icc (0 : ℝ) ρ ⊆ U ∩ (univ ×ˢ Ici (0 : ℝ)) := by
    intro z hz
    refine ⟨hAJ ⟨hz.1, hrJ ?_⟩, mem_univ _, hz.2.1⟩
    change dist z.2 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.2.1]
    exact lt_of_le_of_lt hz.2.2 (half_lt_self hr)
  obtain ⟨gext, W₀, hW₀, hgext, hext⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      (fun t x ↦ f (x, t)) ρ hρ A p (by rwa [hA.interior_eq])
      ((hf.mono hstrip).comp (contDiffOn_snd.prodMk contDiffOn_fst)
        (fun z hz ↦ ⟨hz.2, hz.1⟩))
  obtain ⟨W, hWW₀, hW, hpW⟩ := mem_nhds_iff.mp hW₀
  let V := (W ×ˢ Ioo (-ρ) ρ) ∩ U
  let g : E × ℝ → F := fun z ↦ gext z.2 z.1
  have hV : IsOpen V := (hW.prod isOpen_Ioo).inter hU
  have hpV : (p, (0 : ℝ)) ∈ V :=
    ⟨⟨hpW, neg_neg_of_pos hρ, hρ⟩, hp⟩
  refine ⟨V, hV, hpV, inter_subset_right, g, ?_, ?_⟩
  · exact hgext.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun z hz ↦ ⟨mem_univ _, hWW₀ hz.1.1⟩)
  · intro z hz
    exact hext z.2 ⟨hz.2.2, hz.1.1.2.2.le⟩ z.1 (hWW₀ hz.1.1.1)

end DifferentialGeometry.Analysis
