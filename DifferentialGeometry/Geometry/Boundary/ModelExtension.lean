import DifferentialGeometry.Geometry.Boundary.ModelCoordinates
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [HasSmoothBoundary E H I]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_contDiffOn_extension_of_model
    {f : E → F} {U : Set E} {y : E} (hU : IsOpen U) (hyU : y ∈ U)
    (hy : y ∈ frontier (range I)) (hf : ContDiffOn ℝ ∞ f (U ∩ range I)) :
    ∃ V : Set E, IsOpen V ∧ y ∈ V ∧ V ⊆ U ∧
      ∃ g : E → F, ContDiffOn ℝ ∞ g V ∧ EqOn g f (V ∩ range I) := by
  rw [← range_modelBoundaryParam I] at hy
  obtain ⟨p, rfl⟩ := hy
  obtain ⟨e, hp, he, hi, heq⟩ := exists_modelBoundary_coordinates I p
  have hezero : e (p, 0) = modelBoundaryParam I p := by simp [heq]
  let D := e.source ∩ e ⁻¹' U
  have hD : IsOpen D := he.continuousOn.isOpen_inter_preimage e.open_source hU
  have hpD : (p, (0 : ℝ)) ∈ D := ⟨hp, by simpa only [mem_preimage, hezero] using hyU⟩
  obtain ⟨A, J, hA, hpA, hJ, h0J, hAJ⟩ := mem_nhds_prod_iff'.mp (hD.mem_nhds hpD)
  obtain ⟨r, hr, hrJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds h0J)
  let ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hstrip : A ×ˢ Icc (0 : ℝ) ρ ⊆ D := by
    intro z hz
    apply hAJ
    refine ⟨hz.1, hrJ ?_⟩
    change dist z.2 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.2.1]
    exact lt_of_le_of_lt hz.2.2 (half_lt_self hr)
  have hfe : ContDiffOn ℝ ∞ (f ∘ e) (A ×ˢ Icc (0 : ℝ) ρ) := by
    apply hf.comp (he.mono (fun z hz ↦ (hstrip hz).1))
    intro z hz
    refine ⟨(hstrip hz).2, ?_⟩
    rw [heq]
    exact (modelBoundaryParam_add_mem_range_iff I z.1 z.2).2 hz.2.1
  obtain ⟨gext, W₀, hW₀, hgext, hext⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
    (fun t x ↦ f (e (x, t))) ρ hρ A p (by simpa only [hA.interior_eq] using hpA)
    (hfe.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz ↦ ⟨hz.2, hz.1⟩))
  obtain ⟨W, hWW₀, hW, hpW⟩ := mem_nhds_iff.mp hW₀
  let V := (e.target ∩ e.symm ⁻¹' (W ×ˢ Ioo (-ρ) ρ)) ∩ U
  have hV : IsOpen V :=
    (hi.continuousOn.isOpen_inter_preimage e.open_target (hW.prod isOpen_Ioo)).inter hU
  have hyp : e.symm (modelBoundaryParam I p) = (p, 0) := by
    rw [← hezero, e.left_inv hp]
  have hyV : modelBoundaryParam I p ∈ V := by
    refine ⟨⟨hezero ▸ e.map_source hp, ?_⟩, hyU⟩
    change e.symm (modelBoundaryParam I p) ∈ W ×ˢ Ioo (-ρ) ρ
    rw [hyp]
    exact ⟨hpW, neg_neg_of_pos hρ, hρ⟩
  let g : E → F := fun z ↦ gext (e.symm z).2 (e.symm z).1
  have hg : ContDiffOn ℝ ∞ g V := by
    exact hgext.comp ((hi.mono (fun z hz ↦ hz.1.1)).snd.prodMk
      (hi.mono (fun z hz ↦ hz.1.1)).fst)
      (fun z hz ↦ ⟨mem_univ _, hWW₀ hz.1.2.1⟩)
  refine ⟨V, hV, hyV, fun z hz ↦ hz.2, g, hg, ?_⟩
  intro z hz
  have hnonneg : 0 ≤ (e.symm z).2 := by
    apply (modelBoundaryParam_add_mem_range_iff I (e.symm z).1 (e.symm z).2).1
    rw [← heq, e.right_inv hz.1.1.1]
    exact hz.2
  change gext (e.symm z).2 (e.symm z).1 = f z
  rw [hext _ ⟨hnonneg, hz.1.1.2.2.2.le⟩ _ (hWW₀ hz.1.1.2.1), e.right_inv hz.1.1.1]

end Poincare.Geometry.Boundary
