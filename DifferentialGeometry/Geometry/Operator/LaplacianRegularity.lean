import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Bundle.SmoothScalarGerm
import DifferentialGeometry.Geometry.Operator.TimeLaplacian

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

theorem contMDiffOn_laplacian_leviCivita
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (laplacian (Connection.LeviCivita g) g f) U := by
  intro x hx
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ hU hx hf
  have hLF : ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (Connection.LeviCivita g) g F) := by
    apply (Δ_g_contMDiff g ⟨F, hF⟩).congr
    intro y
    exact laplacian_levi_eq g hF y
  have heq : laplacian (Connection.LeviCivita g) g F =ᶠ[𝓝 x]
      laplacian (Connection.LeviCivita g) g f := by
    filter_upwards [hFf.eventuallyEq_nhds, hU.mem_nhds hx] with y hy hyU
    exact laplacian_congr_of_eventuallyEq (Connection.LeviCivita g) g hF.contMDiffAt
      (hf.contMDiffAt (hU.mem_nhds hyU)) hy
  exact (hLF.contMDiffAt.congr_of_eventuallyEq heq.symm).contMDiffWithinAt

theorem contMDiff_laplacian_leviCivita
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (Connection.LeviCivita g) g f) := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_laplacian_leviCivita g isOpen_univ hf.contMDiffOn

private theorem contMDiffOn_laplacian_leviCivita_euclidean_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : SmoothRiemannianMetric I M) (f : P → M → ℝ)
    {S : Set P} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (S ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => laplacian (Connection.LeviCivita g) g (f z.1) z.2)
      (S ×ˢ univ) := by
  intro z hz
  have hfs (p : P) (hp : p ∈ S) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f p) := by
    intro q
    exact (hf.contMDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, mem_univ q⟩)).curry_right
  have ht : extChartAt I z.2 z.2 ∈ interior (extChartAt I z.2).target := by
    rw [(isOpen_extChartAt_target (I := I) z.2).interior_eq]
    exact mem_extChartAt_target z.2
  have h := (scalarOnE_chartVossWeylLaplacian_contDiffOn_prod g f hS hf z.2).contDiffAt
    ((hS.prod isOpen_interior).mem_nhds
      (show (z.1, extChartAt I z.2 z.2) ∈ S ×ˢ interior (extChartAt I z.2).target
        from ⟨hz.1, ht⟩))
  have hc : ContMDiffAt (𝓘(ℝ, P).prod I) 𝓘(ℝ, P × E) ∞
      (fun r : P × M => (r.1, extChartAt I z.2 r.2)) z :=
    contMDiffAt_fst.prodMk_space (contMDiffAt_extChartAt.comp z contMDiffAt_snd)
  apply (h.contMDiffAt.comp z hc).contMDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
        (continuousAt_snd.eventually (extChartAt_source_mem_nhds (I := I) z.2)).filter_mono
          inf_le_left] with r hr hsrc
    simp only [Function.comp_apply, DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_extChartAt z.2 _ hsrc]
    exact (laplacian_levi_eq g (hfs r.1 hr.1) r.2).trans
      (voss_weyl_laplacian_formula_pointwise g z.2 (hfs r.1 hr.1)
        (by rwa [extChartAt_source (I := I) z.2] at hsrc))
  · simp only [Function.comp_apply, DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_extChartAt z.2 _ (mem_extChartAt_source z.2)]
    exact (laplacian_levi_eq g (hfs z.1 hz.1) z.2).trans
      (voss_weyl_laplacian_formula_pointwise g z.2 (hfs z.1 hz.1) (mem_chart_source H z.2))

private theorem contMDiff_laplacian_leviCivita_prod
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
    [IP.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : P → M → ℝ)
    (hf : ContMDiff (IP.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    ContMDiff (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => laplacian (Connection.LeviCivita g) g (f z.1) z.2) := by
  intro z
  let S := (extChartAt IP z.1).target
  let F : EP → M → ℝ := fun p q => f ((extChartAt IP z.1).symm p) q
  have hF : ContMDiffOn (𝓘(ℝ, EP).prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry F)
      (S ×ˢ univ) := by
    exact hf.comp_contMDiffOn
      (((contMDiffOn_extChartAt_symm (I := IP) z.1).comp contMDiffOn_fst
        (fun r hr => hr.1)).prodMk contMDiffOn_snd)
  have hL := contMDiffOn_laplacian_leviCivita_euclidean_prod g F
    (isOpen_extChartAt_target (I := IP) z.1) hF
  have hc : ContMDiffAt (IP.prod I) (𝓘(ℝ, EP).prod I) ∞
      (fun r : P × M => (extChartAt IP z.1 r.1, r.2)) z :=
    (contMDiffAt_extChartAt.comp z contMDiffAt_fst).prodMk contMDiffAt_snd
  have hLC := (hL.contMDiffAt
    (((isOpen_extChartAt_target (I := IP) z.1).prod isOpen_univ).mem_nhds
      (show (extChartAt IP z.1 z.1, z.2) ∈ S ×ˢ univ
        from ⟨mem_extChartAt_target z.1, mem_univ z.2⟩))).comp z hc
  apply hLC.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.eventually (extChartAt_source_mem_nhds (I := IP) z.1)]
    with r hr
  simp only [Function.comp_apply, F, (extChartAt IP z.1).left_inv hr]

theorem contMDiffOn_laplacian_leviCivita_prod_of_isOpen
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
    [IP.Boundaryless] [FiniteDimensional ℝ EP] [T2Space P]
    (g : SmoothRiemannianMetric I M) {f : P → M → ℝ} {D : Set (P × M)}
    (hD : IsOpen D)
    (hf : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f) D) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => laplacian (Connection.LeviCivita g) g (f z.1) z.2) D := by
  intro z hz
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ hD hz hf
  have hLF := contMDiff_laplacian_leviCivita_prod (I := I) (IP := IP) g
    (fun p q => F (p, q)) hF
  have hEq : ∀ᶠ r in 𝓝 z,
      laplacian (Connection.LeviCivita g) g (f r.1) r.2 =
        laplacian (Connection.LeviCivita g) g (fun q => F (r.1, q)) r.2 := by
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hFf
    obtain ⟨Uo, hUsub, hUo, hzU⟩ := mem_nhds_iff.mp hU
    obtain ⟨Vo, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp hV
    have hUV_nhds : Uo ×ˢ Vo ∈ 𝓝 z :=
      (hUo.prod hVo).mem_nhds ⟨hzU, hzV⟩
    filter_upwards [hUV_nhds, hD.mem_nhds hz] with r hr hrD
    have hqeq : (fun q => f r.1 q) =ᶠ[𝓝 r.2] (fun q => F (r.1, q)) := by
      filter_upwards [hVo.mem_nhds hr.2] with q hq
      exact (show F (r.1, q) = f r.1 q from
        hUV (show (r.1, q) ∈ U ×ˢ V from ⟨hUsub hr.1, hVsub hq⟩)).symm
    exact (laplacian_congr_of_eventuallyEq (Connection.LeviCivita g) g
      ((hf.curry_right).contMDiffAt
        ((continuousAt_const.prodMk continuousAt_id).eventually (hD.mem_nhds hrD)))
      (hF.contMDiffAt.comp r.2 (contMDiffAt_const.prodMk contMDiffAt_id)) hqeq)
  exact (hLF.contMDiffAt.congr_of_eventuallyEq hEq).contMDiffWithinAt

end DifferentialGeometry.Geometry.Operator
