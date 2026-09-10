import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

open Function Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_nhds_isOpenEmbedding_domRestrict_of_contMDiffAt_of_bijective_mfderiv
    {E F H G M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace H] [TopologicalSpace G]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M}
    (hn : n ≠ 0)
    (hf : ContMDiffAt I J n f x)
    (hbij : Function.Bijective (mfderiv I J f x)) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧
      Topology.IsOpenEmbedding (U.domRestrict f) := by
  let g : E → F := writtenInExtChartAt I J x f
  let a : E := extChartAt I x x
  have hgContWithin : ContDiffWithinAt ℝ n g (Set.range I) a := by
    simpa [g, a] using (contMDiffAt_iff.mp hf).2
  have hgCont : ContDiffAt ℝ n g a := by
    rw [I.range_eq_univ, contDiffWithinAt_univ] at hgContWithin
    exact hgContWithin
  let D : E →L[ℝ] F := fderiv ℝ g a
  have hmf : mfderiv I J f x = D := by
    rw [(hf.mdifferentiableAt hn).mfderiv]
    rw [I.range_eq_univ, fderivWithin_univ]
  have hDbij : Function.Bijective D := by
    rw [← hmf]
    exact hbij
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hDbij.1)
    (LinearMap.range_eq_top.mpr hDbij.2)
  have hgDerivD : HasFDerivAt g D a :=
    (hgCont.differentiableAt hn).hasFDerivAt
  have hL : (L : E →L[ℝ] F) = D := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  have hgDeriv : HasFDerivAt g (L : E →L[ℝ] F) a := by
    rw [hL]
    exact hgDerivD
  let φ : OpenPartialHomeomorph E F :=
    hgCont.toOpenPartialHomeomorph g hgDeriv hn
  let c : OpenPartialHomeomorph M E :=
    (chartAt H x).transHomeomorph I.toHomeomorph
  let d : OpenPartialHomeomorph N F :=
    (chartAt G (f x)).transHomeomorph J.toHomeomorph
  have hfxSource : f x ∈ d.source := by
    simp [d, OpenPartialHomeomorph.transHomeomorph_source]
  have hpre : f ⁻¹' d.source ∈ 𝓝 x :=
    (contMDiffAt_iff.mp hf).1.preimage_mem_nhds
      (d.open_source.mem_nhds hfxSource)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hpre
  let cV : OpenPartialHomeomorph M E := c.restrOpen V hVopen
  let e : OpenPartialHomeomorph M N := (cV.trans φ).trans d.symm
  have hcxSource : cV x ∈ φ.source := by
    change a ∈ φ.source
    exact hgCont.mem_toOpenPartialHomeomorph_source hgDeriv hn
  have hphi_cx : φ (cV x) = d (f x) := by
    change g (c x) = d (f x)
    simp only [g, writtenInExtChartAt, Function.comp_apply]
    rw [show c x = extChartAt I x x by rfl]
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    rfl
  have hxe : x ∈ e.source := by
    change x ∈ ((cV.trans φ).trans d.symm).source
    rw [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨?_, hcxSource⟩, ?_⟩
    · exact ⟨mem_chart_source (H := H) x, hxV⟩
    · change φ (cV x) ∈ d.target
      rw [hphi_cx]
      exact d.map_source hfxSource
  have heq : Set.EqOn f e e.source := by
    intro y hy
    have hycV : y ∈ cV.source := by
      exact hy.1.1
    have hyV : y ∈ V := hycV.2
    have hyfSource : f y ∈ d.source := hVsub hyV
    change f y = d.symm (φ (cV y))
    have hphi : φ (cV y) = d (f y) := by
      change g (c y) = d (f y)
      simp only [g, writtenInExtChartAt, Function.comp_apply]
      rw [show c y = extChartAt I x y by rfl]
      rw [(extChartAt I x).left_inv (by simpa [c,
        OpenPartialHomeomorph.transHomeomorph_source] using hycV.1)]
      rfl
    rw [hphi, d.left_inv hyfSource]
  have hlocal : IsLocalHomeomorphOn f ({x} : Set M) := by
    apply IsLocalHomeomorphOn.mk f {x}
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨e, hxe, heq⟩
  obtain ⟨ef, hxef, hfun⟩ := hlocal x (by simp)
  refine ⟨ef.source, ef.open_source.mem_nhds hxef, ef.open_source, ?_⟩
  rw [hfun]
  exact ef.isOpenEmbedding_restrict

theorem exists_nhds_injOn_of_contMDiffAt_of_bijective_mfderiv
    {E F H G M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace H] [TopologicalSpace G]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M}
    (hn : n ≠ 0)
    (hf : ContMDiffAt I J n f x)
    (hbij : Function.Bijective (mfderiv I J f x)) :
    ∃ U ∈ 𝓝 x, Set.InjOn f U := by
  obtain ⟨U, hU, -, hUemb⟩ :=
    exists_nhds_isOpenEmbedding_domRestrict_of_contMDiffAt_of_bijective_mfderiv
      I J hn hf hbij
  exact ⟨U, hU, Set.injOn_iff_injective.mpr hUemb.injective⟩

end DifferentialGeometry.Topology.SphereSeparation
