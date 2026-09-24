import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Convex.PathConnected

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

private theorem interior_maximal_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {e e' : OpenPartialHomeomorph M H} {x : M}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn ℝ ∞ φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Filter.inter_mem_iff,
      mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex (e'.open_source.mem_nhds hex')
  have hsurj : Function.Surjective (fderiv ℝ φ (e.extend I x)) := by
    rw [← fderivWithin_of_mem_nhds hφx]
    exact (I.isInvertible_fderivWithin_extendCoordChange (by simp) he he'
      (by simp [hex, hex'])).surjective
  have hmem : e'.extend I x ∈ interior (range I) := by
    rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
    have hd : DifferentiableAt ℝ φ (e.extend I x) :=
      (hφ.differentiableOn (by simp)).differentiableAt hφx
    exact hd.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
      I.nonempty_interior (φ.mapsTo.mono_right (by simp [φ, inter_assoc])) hsurj
  exact e'.mem_interior_extend_target (by simp [hex']) hmem

theorem immersion_image_mem_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    {f : M → N} {x : M}
    (hf : IsImmersionAt I J ∞ f x)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E')
    (hx : I.IsInteriorPoint x) {s : Set M} (hs : s ∈ 𝓝 x) :
    f '' s ∈ 𝓝 (f x) := by
  obtain ⟨F, hF, hFR, h⟩ := hf
  let := hF
  let := hFR
  let : FiniteDimensional ℝ (E × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  let : FiniteDimensional ℝ F := Module.Finite.of_surjective
    (LinearMap.snd ℝ E F) (fun z => ⟨(0, z), rfl⟩)
  have hzero : Module.finrank ℝ F = 0 := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, ← hdim] at heq
    omega
  let : Subsingleton F := (Module.finrank_zero_iff).mp hzero
  let : Unique F := ⟨⟨0⟩, fun z => Subsingleton.elim z 0⟩
  let A : E ≃L[ℝ] E' := (ContinuousLinearEquiv.prodUnique ℝ E F).symm.trans h.equiv
  have hA (z : E) : A z = h.equiv (z, 0) := rfl
  have hxi : h.domChart.extend I x ∈ interior (h.domChart.extend I).target :=
    interior_maximal_chart (IsManifold.subset_maximalAtlas (chart_mem_atlas H x))
      h.domChart_mem_maximalAtlas (mem_chart_source H x) h.mem_domChart_source
      ((I.isInteriorPoint_iff).mp hx)
  have hxrange : h.domChart.extend I x ∈ interior (range I) :=
    interior_mono h.domChart.extend_target_subset_range hxi
  have himage : (h.domChart.extend I) '' (s ∩ h.domChart.source) ∈
      𝓝 (h.domChart.extend I x) :=
    h.domChart.extend_image_nhds_mem_nhds_of_mem_interior_range h.mem_domChart_source
      hxrange (Filter.inter_mem hs (h.domChart.open_source.mem_nhds h.mem_domChart_source))
  have hformula (z : M) (hz : z ∈ h.domChart.source) :
      (h.codChart.extend J) (f z) = A ((h.domChart.extend I) z) := by
    have hze : z ∈ (h.domChart.extend I).source := by
      simpa only [OpenPartialHomeomorph.extend_source] using hz
    have hnormal := h.writtenInCharts ((h.domChart.extend I).map_source hze)
    simpa only [Function.comp_apply, OpenPartialHomeomorph.extend_source,
      (h.domChart.extend I).left_inv hze, hA] using hnormal
  have htarget : A '' ((h.domChart.extend I) '' (s ∩ h.domChart.source)) ∈
      𝓝 ((h.codChart.extend J) (f x)) := by
    rw [hformula x h.mem_domChart_source]
    exact A.toHomeomorph.isOpenMap.image_mem_nhds himage
  have hpre := (h.codChart.continuousAt_extend h.mem_codChart_source).preimage_mem_nhds htarget
  filter_upwards [hpre, h.codChart.open_source.mem_nhds h.mem_codChart_source] with y hy hys
  obtain ⟨v, ⟨z, hzs, rfl⟩, heq⟩ := hy
  refine ⟨z, hzs.1, ?_⟩
  have hfzOriginal : f z ∈ h.codChart.source := h.source_subset_preimage_source hzs.2
  have hfz : f z ∈ (h.codChart.extend J).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using hfzOriginal
  have hyc : y ∈ (h.codChart.extend J).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using hys
  apply (h.codChart.extend J).injOn hfz hyc
  exact (hformula z hzs.2).trans heq

end DifferentialGeometry.Topology
