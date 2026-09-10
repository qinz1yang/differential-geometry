import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open Function Set
open scoped Topology ContDiff Manifold

namespace Poincare.Topology.SphereSeparation

namespace Manifold

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} {E'' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

theorem isOpen_range_of_isImmersionOfComplement_punit
    [I.Boundaryless] [J.Boundaryless]
    (hf : Manifold.IsImmersionOfComplement PUnit.{u + 1} I J n f) :
    IsOpen (Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, rfl⟩
  let h := hf x
  let domExt : OpenPartialHomeomorph M E :=
    h.domChart.transHomeomorph I.toHomeomorph
  let codExt : OpenPartialHomeomorph N E'' :=
    h.codChart.transHomeomorph J.toHomeomorph
  let L : E ≃L[𝕜] E'' :=
    (ContinuousLinearEquiv.prodUnique 𝕜 E PUnit.{u + 1}).symm.trans h.equiv
  let U : Set E'' := L '' domExt.target
  have hUopen : IsOpen U :=
    L.toHomeomorph.isOpen_image.2 domExt.open_target
  have hUtarget : U ⊆ codExt.target := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hwChart : I.symm w ∈ h.domChart.target := by
      simpa [domExt, OpenPartialHomeomorph.transHomeomorph_target,
        ModelWithCorners.toHomeomorph] using hw
    have hw' : w ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target]
      exact ⟨hwChart, by simp [I.range_eq_univ]⟩
    have hz := h.map_target_subset_target
    have hz' := hz (Set.mem_image_of_mem _ hw')
    rw [h.codChart.extend_target] at hz'
    simpa [codExt, OpenPartialHomeomorph.transHomeomorph_target,
      ModelWithCorners.toHomeomorph, L] using hz'.1
  let V : Set N := codExt.symm '' U
  have hVopen : IsOpen V :=
    codExt.isOpen_image_symm_of_subset_target hUopen hUtarget
  have hfxV : f x ∈ V := by
    let w := domExt x
    have hxDom : x ∈ domExt.source := by
      simpa [domExt, OpenPartialHomeomorph.transHomeomorph_source] using h.mem_domChart_source
    have hw : w ∈ domExt.target := domExt.map_source hxDom
    have hwChart : I.symm w ∈ h.domChart.target := by
      simpa [domExt, OpenPartialHomeomorph.transHomeomorph_target,
        ModelWithCorners.toHomeomorph] using hw
    have hw' : w ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target]
      exact ⟨hwChart, by simp [I.range_eq_univ]⟩
    have hnormal := h.writtenInCharts hw'
    have hcoord : codExt (f x) = L w := by
      simpa [w, domExt, codExt, L, Function.comp_apply,
        OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
        OpenPartialHomeomorph.transHomeomorph_apply,
        OpenPartialHomeomorph.transHomeomorph_symm_apply,
        ModelWithCorners.toHomeomorph,
        h.domChart.left_inv h.mem_domChart_source] using hnormal
    refine ⟨L w, ⟨w, hw, rfl⟩, ?_⟩
    rw [← hcoord]
    exact codExt.left_inv (by
      simpa [codExt, OpenPartialHomeomorph.transHomeomorph_source] using h.mem_codChart_source)
  have hVrange : V ⊆ Set.range f := by
    intro z hz
    rcases hz with ⟨q, ⟨w, hw, rfl⟩, rfl⟩
    let m := domExt.symm w
    have hmSource : m ∈ domExt.source := domExt.map_target hw
    have hwChart : I.symm w ∈ h.domChart.target := by
      simpa [domExt, OpenPartialHomeomorph.transHomeomorph_target,
        ModelWithCorners.toHomeomorph] using hw
    have hw' : w ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target]
      exact ⟨hwChart, by simp [I.range_eq_univ]⟩
    have hnormal := h.writtenInCharts hw'
    have hmSource' : m ∈ h.domChart.source := by
      simpa [domExt, OpenPartialHomeomorph.transHomeomorph_source] using hmSource
    have hfmSource : f m ∈ codExt.source := by
      simpa [codExt, OpenPartialHomeomorph.transHomeomorph_source] using
        h.source_subset_preimage_source hmSource'
    refine ⟨m, ?_⟩
    apply codExt.injOn
    · exact hfmSource
    · exact codExt.map_target (hUtarget ⟨w, hw, rfl⟩)
    rw [codExt.right_inv (hUtarget ⟨w, hw, rfl⟩)]
    simpa [m, domExt, codExt, L, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.transHomeomorph_apply,
      OpenPartialHomeomorph.transHomeomorph_symm_apply,
      ModelWithCorners.toHomeomorph] using hnormal
  exact Filter.mem_of_superset (hVopen.mem_nhds hfxV) hVrange

theorem isOpen_range_of_isImmersion
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'']
    [I.Boundaryless] [J.Boundaryless]
    (hrank : Module.finrank 𝕜 E = Module.finrank 𝕜 E'')
    (hf : Manifold.IsImmersion I J n f) :
    IsOpen (Set.range f) := by
  apply isOpen_range_of_isImmersionOfComplement_punit
    (𝕜 := 𝕜) (E := E) (E'' := E'') (H := H) (G := G)
    (I := I) (J := J) (n := n)
  rcases hf with ⟨F, hFgroup, hFspace, hf⟩
  intro x
  let h := hf x
  let inclusion : F →ₗ[𝕜] E × F :=
    LinearMap.inr 𝕜 E F
  let linearInclusion : F →ₗ[𝕜] E'' :=
    h.equiv.toLinearEquiv.toLinearMap.comp inclusion
  let _ : FiniteDimensional 𝕜 F :=
    FiniteDimensional.of_injective linearInclusion
      (h.equiv.injective.comp (Prod.mk_right_injective 0))
  have hfinrank : Module.finrank 𝕜 F = 0 := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, hrank] at heq
    omega
  let complementEquiv : F ≃L[𝕜] PUnit.{u + 1} :=
    ContinuousLinearEquiv.ofFinrankEq
      (hfinrank.trans
        (Module.finrank_eq_zero_of_subsingleton (R := 𝕜) (M := PUnit.{u + 1})).symm)
  exact h.trans_F complementEquiv

theorem isOpen_range_of_isSmoothEmbedding
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'']
    [I.Boundaryless] [J.Boundaryless]
    (hrank : Module.finrank 𝕜 E = Module.finrank 𝕜 E'')
    (hf : Manifold.IsSmoothEmbedding I J n f) :
    IsOpen (Set.range f) :=
  isOpen_range_of_isImmersion (I := I) (J := J) hrank hf.isImmersion

end Manifold

end Poincare.Topology.SphereSeparation
