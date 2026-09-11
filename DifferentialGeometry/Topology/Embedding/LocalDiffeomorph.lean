import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped ContDiff Topology

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {J' : ModelWithCorners 𝕜 E'' G'}
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω} {f : M → N} {g : N → N'} {x : M}

private theorem isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
    [IsManifold J' n N'] (L : E' ≃L[𝕜] E'') (θ : Diffeomorph J J' G G' n)
    (hθ : ∀ y, J' (θ y) = L (J y)) (hf : IsImmersionAtOfComplement F I J n f x)
    (hg : IsLocalDiffeomorphAt J J' n g (f x)) :
    IsImmersionAtOfComplement F I J' n (g ∘ f) x := by
  classical
  obtain ⟨Φ, hΦx, hΦeq⟩ := hg
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp
    (hf.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hΦx))
  let φ := hf.domChart.restr s
  let ψ := (Φ.symm.toOpenPartialHomeomorph.trans hf.codChart).trans
    θ.toHomeomorph.toOpenPartialHomeomorph
  have hφsource : φ.source = hf.domChart.source ∩ s :=
    hf.domChart.restr_source' s hsopen
  have hψsource : ψ.source = Φ.target ∩ Φ.symm ⁻¹' hf.codChart.source := by
    simp [ψ]
  have hψtarget : ψ.target =
      θ.symm ⁻¹' (hf.codChart.target ∩ hf.codChart.symm ⁻¹' Φ.source) := by
    simp [ψ]
  have hxφ : x ∈ φ.source := by
    rw [hφsource]
    exact ⟨hf.mem_domChart_source, hxs⟩
  have hψ : ψ ∈ IsManifold.maximalAtlas J' n N' := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn J' J' n (θ ∘ hf.codChart ∘ Φ.symm) ψ.source
      rw [hψsource]
      exact θ.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
          (Φ.symm.contMDiffOn.mono Set.inter_subset_left) Set.inter_subset_right)
    · change ContMDiffOn J' J' n (Φ ∘ hf.codChart.symm ∘ θ.symm) ψ.target
      rw [hψtarget]
      have hinv : ContMDiffOn J J' n (Φ ∘ hf.codChart.symm)
          (hf.codChart.target ∩ hf.codChart.symm ⁻¹' Φ.source) :=
        Φ.contMDiffOn.comp
          ((contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).mono
            Set.inter_subset_left) Set.inter_subset_right
      exact hinv.comp θ.symm.contMDiff.contMDiffOn (fun _ hy => hy)
  have hsource : φ.source ⊆ (g ∘ f) ⁻¹' ψ.source := by
    intro y hy
    rw [hφsource] at hy
    have hyΦ : f y ∈ Φ.source := hs hy.2
    change g (f y) ∈ ψ.source
    rw [hψsource, hΦeq hyΦ]
    refine ⟨Φ.map_source hyΦ, ?_⟩
    change Φ.symm (Φ (f y)) ∈ hf.codChart.source
    have hcancel : Φ.symm (Φ (f y)) = f y := Φ.left_inv hyΦ
    rw [hcancel]
    exact hf.source_subset_preimage_source hy.1
  have htarget : (φ.extend I).target ⊆ (hf.domChart.extend I).target := by
    intro y hy
    rw [OpenPartialHomeomorph.extend_target] at hy ⊢
    exact ⟨hy.1.1, hy.2⟩
  apply IsImmersionAtOfComplement.mk_of_charts (hf.equiv.trans L) φ ψ hxφ (hsource hxφ)
  · exact restr_mem_maximalAtlas (contDiffGroupoid n I) hf.domChart_mem_maximalAtlas hsopen
  · exact hψ
  · exact hsource
  · intro y hy
    have hyφ := (φ.extend I).map_target hy
    rw [OpenPartialHomeomorph.extend_source, hφsource] at hyφ
    have hyΦ : f ((φ.extend I).symm y) ∈ Φ.source := hs hyφ.2
    change J' (θ (hf.codChart (Φ.symm (g (f ((φ.extend I).symm y)))))) =
      L (hf.equiv (y, 0))
    rw [hθ]
    have hcancel : Φ.symm (Φ (f ((φ.extend I).symm y))) =
        f ((φ.extend I).symm y) := Φ.left_inv hyΦ
    rw [hΦeq hyΦ, hcancel]
    exact congrArg L (hf.writtenInCharts (htarget hy))

theorem IsImmersionAt.isLocalDiffeomorphAt_comp
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {g : N → P}
    [IsManifold J n P] (hf : IsImmersionAt I J n f x)
    (hg : IsLocalDiffeomorphAt J J n g (f x)) :
    IsImmersionAt I J n (g ∘ f) x :=
  (isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
    (ContinuousLinearEquiv.refl 𝕜 E') (Diffeomorph.refl J G n) (fun _ => rfl)
    hf.isImmersionAtOfComplement_complement hg).isImmersionAt

theorem IsImmersion.isLocalDiffeomorphOn_comp
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P] {g : N → P}
    [IsManifold J n P] (hf : IsImmersion I J n f)
    (hg : IsLocalDiffeomorphOn J J n g (Set.range f)) :
    IsImmersion I J n (g ∘ f) := by
  apply IsImmersionOfComplement.isImmersion (F := hf.complement)
  intro x
  exact isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
    (ContinuousLinearEquiv.refl 𝕜 E') (Diffeomorph.refl J G n) (fun _ => rfl)
    (hf.isImmersionOfComplement_complement x) (hg ⟨f x, Set.mem_range_self x⟩)

private def modelDiffeomorph [J.Boundaryless] [J'.Boundaryless] (L : E' ≃L[𝕜] E'') :
    Diffeomorph J J' G G' n := by
  have hJ : ContMDiff 𝓘(𝕜, E') J n J.symm := by
    simpa only [J.range_eq_univ, contMDiffOn_univ] using J.contMDiffOn_symm (n := n)
  have hJ' : ContMDiff 𝓘(𝕜, E'') J' n J'.symm := by
    simpa only [J'.range_eq_univ, contMDiffOn_univ] using J'.contMDiffOn_symm (n := n)
  exact
    { toEquiv := ((J.toHomeomorph.trans L.toHomeomorph).trans J'.toHomeomorph.symm).toEquiv
      contMDiff_toFun := hJ'.comp (L.contDiff.contMDiff.comp J.contMDiff)
      contMDiff_invFun := hJ.comp (L.symm.contDiff.contMDiff.comp J'.contMDiff) }

theorem IsImmersionAt.isLocalDiffeomorphAt_comp_of_boundaryless
    {J' : ModelWithCorners 𝕜 E' G'}
    [J.Boundaryless] [J'.Boundaryless] [IsManifold J' n N']
    (hf : IsImmersionAt I J n f x) (hg : IsLocalDiffeomorphAt J J' n g (f x)) :
    IsImmersionAt I J' n (g ∘ f) x := by
  have hmodel (y : G) : J' (modelDiffeomorph (J := J) (J' := J') (n := n)
      (ContinuousLinearEquiv.refl 𝕜 E') y) = J y :=
    J'.toHomeomorph.apply_symm_apply (J y)
  exact (isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
    (ContinuousLinearEquiv.refl 𝕜 E') (modelDiffeomorph (ContinuousLinearEquiv.refl 𝕜 E'))
    hmodel hf.isImmersionAtOfComplement_complement hg).isImmersionAt

theorem IsImmersion.isLocalDiffeomorphOn_comp_of_boundaryless
    {J' : ModelWithCorners 𝕜 E' G'}
    [J.Boundaryless] [J'.Boundaryless] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsLocalDiffeomorphOn J J' n g (Set.range f)) :
    IsImmersion I J' n (g ∘ f) := by
  have hmodel (y : G) : J' (modelDiffeomorph (J := J) (J' := J') (n := n)
      (ContinuousLinearEquiv.refl 𝕜 E') y) = J y :=
    J'.toHomeomorph.apply_symm_apply (J y)
  apply IsImmersionOfComplement.isImmersion (F := hf.complement)
  intro x
  exact isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
    (ContinuousLinearEquiv.refl 𝕜 E') (modelDiffeomorph (ContinuousLinearEquiv.refl 𝕜 E')) hmodel
    (hf.isImmersionOfComplement_complement x) (hg ⟨f x, Set.mem_range_self x⟩)

theorem IsImmersionAt.isLocalDiffeomorphAt_comp_of_ne_zero
    [J.Boundaryless] [J'.Boundaryless] [IsManifold J' n N']
    (hf : IsImmersionAt I J n f x) (hg : IsLocalDiffeomorphAt J J' n g (f x))
    (hn : n ≠ 0) : IsImmersionAt I J' n (g ∘ f) x := by
  let L : E' ≃L[𝕜] E'' := hg.mfderivToContinuousLinearEquiv hn
  have hmodel (y : G) : J' (modelDiffeomorph (J := J) (J' := J') (n := n) L y) = L (J y) :=
    J'.toHomeomorph.apply_symm_apply (L (J y))
  exact (isImmersionAtOfComplement_isLocalDiffeomorphAt_comp L (modelDiffeomorph L)
    hmodel hf.isImmersionAtOfComplement_complement hg).isImmersionAt

theorem IsImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
    [J.Boundaryless] [J'.Boundaryless] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsLocalDiffeomorphOn J J' n g (Set.range f))
    (hn : n ≠ 0) : IsImmersion I J' n (g ∘ f) := by
  apply IsImmersionOfComplement.isImmersion (F := hf.complement)
  intro x
  have hx := hg ⟨f x, Set.mem_range_self x⟩
  let L : E' ≃L[𝕜] E'' := hx.mfderivToContinuousLinearEquiv hn
  have hmodel (y : G) : J' (modelDiffeomorph (J := J) (J' := J') (n := n) L y) = L (J y) :=
    J'.toHomeomorph.apply_symm_apply (L (J y))
  exact isImmersionAtOfComplement_isLocalDiffeomorphAt_comp L (modelDiffeomorph L)
    hmodel (hf.isImmersionOfComplement_complement x) hx

end Manifold
