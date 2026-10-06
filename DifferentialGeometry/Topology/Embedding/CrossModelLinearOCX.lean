import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Cross-model immersions, part 1: affine changes of model spaces (lane O-CROSS, G1)

Mathlib composes immersions with diffeomorphisms only when the models agree. This file treats
diffeomorphisms between manifolds with DIFFERENT models whose model ranges correspond under an
affine map `v ↦ Λ v + s` of the model vector spaces:

* `modelAffineDiffeomorph_OCX I I' Λ s hΛ : H ≃ₘ⟮I, I'⟯ H'`, `h ↦ I'⁻¹ (Λ (I h) + s)`, for every
  continuous linear equivalence `Λ` and shift `s` with `Λ v + s ∈ range I' ↔ v ∈ range I`
  (translations of a model along its boundary, coordinate permutations between `𝓡∂ 3` and
  `torusModel.prod (𝓡∂ 1)`, …);
* `chartPartialDiffeomorph_OCX`: a chart of the maximal atlas as a partial diffeomorphism, and
  `PartialDiffeomorph.mem_maximalAtlas_OCX` (the converse);
* `IsImmersionAtOfComplement.diffeomorph_comp_linear_OCX` / `.comp_diffeomorph_linear_OCX`:
  post- and pre-composition of an immersion with a cross-model diffeomorphism when a linear `Λ`
  matches the two model ranges; global forms `IsImmersion.*_OCX`, `IsSmoothEmbedding.*_OCX`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Manifold

section ModelAffine

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']

/-- **Affine change of model spaces**: `h ↦ I'⁻¹ (Λ (I h) + s)`, a diffeomorphism `H ≃ H'` as
soon as `v ↦ Λ v + s` maps `range I` onto `range I'`. -/
def modelAffineDiffeomorph_OCX (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (Λ : E ≃L[ℝ] E') (s : E') (hΛ : ∀ v, Λ v + s ∈ range I' ↔ v ∈ range I) :
    Diffeomorph I I' H H' ∞ where
  toFun h := I'.symm (Λ (I h) + s)
  invFun h' := I.symm (Λ.symm (I' h' - s))
  left_inv h := by
    have h1 : Λ (I h) + s ∈ range I' := (hΛ _).2 (mem_range_self h)
    change I.symm (Λ.symm (I' (I'.symm (Λ (I h) + s)) - s)) = h
    rw [I'.right_inv h1, add_sub_cancel_right, Λ.symm_apply_apply, I.left_inv]
  right_inv h' := by
    have h1 : Λ.symm (I' h' - s) ∈ range I := by
      rw [← hΛ, Λ.apply_symm_apply, sub_add_cancel]
      exact mem_range_self h'
    change I'.symm (Λ (I (I.symm (Λ.symm (I' h' - s)))) + s) = h'
    rw [I.right_inv h1, Λ.apply_symm_apply, sub_add_cancel, I'.left_inv]
  contMDiff_toFun := by
    refine I'.contMDiffOn_symm.comp_contMDiff ?_ (fun h => (hΛ _).2 (mem_range_self h))
    exact ((Λ.contDiff.add contDiff_const).contMDiff).comp I.contMDiff
  contMDiff_invFun := by
    refine I.contMDiffOn_symm.comp_contMDiff ?_ (fun h' => ?_)
    · exact ((Λ.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff).comp
        I'.contMDiff
    · rw [← hΛ, Λ.apply_symm_apply, sub_add_cancel]
      exact mem_range_self h'

variable {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {Λ : E ≃L[ℝ] E'} {s : E'}
  {hΛ : ∀ v, Λ v + s ∈ range I' ↔ v ∈ range I}

theorem modelAffineDiffeomorph_OCX_model (h : H) :
    I' (modelAffineDiffeomorph_OCX I I' Λ s hΛ h) = Λ (I h) + s :=
  I'.right_inv ((hΛ _).2 (mem_range_self h))

theorem modelAffineDiffeomorph_OCX_symm_model (h' : H') :
    I ((modelAffineDiffeomorph_OCX I I' Λ s hΛ).symm h') = Λ.symm (I' h' - s) := by
  have h1 : Λ.symm (I' h' - s) ∈ range I := by
    rw [← hΛ, Λ.apply_symm_apply, sub_add_cancel]
    exact mem_range_self h'
  exact I.right_inv h1

/-- The inverse of the affine change, read in the models, on `range I'`. -/
theorem modelAffineDiffeomorph_OCX_symm_eq {v : E'} (hv : v ∈ range I') :
    (modelAffineDiffeomorph_OCX I I' Λ s hΛ).symm (I'.symm v) = I.symm (Λ.symm (v - s)) := by
  change I.symm (Λ.symm (I' (I'.symm v) - s)) = _
  rw [I'.right_inv hv]

end ModelAffine

section Charts

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A chart of the maximal atlas as a partial diffeomorphism onto its image in the model. -/
def chartPartialDiffeomorph_OCX (φ : OpenPartialHomeomorph M H)
    (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M) : PartialDiffeomorph I I M H ∞ where
  toPartialEquiv := φ.toPartialEquiv
  open_source := φ.open_source
  open_target := φ.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hφ
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hφ

/-- A partial diffeomorphism into the model space is a chart of the maximal atlas. -/
theorem _root_.PartialDiffeomorph.mem_maximalAtlas_OCX [IsManifold I ∞ M]
    (ψ : PartialDiffeomorph I I M H ∞) :
    ψ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas I ∞ M :=
  ψ.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn ψ.contMDiffOn ψ.symm.contMDiffOn

end Charts

section Linear

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E H} {J' : ModelWithCorners ℝ E' H'}
  {N N' : Type*} [TopologicalSpace N] [ChartedSpace H N] [TopologicalSpace N']
  [ChartedSpace H' N']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Post-composition with a cross-model diffeomorphism** (linear range correspondence): the code
chart is transported by `Φ` and by the affine model change. -/
theorem IsImmersionAtOfComplement.diffeomorph_comp_linear_OCX [IsManifold J' ∞ N']
    (Λ : E ≃L[ℝ] E') (hΛ : ∀ v, Λ v + 0 ∈ range J' ↔ v ∈ range J) {f : M → N} {x : M}
    (hf : IsImmersionAtOfComplement F IM J ∞ f x) (Φ : Diffeomorph J J' N N' ∞) :
    IsImmersionAtOfComplement F IM J' ∞ (Φ ∘ f) x := by
  classical
  let κ := modelAffineDiffeomorph_OCX J J' Λ 0 hΛ
  let ψ : OpenPartialHomeomorph N' H' :=
    (Φ.symm.toHomeomorph.toOpenPartialHomeomorph.trans hf.codChart).trans
      κ.toHomeomorph.toOpenPartialHomeomorph
  have hψsource : ψ.source = Φ.symm ⁻¹' hf.codChart.source := by
    simp [ψ]
  have hψtarget : ψ.target = κ.symm ⁻¹' hf.codChart.target := by
    simp [ψ]
  have hψ : ψ ∈ IsManifold.maximalAtlas J' ∞ N' := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn J' J' ∞ (κ ∘ hf.codChart ∘ Φ.symm) ψ.source
      refine κ.contMDiff.comp_contMDiffOn ?_
      apply (contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        Φ.symm.contMDiff.contMDiffOn
      intro y hy
      exact hψsource ▸ hy
    · change ContMDiffOn J' J' ∞ (Φ ∘ hf.codChart.symm ∘ κ.symm) ψ.target
      refine Φ.contMDiff.comp_contMDiffOn ?_
      apply (contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        κ.symm.contMDiff.contMDiffOn
      intro y hy
      exact hψtarget ▸ hy
  apply IsImmersionAtOfComplement.mk_of_charts (hf.equiv.trans Λ) hf.domChart ψ
    hf.mem_domChart_source
  · rw [hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, Φ.symm_apply_apply] using
      hf.mem_codChart_source
  · exact hf.domChart_mem_maximalAtlas
  · exact hψ
  · intro y hy
    rw [Set.mem_preimage, hψsource]
    simpa only [Set.mem_preimage, Function.comp_apply, Φ.symm_apply_apply] using
      hf.source_subset_preimage_source hy
  · intro y hy
    change J' (κ (hf.codChart (Φ.symm (Φ (f ((hf.domChart.extend IM).symm y)))))) =
      (hf.equiv.trans Λ) (y, 0)
    rw [Φ.symm_apply_apply, modelAffineDiffeomorph_OCX_model, add_zero,
      ContinuousLinearEquiv.trans_apply]
    congr 1
    exact hf.writtenInCharts hy

/-- **Pre-composition with a cross-model diffeomorphism** (linear range correspondence): the
source chart is transported by `D⁻¹` and by the linear model change. -/
theorem IsImmersionAtOfComplement.comp_diffeomorph_linear_OCX [IsManifold IP ∞ P]
    (Λ : EP ≃L[ℝ] EM) (hΛ : ∀ v, Λ v + 0 ∈ range IM ↔ v ∈ range IP) {g : M → N}
    (D : Diffeomorph IP IM P M ∞) {x : P}
    (hg : IsImmersionAtOfComplement F IM J ∞ g (D x)) :
    IsImmersionAtOfComplement F IP J ∞ (g ∘ D) x := by
  classical
  let κ := modelAffineDiffeomorph_OCX IP IM Λ 0 hΛ
  let φ : OpenPartialHomeomorph P HP :=
    (D.toHomeomorph.toOpenPartialHomeomorph.trans hg.domChart).trans
      κ.symm.toHomeomorph.toOpenPartialHomeomorph
  have hφsource : φ.source = D ⁻¹' hg.domChart.source := by
    simp [φ]
  have hφtarget : φ.target = κ ⁻¹' hg.domChart.target := by
    ext y
    simp [φ]
  have hφ : φ ∈ IsManifold.maximalAtlas IP ∞ P := by
    apply φ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn IP IP ∞ (κ.symm ∘ hg.domChart ∘ D) φ.source
      refine κ.symm.contMDiff.comp_contMDiffOn ?_
      apply (contMDiffOn_of_mem_maximalAtlas hg.domChart_mem_maximalAtlas).comp
        D.contMDiff.contMDiffOn
      intro y hy
      exact hφsource ▸ hy
    · change ContMDiffOn IP IP ∞ (D.symm ∘ hg.domChart.symm ∘ κ) φ.target
      refine D.symm.contMDiff.comp_contMDiffOn ?_
      apply (contMDiffOn_symm_of_mem_maximalAtlas hg.domChart_mem_maximalAtlas).comp
        κ.contMDiff.contMDiffOn
      intro y hy
      exact hφtarget ▸ hy
  have hκIP : ∀ y ∈ range IP, κ (IP.symm y) = IM.symm (Λ y) := by
    intro y hy
    change IM.symm (Λ (IP (IP.symm y)) + 0) = _
    rw [IP.right_inv hy, add_zero]
  apply IsImmersionAtOfComplement.mk_of_charts
    (((Λ.prodCongr (ContinuousLinearEquiv.refl ℝ F))).trans hg.equiv) φ hg.codChart
  · rw [hφsource]
    exact hg.mem_domChart_source
  · exact hg.mem_codChart_source
  · exact hφ
  · exact hg.codChart_mem_maximalAtlas
  · intro y hy
    apply hg.source_subset_preimage_source
    simpa only [hφsource, Set.mem_preimage] using hy
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [IP.target_eq] at hy1
    have hΛy : Λ y ∈ (hg.domChart.extend IM).target := by
      refine ⟨?_, ?_⟩
      · rw [IM.target_eq, ← add_zero (Λ y), hΛ]
        exact hy1
      · change IM.symm (Λ y) ∈ hg.domChart.target
        rw [← hκIP y hy1]
        change IP.symm y ∈ φ.target at hy2
        rw [hφtarget] at hy2
        exact hy2
    have hw := hg.writtenInCharts hΛy
    change hg.codChart.extend J (g (D (D.symm (hg.domChart.symm (κ (IP.symm y)))))) =
      hg.equiv ((Λ.prodCongr (ContinuousLinearEquiv.refl ℝ F)) (y, 0))
    rw [D.apply_symm_apply, hκIP y hy1]
    exact hw

variable [IsManifold J' ∞ N'] [IsManifold IP ∞ P]

/-- Global form of `IsImmersionAtOfComplement.diffeomorph_comp_linear_OCX`. -/
theorem IsImmersion.diffeomorph_comp_linear_OCX (Λ : E ≃L[ℝ] E')
    (hΛ : ∀ v, Λ v + 0 ∈ range J' ↔ v ∈ range J) {f : M → N} (hf : IsImmersion IM J ∞ f)
    (Φ : Diffeomorph J J' N N' ∞) : IsImmersion IM J' ∞ (Φ ∘ f) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hf
  let _ := hFg
  let _ := hFs
  exact IsImmersionOfComplement.isImmersion
    (fun x => (hF x).diffeomorph_comp_linear_OCX Λ hΛ Φ)

/-- Global form of `IsImmersionAtOfComplement.comp_diffeomorph_linear_OCX`. -/
theorem IsImmersion.comp_diffeomorph_linear_OCX (Λ : EP ≃L[ℝ] EM)
    (hΛ : ∀ v, Λ v + 0 ∈ range IM ↔ v ∈ range IP) {g : M → N} (hg : IsImmersion IM J ∞ g)
    (D : Diffeomorph IP IM P M ∞) : IsImmersion IP J ∞ (g ∘ D) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hg
  let _ := hFg
  let _ := hFs
  exact IsImmersionOfComplement.isImmersion
    (fun x => (hF (D x)).comp_diffeomorph_linear_OCX Λ hΛ D)

/-- A smooth embedding followed by a cross-model diffeomorphism (linear range correspondence). -/
theorem IsSmoothEmbedding.diffeomorph_comp_linear_OCX (Λ : E ≃L[ℝ] E')
    (hΛ : ∀ v, Λ v + 0 ∈ range J' ↔ v ∈ range J) {f : M → N}
    (hf : IsSmoothEmbedding IM J ∞ f) (Φ : Diffeomorph J J' N N' ∞) :
    IsSmoothEmbedding IM J' ∞ (Φ ∘ f) :=
  ⟨hf.isImmersion.diffeomorph_comp_linear_OCX Λ hΛ Φ,
    Φ.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

/-- A smooth embedding precomposed with a cross-model diffeomorphism (linear range
correspondence). -/
theorem IsSmoothEmbedding.comp_diffeomorph_linear_OCX (Λ : EP ≃L[ℝ] EM)
    (hΛ : ∀ v, Λ v + 0 ∈ range IM ↔ v ∈ range IP) {g : M → N}
    (hg : IsSmoothEmbedding IM J ∞ g) (D : Diffeomorph IP IM P M ∞) :
    IsSmoothEmbedding IP J ∞ (g ∘ D) :=
  ⟨hg.isImmersion.comp_diffeomorph_linear_OCX Λ hΛ D,
    hg.isEmbedding.comp D.toHomeomorph.isEmbedding⟩

end Linear

end Manifold
