import Mathlib.Geometry.Manifold.Diffeomorph

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Diffeomorph

theorem exists_restrict_opens
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
    {Ω : Opens M} {W : Opens N} (e : Diffeomorph I J Ω W ∞)
    (S : Opens M) (hSΩ : S ≤ Ω) :
    ∃ (Y : Opens N) (hYW : Y ≤ W),
      (Y : Set N) = Subtype.val '' (e '' (Subtype.val ⁻¹' (S : Set M))) ∧
      ∃ d : Diffeomorph I J S Y ∞,
        (∀ q : S, (d q : N) = (e ⟨q.val, hSΩ q.property⟩ : N)) ∧
        ∀ y : Y, (d.symm y : M) = (e.symm ⟨y.val, hYW y.property⟩ : M) := by
  let f : S → N := fun q => (e ⟨q.val, hSΩ q.property⟩ : N)
  have hfopen : IsOpenEmbedding f := W.isOpenEmbedding'.comp
    (e.toHomeomorph.isOpenEmbedding.comp (Opens.isOpenEmbedding_of_le hSΩ))
  let Y : Opens N := ⟨range f, hfopen.isOpen_range⟩
  have hYW : Y ≤ W := by
    rintro y ⟨q, rfl⟩
    exact (e ⟨q.val, hSΩ q.property⟩).property
  let d : S ≃ₜ Y := hfopen.isEmbedding.toHomeomorph
  have hd (q : S) : (d q : N) = f q := rfl
  let g : Y → Ω := fun y => e.symm ⟨y.val, hYW y.property⟩
  have hg : ContMDiff J I ∞ g := by
    apply e.symm.contMDiff.comp
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    exact contMDiff_subtype_val
  have hdinv (y : Y) : (d.symm y : M) = (g y : M) := by
    have heq : e ⟨(d.symm y).val, hSΩ (d.symm y).property⟩ = ⟨y.val, hYW y.property⟩ := by
      apply Subtype.ext
      change f (d.symm y) = y.val
      rw [← hd, d.apply_symm_apply]
    exact (congrArg Subtype.val (e.symm_apply_eq.mpr heq.symm)).symm
  have hdf : ContMDiff I J ∞ d := by
    apply (ContMDiff.subtypeVal_comp_iff Y d).mp
    change ContMDiff I J ∞ f
    have hj : ContMDiff I I ∞ (fun q : S => (⟨q.val, hSΩ q.property⟩ : Ω)) := by
      apply (ContMDiff.subtypeVal_comp_iff Ω _).mp
      exact contMDiff_subtype_val
    exact (contMDiff_subtype_val (U := W)).comp (e.contMDiff.comp hj)
  have hdi : ContMDiff J I ∞ d.symm := by
    apply (ContMDiff.subtypeVal_comp_iff S d.symm).mp
    have hh := (contMDiff_subtype_val (U := Ω)).comp hg
    exact hh.congr hdinv
  refine ⟨Y, hYW, ?_, ⟨d.toEquiv, hdf, hdi⟩, hd, hdinv⟩
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨e ⟨q.val, hSΩ q.property⟩, ⟨⟨q.val, hSΩ q.property⟩, q.property, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨⟨q.val, hq⟩, rfl⟩

end Poincare.Manifold.Diffeomorph
