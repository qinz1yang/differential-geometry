import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H'' : Type*} [TopologicalSpace H''] {L : ModelWithCorners 𝕜 F H''}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H'' Q] [Zero Q]
  {n : ℕ∞ω} {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}

theorem exists_contMDiff_extension_of_hasCompactSupport
    (c : Diffeomorph I J U V n) {k : N → Q}
    (hk : ContMDiffOn J L n k V) (hkc : HasCompactSupport k)
    (hkv : tsupport k ⊆ V) :
    ∃ h : M → Q, ContMDiff I L n h ∧ HasCompactSupport h ∧
      (∀ x : U, h x = k (c x)) ∧
      tsupport h = (fun y : V => (c.symm y : M)) ''
        (Subtype.val ⁻¹' tsupport k) ∧
      tsupport h ⊆ U ∧ Set.EqOn h 0 (U : Set M)ᶜ := by
  let kV : V → Q := fun y => k y
  let kU : U → Q := fun x => k (c x)
  have hV : tsupport kV = Subtype.val ⁻¹' tsupport k := by
    change closure (Function.support (k ∘ Subtype.val)) =
      Subtype.val ⁻¹' closure (Function.support k)
    rw [Function.support_comp_eq_preimage]
    exact (V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val _).symm
  have hU : tsupport kU = c.symm '' (Subtype.val ⁻¹' tsupport k) := by
    change tsupport (kV ∘ c.toHomeomorph) = _
    rw [tsupport_comp_eq_preimage, hV]
    ext x
    constructor
    · intro hx
      exact ⟨c x, hx, c.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change (c (c.symm y) : N) ∈ tsupport k
      simpa only [Set.mem_preimage, Diffeomorph.apply_symm_apply] using hy
  have hVc : IsCompact (Subtype.val ⁻¹' tsupport k : Set V) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hkc
      (by simpa only [Subtype.range_coe] using hkv)
  have hUc : HasCompactSupport kU := by
    change IsCompact (tsupport kU)
    rw [hU]
    exact hVc.image c.symm.continuous
  have hUd : ContMDiff I L n kU := by
    intro x
    exact ((hk (c x) (c x).property).contMDiffAt
      (V.isOpen.mem_nhds (c x).property)).comp x
      ((contMDiff_subtype_val.comp c.contMDiff).contMDiffAt)
  let h : M → Q := Subtype.val.extend kU 0
  have hs : tsupport h = (fun y : V => (c.symm y : M)) ''
      (Subtype.val ⁻¹' tsupport k) := by
    rw [hUc.tsupport_extend_zero continuous_subtype_val Subtype.val_injective, hU,
      Set.image_image]
  have hsU : tsupport h ⊆ U := by
    rw [hs]
    rintro x ⟨y, hy, rfl⟩
    exact (c.symm y).property
  refine ⟨h, ContMDiff.extend_zero hUc hUd, hUc.extend_zero continuous_subtype_val,
    ?_, hs, hsU, ?_⟩
  · intro x
    exact Subtype.val_injective.extend_apply kU 0 x
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hsx => hx (hsU hsx))

end Diffeomorph
