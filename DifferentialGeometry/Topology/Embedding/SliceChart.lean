/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open scoped ContDiff Manifold

namespace Manifold

open Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

theorem IsImmersionAtOfComplement.exists_contMDiffOn_slice_chart [J.Boundaryless]
    {x : M} (h : IsImmersionAtOfComplement F I J n f x) (hf : IsInducing f) :
    ∃ Φ : OpenPartialHomeomorph N (E × F), f x ∈ Φ.source ∧
      ContMDiffOn J 𝓘(𝕜, E × F) n Φ Φ.source ∧
      ContMDiffOn 𝓘(𝕜, E × F) J n Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range f) = Φ.target ∩ (range I ×ˢ ({0} : Set F)) := by
  let Ψ : OpenPartialHomeomorph N (E × F) :=
    h.codChart.transHomeomorph (J.toHomeomorph.trans h.equiv.toHomeomorph.symm)
  have hΨ_apply : ∀ p : N, Ψ p = h.equiv.symm ((h.codChart.extend J) p) := fun _ => rfl
  have hextend : ∀ y : M, (h.domChart.extend I) y = I (h.domChart y) := fun _ => rfl
  have hΨsmooth : ContMDiffOn J 𝓘(𝕜, E × F) n Ψ Ψ.source := by
    change ContMDiffOn J 𝓘(𝕜, E × F) n
      (h.equiv.symm ∘ h.codChart.extend J) h.codChart.source
    exact h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn
      (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas)
  have hΨsmooth_inv : ContMDiffOn 𝓘(𝕜, E × F) J n Ψ.symm Ψ.target := by
    change ContMDiffOn 𝓘(𝕜, E × F) J n
      ((h.codChart.extend J).symm ∘ h.equiv) Ψ.target
    refine (contMDiffOn_extend_symm h.codChart_mem_maximalAtlas).comp
      h.equiv.contDiff.contMDiff.contMDiffOn ?_
    intro q hq
    change J.symm (h.equiv q) ∈ h.codChart.target at hq
    exact ⟨J.symm (h.equiv q), hq, J.right_inv (by rw [J.range_eq_univ]; trivial)⟩
  have key : ∀ y ∈ h.domChart.source, Ψ (f y) = ((h.domChart.extend I) y, 0) := by
    intro y hy
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hwritten := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hwritten
    rw [hΨ_apply, hwritten, ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨W, hW, hWf⟩ := hf.isOpen_iff.1 h.domChart.open_source
  have hmemW : ∀ y : M, f y ∈ W ↔ y ∈ h.domChart.source := fun y => by
    rw [← hWf]
    exact Iff.rfl
  have hU : IsOpen (I.symm ⁻¹' h.domChart.target) :=
    h.domChart.open_target.preimage I.continuous_symm
  let V : Set N :=
    (Ψ.source ∩ Ψ ⁻¹' ((I.symm ⁻¹' h.domChart.target) ×ˢ (univ : Set F))) ∩ W
  have hVopen : IsOpen V := (Ψ.isOpen_inter_preimage (hU.prod isOpen_univ)).inter hW
  have hx : x ∈ h.domChart.source := h.mem_domChart_source
  have hfx : f x ∈ Ψ.source := h.mem_codChart_source
  have hfxV : f x ∈ V := by
    refine ⟨⟨hfx, ?_⟩, (hmemW x).2 hx⟩
    rw [mem_preimage, key x hx]
    exact ⟨by rw [mem_preimage, hextend, I.left_inv]; exact h.domChart.map_source hx,
      mem_univ _⟩
  let Φ := Ψ.restrOpen V hVopen
  have hiff : ∀ p ∈ Φ.source, p ∈ range f ↔ Φ p ∈ range I ×ˢ ({0} : Set F) := by
    intro p hp
    change p ∈ Ψ.source ∩ V at hp
    change p ∈ range f ↔ Ψ p ∈ range I ×ˢ ({0} : Set F)
    constructor
    · rintro ⟨y, rfl⟩
      have hy : y ∈ h.domChart.source := (hmemW y).1 hp.2.2
      rw [key y hy, hextend]
      exact ⟨mem_range_self _, rfl⟩
    · intro hps
      have hmem : (Ψ p).1 ∈ (h.domChart.extend I).target := by
        rw [h.domChart.extend_target]
        exact ⟨hp.2.1.2.1, hps.1⟩
      have hys : (h.domChart.extend I).symm (Ψ p).1 ∈ h.domChart.source := by
        rw [← h.domChart.extend_source (I := I)]
        exact (h.domChart.extend I).map_target hmem
      have hfy : Ψ (f ((h.domChart.extend I).symm (Ψ p).1)) = Ψ p := by
        rw [key _ hys, (h.domChart.extend I).right_inv hmem, ← (hps.2 : (Ψ p).2 = 0)]
      exact ⟨_, Ψ.injOn (h.source_subset_preimage_source hys) hp.1 hfy⟩
  refine ⟨Φ, ⟨hfx, hfxV⟩, hΨsmooth.mono inter_subset_left,
    hΨsmooth_inv.mono inter_subset_left, ?_⟩
  ext q
  constructor
  · rintro ⟨p, ⟨hps, hpr⟩, rfl⟩
    exact ⟨Φ.map_source hps, (hiff p hps).mp hpr⟩
  · rintro ⟨hqt, hqS⟩
    refine ⟨Φ.symm q, ⟨Φ.map_target hqt, ?_⟩, Φ.right_inv hqt⟩
    apply (hiff _ (Φ.map_target hqt)).mpr
    rwa [Φ.right_inv hqt]

theorem IsSmoothEmbedding.exists_contMDiffOn_slice_chart [J.Boundaryless]
    (h : IsSmoothEmbedding I J n f) (x : M) :
    ∃ Φ : OpenPartialHomeomorph N (E × h.isImmersion.complement), f x ∈ Φ.source ∧
      ContMDiffOn J 𝓘(𝕜, E × h.isImmersion.complement) n Φ Φ.source ∧
      ContMDiffOn 𝓘(𝕜, E × h.isImmersion.complement) J n Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range f) =
        Φ.target ∩ (range I ×ˢ ({0} : Set h.isImmersion.complement)) :=
  (h.isImmersion.isImmersionOfComplement_complement x).exists_contMDiffOn_slice_chart
    h.isEmbedding.isInducing

end Manifold
