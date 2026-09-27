/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Topology.UnitInterval

open Set

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem isOpen_range_from_open_chartedSpace
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace E N] {U : Set M} (hU : IsOpen U)
    (f : U → N) (hf : Continuous f) (hinj : Function.Injective f) : IsOpen (range f) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, rfl⟩
  let f₀ : M → N := Function.extend Subtype.val f (fun _ => f x)
  have heq (z : U) : f₀ z.val = f z :=
    Function.Injective.extend_apply Subtype.val_injective f (fun _ => f x) z
  have hc : ContinuousOn f₀ U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hf using 1
    funext z
    exact heq z
  have hi : InjOn f₀ U := by
    intro z hz w hw hzw
    exact congrArg (fun p : U => (p : M))
      (hinj ((heq ⟨z, hz⟩).symm.trans (hzw.trans (heq ⟨w, hw⟩))))
  have hopen := isOpen_image_of_continuousOn_injOn (E := E) hU hc hi
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨x.val, x.property, heq x⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, (heq ⟨z, hz⟩).symm⟩

variable {M : Type*} [TopologicalSpace M] [CompactSpace M] [ChartedSpace E (M × ℝ)]

theorem interior_range_prod_unitInterval
    (g : M × unitInterval → E) (hg : Continuous g) (hinj : Function.Injective g) :
    interior (range g) = g '' {p | (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1} := by
  let j : M × unitInterval → M × ℝ := fun p => (p.1, (p.2 : ℝ))
  have hj : _root_.Topology.IsEmbedding j :=
    _root_.Topology.IsEmbedding.id.prodMap _root_.Topology.IsEmbedding.subtypeVal
  have hemb : _root_.Topology.IsEmbedding g := (hg.isClosedEmbedding hinj).isEmbedding
  apply Subset.antisymm
  · intro y hy
    obtain ⟨a, rfl⟩ := interior_subset hy
    let F : interior (range g) → M × ℝ :=
      fun w => j (hemb.toHomeomorph.symm ⟨w.val, interior_subset w.property⟩)
    have hFc : Continuous F := hj.continuous.comp
      (hemb.toHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
    have hFi : Function.Injective F := by
      intro v w hvw
      have h := hemb.toHomeomorph.symm.injective (hj.injective hvw)
      exact Subtype.ext (congrArg (fun p : range g => (p : E)) h)
    have hFo : IsOpen (range F) :=
      isOpen_range_from_open_chartedSpace (E := E) isOpen_interior F hFc hFi
    have hFsub : range F ⊆ (univ : Set M) ×ˢ Icc (0 : ℝ) 1 := by
      rintro _ ⟨w, rfl⟩
      exact ⟨mem_univ _, (hemb.toHomeomorph.symm ⟨w.val, interior_subset w.property⟩).2.property⟩
    have hmem : j a ∈ range F := by
      refine ⟨⟨g a, hy⟩, ?_⟩
      change j (hemb.toHomeomorph.symm ⟨g a, interior_subset hy⟩) = j a
      have hga : hemb.toHomeomorph a = ⟨g a, interior_subset hy⟩ :=
        Subtype.ext (hemb.toHomeomorph_apply_coe a)
      rw [← hga, hemb.toHomeomorph.symm_apply_apply]
    have ha := interior_maximal hFsub hFo hmem
    refine ⟨a, ?_, rfl⟩
    change (a.2 : ℝ) ∈ Ioo (0 : ℝ) 1
    simpa only [interior_prod_eq, interior_univ, interior_Icc, mem_prod,
      mem_univ, true_and, j] using ha
  · rintro _ ⟨a, ha, rfl⟩
    let U : Set (M × ℝ) := univ ×ˢ Ioo (0 : ℝ) 1
    let k : U → M × unitInterval := fun p =>
      (p.val.1, ⟨p.val.2, Ioo_subset_Icc_self p.property.2⟩)
    have hkc : Continuous k := (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have hki : Function.Injective k := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg j hpq
    have hopen : IsOpen (range (g ∘ k)) :=
      isOpen_range_from_open_chartedSpace (E := E) (isOpen_univ.prod isOpen_Ioo)
        (g ∘ k) (hg.comp hkc) (hinj.comp hki)
    have hsub : range (g ∘ k) ⊆ range g := by
      rintro _ ⟨p, rfl⟩
      exact ⟨k p, rfl⟩
    exact interior_maximal hsub hopen ⟨⟨(a.1, (a.2 : ℝ)), mem_univ _, ha⟩, rfl⟩

theorem frontier_range_prod_unitInterval
    (g : M × unitInterval → E) (hg : Continuous g) (hinj : Function.Injective g) :
    frontier (range g) =
      g '' {p | (p.2 : ℝ) = 0} ∪ g '' {p | (p.2 : ℝ) = 1} := by
  have heq : (univ : Set (M × unitInterval)) \ {p | (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1} =
      {p | (p.2 : ℝ) = 0} ∪ {p | (p.2 : ℝ) = 1} := by
    ext p
    simp only [mem_sdiff, mem_univ, true_and, mem_ofPred_eq, mem_Ioo, mem_union]
    constructor
    · intro h
      rcases le_or_gt (p.2 : ℝ) 0 with h₀ | h₀
      · exact Or.inl (le_antisymm h₀ p.2.property.1)
      · exact Or.inr (le_antisymm p.2.property.2 (not_lt.mp (fun h₁ => h ⟨h₀, h₁⟩)))
    · rintro (h | h) <;> simp [h]
  rw [(isCompact_range hg).isClosed.frontier_eq, interior_range_prod_unitInterval g hg hinj,
    ← image_univ, ← image_sdiff hinj, heq, image_union]

noncomputable def prodIooHomeomorphInteriorRange
    (g : M × unitInterval → E) (hg : Continuous g) (hinj : Function.Injective g) :
    (M × Ioo (0 : ℝ) 1) ≃ₜ interior (range g) := by
  let j : M × Ioo (0 : ℝ) 1 → M × unitInterval :=
    Prod.map id (Set.inclusion Ioo_subset_Icc_self)
  have hj : _root_.Topology.IsEmbedding j :=
    _root_.Topology.IsEmbedding.id.prodMap (_root_.Topology.IsEmbedding.inclusion _)
  have hemb : _root_.Topology.IsEmbedding g := (hg.isClosedEmbedding hinj).isEmbedding
  have hrange : range (g ∘ j) = interior (range g) := by
    rw [interior_range_prod_unitInterval g hg hinj]
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨j p, p.2.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, ⟨(p.2 : ℝ), hp⟩), rfl⟩
  exact (hemb.comp hj).toHomeomorph.trans (Homeomorph.setCongr hrange)

end DifferentialGeometry.Topology
