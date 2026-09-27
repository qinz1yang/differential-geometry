/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionOutsideTools

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y]

theorem IsPLTorus.carriesFirstHomologyOnto_image_sdiff_of_disk {ι : Type*} [Finite ι]
    {Θ Tr J D : Set E3} {C : ι → Set E3} (hΘ : IsPLTorus Θ) (hC : ∀ i, IsPLSphere 1 (C i))
    (hCd : Pairwise fun i j => Disjoint (C i) (C j)) (hCeq : ⋃ i, C i = Tr) (hTrΘ : Tr ⊆ Θ)
    (hJc : IsConnected J) (hJcl : IsClosed J) (hJTr : J ⊆ Tr)
    (hJo : ∃ O : Set E3, IsOpen O ∧ J ⊆ O ∧ Tr ∩ O ⊆ J) (hDΘ : D ⊆ Θ) (hJD : J ⊆ D)
    (hDc : IsClosed D) (hDJ : (D \ J).Nonempty)
    (hDo : ∀ z ∈ D \ J, ∃ O : Set E3, IsOpen O ∧ z ∈ O ∧ O ∩ Θ ⊆ D) (hΘD : (Θ \ D).Nonempty)
    {φ : E3 → Y} {S : Set Y} (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ) (hS : φ '' Θ ⊆ S)
    (hZ : CarriesFirstHomologyOnto (φ '' Tr) S) :
    CarriesFirstHomologyOnto (φ '' (Tr \ J)) S := by
  classical
  have hCΘ : ∀ i, C i ⊆ Θ := fun i => (subset_iUnion C i).trans (hCeq.subset.trans hTrΘ)
  have hTrU : ∀ z ∈ Tr, ∃ i, z ∈ C i := fun z hz => mem_iUnion.mp (hCeq.symm ▸ hz)
  obtain ⟨p, hp⟩ := hJc.nonempty
  obtain ⟨i₀, hi₀⟩ := hTrU p (hJTr hp)
  obtain ⟨O, hO, hJO, hTrO⟩ := hJo
  have hCi₀J : C i₀ ⊆ J := by
    have hsub : C i₀ ⊆ J ∪ Oᶜ := by
      intro z hz
      by_cases hzO : z ∈ O
      · exact Or.inl (hTrO ⟨hCeq ▸ mem_iUnion.mpr ⟨i₀, hz⟩, hzO⟩)
      · exact Or.inr hzO
    have hdisj : C i₀ ∩ (J ∩ Oᶜ) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun z hz => hz.2.2 (hJO hz.2.1)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hC i₀).isConnected.isPreconnected
      J Oᶜ hJcl hO.isClosed_compl hsub hdisj with h | h
    · exact h
    · exact absurd (hJO hp) (h hi₀)
  have hVc : IsClosed (⋃ (i) (_ : i ≠ i₀), C i) :=
    isClosed_iUnion_of_finite fun i =>
      isClosed_iUnion_of_finite fun _ => (hC i).isPolyhedron.isClosed
  have hJCi₀ : J ⊆ C i₀ := by
    have hsub : J ⊆ C i₀ ∪ ⋃ (i) (_ : i ≠ i₀), C i := by
      intro z hz
      obtain ⟨i, hi⟩ := hTrU z (hJTr hz)
      by_cases h : i = i₀
      · exact Or.inl (h ▸ hi)
      · exact Or.inr (mem_iUnion₂.mpr ⟨i, h, hi⟩)
    have hdisj : J ∩ (C i₀ ∩ ⋃ (i) (_ : i ≠ i₀), C i) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz.2.2
      exact Set.disjoint_left.mp (hCd (Ne.symm hi)) hz.2.1 hzi
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hJc.isPreconnected _ _
      (hC i₀).isPolyhedron.isClosed hVc hsub hdisj with h | h
    · exact h
    · obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (h hp)
      exact absurd hpi (Set.disjoint_left.mp (hCd (Ne.symm hi)) hi₀)
  have hJeq : C i₀ = J := Subset.antisymm hCi₀J hJCi₀
  have hTrJ : Tr \ J = ⋃ (i) (_ : i ≠ i₀), C i := by
    ext z
    constructor
    · rintro ⟨hz, hzJ⟩
      obtain ⟨i, hi⟩ := hTrU z hz
      refine mem_iUnion₂.mpr ⟨i, fun h => hzJ ?_, hi⟩
      rw [← hJeq, ← h]
      exact hi
    · intro hz
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
      refine ⟨hCeq ▸ mem_iUnion.mpr ⟨i, hzi⟩, fun hzJ => ?_⟩
      rw [← hJeq] at hzJ
      exact Set.disjoint_left.mp (hCd hi) hzi hzJ
  choose! Oz hOz hzOz hOzΘ using hDo
  have hsep : ¬ IsPreconnected (Θ \ C i₀) := by
    rw [hJeq]
    intro hpc
    have hu : IsOpen (⋃ z ∈ D \ J, Oz z) := isOpen_biUnion fun z hz => hOz z hz
    have hcov : Θ \ J ⊆ (⋃ z ∈ D \ J, Oz z) ∪ Dᶜ := by
      rintro z ⟨hz, hzJ⟩
      by_cases hzD : z ∈ D
      · exact Or.inl (mem_iUnion₂.mpr ⟨z, ⟨hzD, hzJ⟩, hzOz z ⟨hzD, hzJ⟩⟩)
      · exact Or.inr hzD
    have hin : ∀ z ∈ Θ, z ∈ ⋃ z ∈ D \ J, Oz z → z ∈ D := by
      intro z hz hzu
      obtain ⟨z', hz', hzz'⟩ := mem_iUnion₂.mp hzu
      exact hOzΘ z' hz' ⟨hzz', hz⟩
    have hdisj : (Θ \ J) ∩ ((⋃ z ∈ D \ J, Oz z) ∩ Dᶜ) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun z hz => hz.2.2 (hin z hz.1.1 hz.2.1)
    rcases isPreconnected_iff_subset_of_disjoint.mp hpc _ _ hu hDc.isOpen_compl hcov hdisj with
      h | h
    · obtain ⟨z, hzΘ, hzD⟩ := hΘD
      exact hzD (hin z hzΘ (h ⟨hzΘ, fun hzJ => hzD (hJD hzJ)⟩))
    · obtain ⟨z, hzD, hzJ⟩ := hDJ
      exact h ⟨hDΘ hzD, hzJ⟩ hzD
  have hZ' : CarriesFirstHomologyOnto (φ '' ⋃ i, C i) S := by
    rw [hCeq]
    exact hZ
  have hres := hΘ.carriesFirstHomologyOnto_image_iUnion_ne_of_not_isPreconnected hC hCΘ hCd hφ
    hφi hS hZ' hsep
  rw [hTrJ]
  exact hres

end DifferentialGeometry.Topology.PiecewiseLinear
