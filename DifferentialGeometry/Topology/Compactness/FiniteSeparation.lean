/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace DifferentialGeometry.Topology.Compactness

private theorem exists_pos_uniform_finite {ι : Type*} [Finite ι]
    (P : ι → ℝ → Prop)
    (hP : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → P i δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i δ, 0 < δ → δ < ε → P i δ := by
  classical
  let _ := Fintype.ofFinite ι
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      exact ⟨1, zero_lt_one, fun i => isEmptyElim i⟩
  | inr hι =>
      let values : Finset ℝ := Finset.univ.image fun i => Classical.choose (hP i)
      have hvalues : values.Nonempty := by
        let i : ι := Classical.choice hι
        exact ⟨Classical.choose (hP i),
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      let ε := values.min' hvalues
      have hε : 0 < ε := by
        have hmem : ε ∈ values := Finset.min'_mem values hvalues
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        rw [← hi]
        exact (Classical.choose_spec (hP i)).1
      refine ⟨ε, hε, ?_⟩
      intro i δ hδ hδε
      apply (Classical.choose_spec (hP i)).2 δ hδ
      exact hδε.trans_le (Finset.min'_le values
        (Classical.choose (hP i)) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

theorem exists_open_supersets_preserving_disjointness
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      ∀ i j, R i j → Disjoint (U i) (U j) := by
  classical
  have hsep (i j : ι) : ∃ A B : Set X,
      IsOpen A ∧ IsOpen B ∧ K i ⊆ A ∧ K j ⊆ B ∧ (R i j → Disjoint A B) := by
    by_cases hij : R i j
    · obtain ⟨A, B, hA, hB, hi, hj, hd⟩ :=
        SeparatedNhds.of_isCompact_isCompact (hK i) (hK j) (hR i j hij)
      exact ⟨A, B, hA, hB, hi, hj, fun _ ↦ hd⟩
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, subset_univ _, subset_univ _,
        fun h ↦ (hij h).elim⟩
  choose A B hA hB hKA hKB hd using hsep
  let U (i : ι) := (⋂ j, A i j) ∩ (⋂ j, B j i)
  refine ⟨U, fun i ↦ (isOpen_iInter_of_finite (hA i)).inter
      (isOpen_iInter_of_finite fun j ↦ hB j i),
    fun i x hx ↦ ⟨mem_iInter.mpr fun j ↦ hKA i j hx,
      mem_iInter.mpr fun j ↦ hKB j i hx⟩, ?_⟩
  intro i j hij
  exact (hd i j hij).mono
    (fun _ hx ↦ mem_iInter.mp hx.1 j) (fun _ hx ↦ mem_iInter.mp hx.2 i)

theorem exists_perturbation_radius_preserving_containment_pairwise_disjoint
    {X ι : Type*} [MetricSpace X] [Finite ι] (A B : ι → Set X)
    (hA : ∀ i, IsCompact (A i)) {U : Set X} (hU : IsOpen U)
    (hAU : ∀ i, A i ⊆ U) (hBA : ∀ i, B i ⊆ A i)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : ι → X → X,
        (∀ i x, x ∈ A i → dist (g i x) x < δ) →
        (∀ i, g i '' A i ⊆ U) ∧
        Pairwise (fun i j => Disjoint (g i '' A i) (g j '' A j)) ∧
        Pairwise fun i j => Disjoint (g i '' B i) (g j '' B j) := by
  have hinside (i : ι) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
        Metric.thickening δ (A i) ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := (hA i).exists_thickening_subset_open hU (hAU i)
    exact ⟨ε, hε, fun δ _ hδε => (Metric.thickening_mono hδε.le _).trans hεU⟩
  obtain ⟨εU, hεU, hinside⟩ :=
    exists_pos_uniform_finite (fun i δ => Metric.thickening δ (A i) ⊆ U) hinside
  let P := {p : ι × ι // p.1 ≠ p.2}
  have hseparate (p : P) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
        Disjoint (Metric.thickening δ (A p.1.1))
          (Metric.thickening δ (A p.1.2)) := by
    obtain ⟨ε, hε, hεdis⟩ :=
      (hdis p.2).exists_thickenings (hA p.1.1) (hA p.1.2).isClosed
    exact ⟨ε, hε, fun δ _ hδε => hεdis.mono
      (Metric.thickening_mono hδε.le _) (Metric.thickening_mono hδε.le _)⟩
  obtain ⟨εD, hεD, hseparate⟩ := exists_pos_uniform_finite
    (fun p : P => fun δ => Disjoint (Metric.thickening δ (A p.1.1))
      (Metric.thickening δ (A p.1.2))) hseparate
  let δ := min εU εD / 2
  have hδ : 0 < δ := div_pos (lt_min hεU hεD) (by norm_num)
  have hδεU : δ < εU :=
    (half_lt_self (lt_min hεU hεD)).trans_le (min_le_left εU εD)
  have hδεD : δ < εD :=
    (half_lt_self (lt_min hεU hεD)).trans_le (min_le_right εU εD)
  refine ⟨δ, hδ, ?_⟩
  intro g hg
  have hgA (i : ι) : g i '' A i ⊆ Metric.thickening δ (A i) := by
    rintro y ⟨x, hx, rfl⟩
    exact Metric.mem_thickening_iff.mpr ⟨x, hx, hg i x hx⟩
  refine ⟨fun i => (hgA i).trans (hinside i δ hδ hδεU), ?_, ?_⟩
  · intro i j hij
    exact (hseparate ⟨(i, j), hij⟩ δ hδ hδεD).mono (hgA i) (hgA j)
  · intro i j hij
    exact (hseparate ⟨(i, j), hij⟩ δ hδ hδεD).mono
      ((image_mono (hBA i)).trans (hgA i))
      ((image_mono (hBA j)).trans (hgA j))

end DifferentialGeometry.Topology.Compactness
