/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellPiercingNeighborhoods

/-!
# Stability of dual-cell piercing neighborhoods
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

open Classical in
theorem exists_perturbation_radius_of_pairwise_disjoint_nested_common_neighborhoods
    {ι : Type*} [Finite ι] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (A B J S₀ S₁ : ι → Set E)
    {U : Set E} (hU : IsOpen U)
    (hAB : ∀ i, IsNestedCommonAnnularDerivedNeighborhood K
      (A i) (B i) (J i) (S₀ i) (S₁ i))
    (hAU : ∀ i, A i ⊆ U)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : ι → E → E,
        (∀ i x, x ∈ A i → dist (g i x) x < δ) →
        (∀ i, g i '' A i ⊆ U) ∧
        Pairwise (fun i j => Disjoint (g i '' A i) (g j '' A j)) ∧
        Pairwise fun i j => Disjoint (g i '' B i) (g j '' B j) := by
  have hAcompact (i : ι) : IsCompact (A i) :=
    (hAB i).1.isPolyhedron.isCompact
  have hinside (i : ι) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
        Metric.thickening δ (A i) ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := (hAcompact i).exists_thickening_subset_open hU (hAU i)
    exact ⟨ε, hε, fun δ _ hδε => (Metric.thickening_mono hδε.le _).trans hεU⟩
  obtain ⟨εU, hεU, hinside⟩ :=
    exists_pos_uniform_finite (fun i δ => Metric.thickening δ (A i) ⊆ U) hinside
  let P := {p : ι × ι // p.1 ≠ p.2}
  have hseparate (p : P) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
        Disjoint (Metric.thickening δ (A p.1.1))
          (Metric.thickening δ (A p.1.2)) := by
    obtain ⟨ε, hε, hεdis⟩ :=
      (hdis p.2).exists_thickenings (hAcompact p.1.1) (hAcompact p.1.2).isClosed
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
      ((image_mono (hAB i).inner_subset_outer).trans (hgA i))
      ((image_mono (hAB j).inner_subset_outer).trans (hgA j))

end DifferentialGeometry.Topology.PiecewiseLinear
