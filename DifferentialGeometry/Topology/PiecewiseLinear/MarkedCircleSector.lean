/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePair
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_marked_sector_cover
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Finite ι]
    {S : Set E} {S' : Set F} {P : ι → Set E} {Q : ι → Set F}
    {p : ι → E} {q : ι → F} {f : ι → E → F}
    (hPcover : (⋃ i, P i) = S) (hQcover : (⋃ i, Q i) = S')
    (hP : ∀ i, IsPolyhedron (P i))
    (hf : ∀ i, IsPLHomeomorphOn (f i) (P i) (Q i))
    (hfg : ∀ i j, EqOn (f i) (f j) (P i ∩ P j))
    (hmeet : ∀ i j, f i '' (P i ∩ P j) = Q i ∩ Q j)
    (hp : ∀ k, p k ∈ S)
    (hlabel : ∀ i k, p k ∈ P i → f i (p k) = q k) :
    ∃ g : E → F, IsPLHomeomorphOn g S S' ∧ (∀ i, EqOn g (f i) (P i)) ∧
      ∀ k, g (p k) = q k := by
  obtain ⟨g, hg, hgi⟩ := exists_isPLHomeomorphOn_iUnion hP hf hfg hmeet
  have hgi' : ∀ i, EqOn g (f i) (P i) := hgi
  have hlabel' : ∀ k, ∃ i, p k ∈ P i := by
    intro k
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hPcover.symm ▸ hp k)
    exact ⟨i, hi⟩
  refine ⟨g, hPcover ▸ hQcover ▸ hg, hgi', ?_⟩
  intro k
  obtain ⟨i, hi⟩ := hlabel' k
  exact (hgi' i hi).trans (hlabel i k hi)

theorem exists_isPLHomeomorphOn_marked_circle_sector_of_arc_cover
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Finite ι]
    {S : Set E} {S' : Set F} {P : ι → Set E} {Q : ι → Set F}
    {p : ι → E} {q : ι → F} (γ : ι → ℝ → E) (δ : ι → ℝ → F)
    (a b : ι → ι)
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (P i))
    (hδ : ∀ i, IsPLHomeomorphOn (δ i) (Icc 0 1) (Q i))
    (hγ0 : ∀ i, γ i 0 = p (a i)) (hγ1 : ∀ i, γ i 1 = p (b i))
    (hδ0 : ∀ i, δ i 0 = q (a i)) (hδ1 : ∀ i, δ i 1 = q (b i))
    (hPcover : (⋃ i, P i) = S) (hQcover : (⋃ i, Q i) = S')
    (hp : ∀ k, p k ∈ S)
    (hpoint : ∀ i k, p k ∈ P i → k = a i ∨ k = b i)
    (hpointQ : ∀ i k, q k ∈ Q i → k = a i ∨ k = b i)
    (hPinter : ∀ i j, i ≠ j → ∀ x ∈ P i ∩ P j, ∃ k, x = p k)
    (hQinter : ∀ i j, i ≠ j → ∀ y ∈ Q i ∩ Q j, ∃ k, y = q k) :
    ∃ g : E → F, IsPLHomeomorphOn g S S' ∧
      (∀ i, EqOn g (δ i ∘ Function.invFunOn (γ i) (Icc 0 1)) (P i)) ∧
      ∀ k, g (p k) = q k := by
  let f : ι → E → F := fun i => δ i ∘ Function.invFunOn (γ i) (Icc 0 1)
  have hf : ∀ i, IsPLHomeomorphOn (f i) (P i) (Q i) := by
    intro i
    exact (hγ i).symm.trans (hδ i)
  have hPpoly : ∀ i, IsPolyhedron (P i) := by
    intro i
    exact ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn (hγ i)).isPolyhedron
  have hlabel : ∀ i k, p k ∈ P i → f i (p k) = q k := by
    intro i k hik
    rcases hpoint i k hik with rfl | rfl
    · dsimp [f]
      rw [← hγ0 i, (hγ i).bijOn.invOn_invFunOn.1 (by norm_num), hδ0 i]
    · dsimp [f]
      rw [← hγ1 i, (hγ i).bijOn.invOn_invFunOn.1 (by norm_num), hδ1 i]
  have hmark : ∀ i k, p k ∈ P i ↔ q k ∈ Q i := by
    intro i k
    constructor
    · intro hik
      rcases hpoint i k hik with rfl | rfl
      · rw [← hδ0 i]
        exact (hδ i).bijOn.mapsTo (by norm_num)
      · rw [← hδ1 i]
        exact (hδ i).bijOn.mapsTo (by norm_num)
    · intro hik
      rcases hpointQ i k hik with rfl | rfl
      · rw [← hγ0 i]
        exact (hγ i).bijOn.mapsTo (by norm_num)
      · rw [← hγ1 i]
        exact (hγ i).bijOn.mapsTo (by norm_num)
  have hfg : ∀ i j, EqOn (f i) (f j) (P i ∩ P j) := by
    intro i j x hx
    by_cases hij : i = j
    · subst j
      rfl
    · obtain ⟨k, hk⟩ := hPinter i j hij x hx
      have hxi : p k ∈ P i := hk ▸ hx.1
      have hxj : p k ∈ P j := hk ▸ hx.2
      rw [hk, hlabel i k hxi, hlabel j k hxj]
  have hmeet : ∀ i j, f i '' (P i ∩ P j) = Q i ∩ Q j := by
    intro i j
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨(hf i).bijOn.mapsTo hx.1, ?_⟩
      rw [hfg i j hx]
      exact (hf j).bijOn.mapsTo hx.2
    · intro y hy
      by_cases hij : i = j
      · subst j
        obtain ⟨x, hx, hxy⟩ := (hf i).bijOn.surjOn hy.1
        exact ⟨x, ⟨hx, hx⟩, hxy⟩
      · obtain ⟨k, hk⟩ := hQinter i j hij y hy
        have hqk : q k ∈ Q i ∩ Q j := hk ▸ hy
        have hpk : p k ∈ P i ∩ P j :=
          ⟨(hmark i k).mpr hqk.1, (hmark j k).mpr hqk.2⟩
        exact ⟨p k, hpk, (hlabel i k hpk.1).trans hk.symm⟩
  obtain ⟨g, hg, hgi, hlabels⟩ := exists_isPLHomeomorphOn_marked_sector_cover
    hPcover hQcover hPpoly hf hfg hmeet hp hlabel
  refine ⟨g, hg, ?_, hlabels⟩
  intro i
  exact hgi i

end DifferentialGeometry.Topology.PiecewiseLinear
