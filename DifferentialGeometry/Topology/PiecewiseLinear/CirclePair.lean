/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem exists_map_of_interval_parameters {A : Set E} {B : Set F}
    {γ : ℝ → E} {δ : ℝ → F} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) :
    ∃ f : E → F, IsPLHomeomorphOn f A B ∧ f (γ 0) = δ 0 ∧ f (γ 1) = δ 1 := by
  refine ⟨δ ∘ Function.invFunOn γ (Icc 0 1), hγ.symm.trans hδ, ?_, ?_⟩
  · change δ (Function.invFunOn γ (Icc 0 1) (γ 0)) = δ 0
    rw [hγ.bijOn.invOn_invFunOn.1 (by norm_num)]
  · change δ (Function.invFunOn γ (Icc 0 1) (γ 1)) = δ 1
    rw [hγ.bijOn.invOn_invFunOn.1 (by norm_num)]

theorem exists_isPLHomeomorphOn_pair_of_isPLSphere_one
    {S : Set E} {S' : Set F} (hS : IsPLSphere 1 S) (hS' : IsPLSphere 1 S')
    {p q : E} {p' q' : F} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (hp' : p' ∈ S') (hq' : q' ∈ S') (hpq' : p' ≠ q') :
    ∃ f : E → F, IsPLHomeomorphOn f S S' ∧ f p = p' ∧ f q = q' := by
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  obtain ⟨A', B', γ', δ', hγ', hδ', hγ'0, hγ'1, hδ'0, hδ'1, hunion', hinter'⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS' hp' hq' hpq'
  obtain ⟨f, hf, hf0, hf1⟩ := exists_map_of_interval_parameters hγ hγ'
  obtain ⟨g, hg, hg0, hg1⟩ := exists_map_of_interval_parameters hδ hδ'
  rw [hγ0, hγ'0] at hf0
  rw [hγ1, hγ'1] at hf1
  rw [hδ0, hδ'0] at hg0
  rw [hδ1, hδ'1] at hg1
  have hfg : EqOn f g (A ∩ B) := by
    rw [hinter]
    rintro x (rfl | rfl)
    · exact hf0.trans hg0.symm
    · exact hf1.trans hg1.symm
  have hsurj : SurjOn f (A ∩ B) (A' ∩ B') := by
    rw [hinter, hinter']
    rintro x (rfl | rfl)
    · exact ⟨p, by simp, hf0⟩
    · exact ⟨q, by simp, hf1⟩
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc (by norm_num)
  obtain ⟨H, hH, hHf, -⟩ := exists_isPLHomeomorphOn_union
    (hI.of_isPLHomeomorphOn hγ).isPolyhedron (hI.of_isPLHomeomorphOn hδ).isPolyhedron
    hf hg hfg hsurj
  rw [hunion, hunion'] at hH
  have hpA : p ∈ A := hγ0 ▸ hγ.bijOn.mapsTo (by norm_num)
  have hqA : q ∈ A := hγ1 ▸ hγ.bijOn.mapsTo (by norm_num)
  exact ⟨H, hH, (hHf hpA).trans hf0, (hHf hqA).trans hf1⟩

theorem exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary
    {D J P : Set E} {D' J' P' : Set F}
    {u : (Fin 3 → ℝ) → E} (hu : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (huJ : u '' stdSimplexBoundary 2 = J)
    {u' : (Fin 3 → ℝ) → F} (hu' : IsPLHomeomorphOn u' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D')
    (huJ' : u' '' stdSimplexBoundary 2 = J')
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) P)
    (hPD : P ⊆ D) (hinter : P ∩ J = {γ 0, γ 1})
    {γ' : ℝ → F} (hγ' : IsPLHomeomorphOn γ' (Icc 0 1) P')
    (hPD' : P' ⊆ D') (hinter' : P' ∩ J' = {γ' 0, γ' 1})
    {f : E → F} (hf : IsPLHomeomorphOn f J J')
    (hf0 : f (γ 0) = γ' 0) (hf1 : f (γ 1) = γ' 1) :
    ∃ G : E → F, IsPLHomeomorphOn G D D' ∧ EqOn G f J ∧ G '' P = P' := by
  obtain ⟨g, hg, hg0, hg1⟩ := exists_map_of_interval_parameters hγ hγ'
  have hJ : IsPLSphere 1 J := huJ ▸ hu.isPLSphere_image_stdSimplexBoundary
  have hP : IsPLBall 1 P := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hfg : EqOn f g (J ∩ P) := by
    rw [inter_comm, hinter]
    rintro x (rfl | rfl)
    · exact hf0.trans hg0.symm
    · exact hf1.trans hg1.symm
  have hsurj : SurjOn f (J ∩ P) (J' ∩ P') := by
    rw [inter_comm J P, hinter, inter_comm J' P', hinter']
    rintro x (rfl | rfl)
    · exact ⟨γ 0, by simp, hf0⟩
    · exact ⟨γ 1, by simp, hf1⟩
  obtain ⟨h, hh, hhf, hhg⟩ := exists_isPLHomeomorphOn_union
    hJ.isPolyhedron hP.isPolyhedron hf hg hfg hsurj
  obtain ⟨G, hG, hGh⟩ := exists_isPLHomeomorphOn_eqOn_disk_crosscut hu huJ hu' huJ'
    hγ hPD hinter hPD' hh (hhf.image_eq.trans hf.image_eq) (hhg.image_eq.trans hg.image_eq)
  refine ⟨G, hG, fun x hx => (hGh (Or.inl hx)).trans (hhf hx), ?_⟩
  exact (show EqOn G g P from fun x hx => (hGh (Or.inr hx)).trans (hhg hx)).image_eq.trans
      hg.image_eq

theorem exists_isPLHomeomorphOn_disk_pair_eqOn_boundary
    {A B J P Q : Set E} {A' B' J' P' Q' : Set F}
    {u v : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A)
    (hv : IsPLHomeomorphOn v (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B)
    (huJ : u '' stdSimplexBoundary 2 = J) (hvJ : v '' stdSimplexBoundary 2 = J)
    (hAB : A ∩ B = J)
    {u' v' : (Fin 3 → ℝ) → F}
    (hu' : IsPLHomeomorphOn u' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A')
    (hv' : IsPLHomeomorphOn v' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B')
    (huJ' : u' '' stdSimplexBoundary 2 = J') (hvJ' : v' '' stdSimplexBoundary 2 = J')
    (hAB' : A' ∩ B' = J')
    {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) P)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) Q)
    (hPA : P ⊆ A) (hQB : Q ⊆ B)
    (hPJ : P ∩ J = {γ 0, γ 1}) (hQJ : Q ∩ J = {δ 0, δ 1})
    {γ' δ' : ℝ → F} (hγ' : IsPLHomeomorphOn γ' (Icc 0 1) P')
    (hδ' : IsPLHomeomorphOn δ' (Icc 0 1) Q')
    (hPA' : P' ⊆ A') (hQB' : Q' ⊆ B')
    (hPJ' : P' ∩ J' = {γ' 0, γ' 1}) (hQJ' : Q' ∩ J' = {δ' 0, δ' 1})
    {f : E → F} (hf : IsPLHomeomorphOn f J J')
    (hfγ0 : f (γ 0) = γ' 0) (hfγ1 : f (γ 1) = γ' 1)
    (hfδ0 : f (δ 0) = δ' 0) (hfδ1 : f (δ 1) = δ' 1) :
    ∃ G : E → F, IsPLHomeomorphOn G (A ∪ B) (A' ∪ B') ∧ EqOn G f J ∧
      G '' A = A' ∧ G '' B = B' ∧ G '' P = P' ∧ G '' Q = Q' := by
  obtain ⟨g, hg, hgf, hgP⟩ := exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary
    hu huJ hu' huJ' hγ hPA hPJ hγ' hPA' hPJ' hf hfγ0 hfγ1
  obtain ⟨h, hh, hhf, hhQ⟩ := exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary
    hv hvJ hv' hvJ' hδ hQB hQJ hδ' hQB' hQJ' hf hfδ0 hfδ1
  have hgh : EqOn g h (A ∩ B) := by
    rw [hAB]
    exact hgf.trans hhf.symm
  have hsurj : SurjOn g (A ∩ B) (A' ∩ B') := by
    rw [hAB, hAB']
    exact (hgf.image_eq.trans hf.image_eq).superset
  obtain ⟨G, hG, hGg, hGh⟩ := exists_isPLHomeomorphOn_union
    (show IsPLBall 2 A from ⟨u, hu⟩).isPolyhedron (show IsPLBall 2 B from ⟨v, hv⟩).isPolyhedron
    hg hh hgh hsurj
  have hJA : J ⊆ A := hAB.symm.subset.trans inter_subset_left
  exact ⟨G, hG, (hGg.mono hJA).trans hgf, hGg.image_eq.trans hg.image_eq,
    hGh.image_eq.trans hh.image_eq, (hGg.mono hPA).image_eq.trans hgP,
    (hGh.mono hQB).image_eq.trans hhQ⟩

theorem exists_isPLHomeomorphOn_disk_pair_map_crosscuts
    {A B J P Q : Set E} {A' B' J' P' Q' : Set F}
    {u v : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A)
    (hv : IsPLHomeomorphOn v (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B)
    (huJ : u '' stdSimplexBoundary 2 = J) (hvJ : v '' stdSimplexBoundary 2 = J)
    (hAB : A ∩ B = J)
    {u' v' : (Fin 3 → ℝ) → F}
    (hu' : IsPLHomeomorphOn u' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A')
    (hv' : IsPLHomeomorphOn v' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B')
    (huJ' : u' '' stdSimplexBoundary 2 = J') (hvJ' : v' '' stdSimplexBoundary 2 = J')
    (hAB' : A' ∩ B' = J')
    {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) P)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) Q)
    (hPA : P ⊆ A) (hQB : Q ⊆ B)
    (hPJ : P ∩ J = {γ 0, γ 1}) (hQJ : Q ∩ J = {δ 0, δ 1})
    (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    {γ' δ' : ℝ → F} (hγ' : IsPLHomeomorphOn γ' (Icc 0 1) P')
    (hδ' : IsPLHomeomorphOn δ' (Icc 0 1) Q')
    (hPA' : P' ⊆ A') (hQB' : Q' ⊆ B')
    (hPJ' : P' ∩ J' = {γ' 0, γ' 1}) (hQJ' : Q' ∩ J' = {δ' 0, δ' 1})
    (hδ'0 : δ' 0 = γ' 0) (hδ'1 : δ' 1 = γ' 1) :
    ∃ G : E → F, IsPLHomeomorphOn G (A ∪ B) (A' ∪ B') ∧
      G '' J = J' ∧ G '' A = A' ∧ G '' B = B' ∧ G '' P = P' ∧ G '' Q = Q' ∧
      G (γ 0) = γ' 0 ∧ G (γ 1) = γ' 1 := by
  have hp : γ 0 ∈ J := (hPJ.symm.subset (by simp)).2
  have hq : γ 1 ∈ J := (hPJ.symm.subset (by simp)).2
  have hp' : γ' 0 ∈ J' := (hPJ'.symm.subset (by simp)).2
  have hq' : γ' 1 ∈ J' := (hPJ'.symm.subset (by simp)).2
  have hpq : γ 0 ≠ γ 1 := fun h => zero_ne_one (hγ.bijOn.injOn (by norm_num) (by norm_num) h)
  have hpq' : γ' 0 ≠ γ' 1 := fun h => zero_ne_one (hγ'.bijOn.injOn (by norm_num) (by norm_num) h)
  obtain ⟨f, hf, hf0, hf1⟩ := exists_isPLHomeomorphOn_pair_of_isPLSphere_one
    (huJ ▸ hu.isPLSphere_image_stdSimplexBoundary) (huJ' ▸ hu'.isPLSphere_image_stdSimplexBoundary)
    hp hq hpq hp' hq' hpq'
  obtain ⟨G, hG, hGf, hGA, hGB, hGP, hGQ⟩ := exists_isPLHomeomorphOn_disk_pair_eqOn_boundary
    hu hv huJ hvJ hAB hu' hv' huJ' hvJ' hAB' hγ hδ hPA hQB hPJ hQJ
    hγ' hδ' hPA' hQB' hPJ' hQJ' hf hf0 hf1 (by rw [hδ0, hδ'0, hf0]) (by rw [hδ1, hδ'1, hf1])
  exact ⟨G, hG, hGf.image_eq.trans hf.image_eq, hGA, hGB, hGP, hGQ,
    (hGf hp).trans hf0, (hGf hq).trans hf1⟩
end DifferentialGeometry.Topology.PiecewiseLinear
