/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallCyclePair
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem inter_subset_frontier_of_regularClosed_of_interior_inter_eq_empty
    {A B : Set E3} (hB : closure (interior B) = B) (hAB : interior (A ∩ B) = ∅) :
    A ∩ B ⊆ frontier A := by
  have hdis : interior A ∩ interior B = ∅ := by rwa [interior_inter] at hAB
  intro x hx
  refine ⟨subset_closure hx.1, fun hxA => ?_⟩
  have hxcl : x ∈ closure (interior A ∩ interior B) :=
    isOpen_interior.inter_closure ⟨hxA, hB.symm ▸ hx.2⟩
  simp only [hdis, closure_empty, mem_empty_iff_false] at hxcl

private theorem inter_subset_frontier_of_inter_eq_disks
    {A B D₀ D₁ : Set E3} (hB : IsPLBall 3 B)
    (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁) (hinter : A ∩ B = D₀ ∪ D₁) :
    A ∩ B ⊆ frontier A := by
  have hI : interior (A ∩ B) = ∅ := by
    rw [hinter, interior_union_isClosed_of_interior_empty hD₀.isPolyhedron.isClosed
      (hD₁.interior_eq_empty_of_lt_finrank (by simp))]
    exact hD₀.interior_eq_empty_of_lt_finrank (by simp)
  exact inter_subset_frontier_of_regularClosed_of_interior_inter_eq_empty hB.closure_interior hI

private theorem disk_union_subset_boundaryComplex [DecidableEq E3]
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {B D₀ D₁ : Set E3} (hB : IsPLBall 3 B) (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁)
    (hinter : K.space ∩ B = D₀ ∪ D₁) : D₀ ∪ D₁ ⊆ (boundaryComplex 3 K).space := by
  have hbd : (boundaryComplex 3 K).space = frontier K.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) (by simp) K
      hK.isCombinatorialManifoldWithBoundary).symm
  rw [hbd, ← hinter]
  exact inter_subset_frontier_of_inter_eq_disks hB hD₀ hD₁ hinter

private theorem exists_cylindricalDiagram_of_inter_eq_disjoint_disks
    {A B D₀ D₁ : Set E3} (hA : IsPLBall 3 A) (hB : IsPLBall 3 B)
    (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁) (hdis : Disjoint D₀ D₁)
    (hinter : A ∩ B = D₀ ∪ D₁) :
    ∃ f : (Fin 3 → ℝ) × ℝ → E3,
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (A ∪ B) := by
  classical
  let _ : DecidableEq E3 := Classical.decEq _
  obtain ⟨K, hKfin, hKA⟩ := hA.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 3 K.space := hKA.symm ▸ hA
  have hL : IsPLBall 3 L.space := hLB.symm ▸ hB
  have hKL : K.space ∩ L.space = D₀ ∪ D₁ := by rw [hKA, hLB, hinter]
  have hDK := disk_union_subset_boundaryComplex K hK hL hD₀ hD₁ hKL
  have hDL := disk_union_subset_boundaryComplex L hL hK hD₀ hD₁
    ((inter_comm L.space K.space).trans hKL)
  obtain ⟨g, hg⟩ := hD₀
  obtain ⟨f, hf, _⟩ := exists_cylindricalDiagram_of_ball_pair (isPLBall_stdSimplex 2) K L hK hL
    hD₁ hdis (subset_union_left.trans hDK) (subset_union_right.trans hDK)
    (subset_union_left.trans hDL) (subset_union_right.trans hDL) hKL hg
  refine ⟨f, ?_⟩
  rwa [hKA, hLB] at hf

theorem isCombinatorialSolidTorus_union_of_inter_eq_disjoint_disks
    {A B D₀ D₁ : Set E3} (hA : IsPLBall 3 A) (hB : IsPLBall 3 B)
    (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁) (hdis : Disjoint D₀ D₁)
    (hinter : A ∩ B = D₀ ∪ D₁) : IsCombinatorialSolidTorus (A ∪ B) := by
  obtain ⟨f, hf⟩ := exists_cylindricalDiagram_of_inter_eq_disjoint_disks hA hB hD₀ hD₁ hdis hinter
  exact hf.isCombinatorialSolidTorus (isPLBall_stdSimplex 2) (by simp)

private theorem finite_cover_mem_nhdsWithin {ι : Type*} [Finite ι]
    (C : ι → Set E3) (hC : ∀ i, IsClosed (C i)) {p : E3} (J : Set ι)
    (hp : ∀ i, p ∈ C i → i ∈ J) : (⋃ i ∈ J, C i) ∈ 𝓝[⋃ i, C i] p := by
  classical
  refine mem_nhdsWithin.mpr ⟨(⋃ i ∉ J, C i)ᶜ,
    (isClosed_iUnion_of_finite fun i =>
      isClosed_iUnion_of_finite fun _ => hC i).isOpen_compl, ?_, ?_⟩
  · intro hpU
    obtain ⟨i, hiJ, hi⟩ := mem_iUnion₂.mp hpU
    exact hiJ (hp i hi)
  · rintro y ⟨hy, hyC⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyC
    have hiJ : i ∈ J := by
      by_contra hiJ
      exact hy (mem_iUnion₂.mpr ⟨i, hiJ, hi⟩)
    exact mem_iUnion₂.mpr ⟨i, hiJ, hi⟩

private theorem isCombinatorialManifoldWithBoundary_iUnion_of_cycle
    {n : ℕ} (C : Fin (n + 3) → Set E3) (hC : ∀ i, IsPLBall 3 (C i))
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅)
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] (hK : K.space = ⋃ i, C i) :
    IsCombinatorialManifoldWithBoundary 3 K := by
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods (n := 2)
  intro p hp
  rw [hK] at hp ⊢
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  by_cases hother : ∃ j, j ≠ i ∧ p ∈ C j
  · obtain ⟨j, hji, hj⟩ := hother
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj i j := by
      by_contra hnot
      exact Set.disjoint_left.mp (hdis i j hji.symm hnot) hi hj
    have hD := hnext i j hadj
    have hDleft : C i ∩ C j ⊆ frontier (C i) :=
      (hC j).inter_subset_frontier_of_isPLBall hD (by norm_num)
    have hDright : C i ∩ C j ⊆ frontier (C j) := by
      rw [inter_comm]
      exact (hC i).inter_subset_frontier_of_isPLBall (inter_comm _ _ ▸ hD) (by norm_num)
    have hball := isPLBall_union_of_inter_isPLBall_two (hC i) (hC j) hD hDleft hDright
    refine ⟨C i ∪ C j, hball, union_subset (subset_iUnion C i) (subset_iUnion C j), ?_⟩
    have hnear := finite_cover_mem_nhdsWithin C (fun k => (hC k).isPolyhedron.isClosed)
      ({i, j} : Set (Fin (n + 3))) (p := p) fun k hk => by
        by_cases hki : k = i
        · exact Or.inl hki
        · by_cases hkj : k = j
          · exact Or.inr hkj
          · have hbad : p ∈ C i ∩ C j ∩ C k := ⟨⟨hi, hj⟩, hk⟩
            rw [htriple i j k hji.symm (Ne.symm hki) (Ne.symm hkj)] at hbad
            exact hbad.elim
    simpa using hnear
  · refine ⟨C i, hC i, subset_iUnion C i, ?_⟩
    have hnear := finite_cover_mem_nhdsWithin C (fun k => (hC k).isPolyhedron.isClosed)
      ({i} : Set (Fin (n + 3))) (p := p) fun k hk => by
        by_contra hki
        exact hother ⟨k, hki, hk⟩
    simpa using hnear

theorem isCombinatorialSolidTorus_iUnion_of_cycle {n : ℕ}
    (C : Fin (n + 3) → Set E3) (hC : ∀ i, IsPLBall 3 (C i))
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅) :
    IsCombinatorialSolidTorus (⋃ i, C i) := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ :=
    (IsPolyhedron.iUnion fun i => (hC i).isPolyhedron).exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK := isCombinatorialManifoldWithBoundary_iUnion_of_cycle C hC hnext hdis htriple K hKspace
  obtain ⟨A, B, D₀, D₁, hA, hB, hD₀, hD₁, hDD, hcover, hinter⟩ :=
    hK.exists_isPLBall_pair_cover_of_cycle C hC
      (fun i => hKspace.symm ▸ subset_iUnion C i) hnext hdis htriple
  rw [← hcover]
  exact isCombinatorialSolidTorus_union_of_inter_eq_disjoint_disks hA hB hD₀ hD₁ hDD hinter

end DifferentialGeometry.Topology.PiecewiseLinear
