/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalBoundaryMeridian

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem inter_subset_frontier_of_regular_closed
    {A B : Set E3} (hB : closure (interior B) = B) (hAB : interior (A ∩ B) = ∅) :
    A ∩ B ⊆ frontier A := by
  have hdis : interior A ∩ interior B = ∅ := by rwa [interior_inter] at hAB
  intro x hx
  refine ⟨subset_closure hx.1, fun hxA => ?_⟩
  have hxcl : x ∈ closure (interior A ∩ interior B) :=
    isOpen_interior.inter_closure ⟨hxA, hB.symm ▸ hx.2⟩
  simp only [hdis, closure_empty, mem_empty_iff_false] at hxcl

private theorem inter_subset_frontier_of_disk_pair
    {A B D₀ D₁ : Set E3} (hB : IsPLBall 3 B)
    (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁) (hinter : A ∩ B = D₀ ∪ D₁) :
    A ∩ B ⊆ frontier A := by
  have hI : interior (A ∩ B) = ∅ := by
    rw [hinter, interior_union_isClosed_of_interior_empty hD₀.isPolyhedron.isClosed
      (hD₁.interior_eq_empty_of_lt_finrank (by simp))]
    exact hD₀.interior_eq_empty_of_lt_finrank (by simp)
  exact inter_subset_frontier_of_regular_closed hB.closure_interior hI

private theorem disk_pair_subset_boundaryComplex [DecidableEq E3]
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {B D₀ D₁ : Set E3} (hB : IsPLBall 3 B) (hD₀ : IsPLBall 2 D₀) (hD₁ : IsPLBall 2 D₁)
    (hinter : K.space ∩ B = D₀ ∪ D₁) : D₀ ∪ D₁ ⊆ (boundaryComplex 3 K).space := by
  have hbd : (boundaryComplex 3 K).space = frontier K.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) (by simp) K
      hK.isCombinatorialManifoldWithBoundary).symm
  rw [hbd, ← hinter]
  exact inter_subset_frontier_of_disk_pair hB hD₀ hD₁ hinter

private theorem ball_subunion_mem_nhdsWithin {ι : Type*} [Finite ι]
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

private theorem isCombinatorialManifoldWithBoundary_of_cyclic_ball_union
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
    have hnear := ball_subunion_mem_nhdsWithin C (fun k => (hC k).isPolyhedron.isClosed)
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
    have hnear := ball_subunion_mem_nhdsWithin C (fun k => (hC k).isPolyhedron.isClosed)
      ({i} : Set (Fin (n + 3))) (p := p) fun k hk => by
        by_contra hki
        exact hother ⟨k, hki, hk⟩
    simpa using hnear

theorem exists_cylindricalDiagram_with_base_of_ball_pair
    {A B D₀ D₁ : Set E3} (hA : IsPLBall 3 A) (hB : IsPLBall 3 B)
    (hD₁ : IsPLBall 2 D₁) (hdis : Disjoint D₀ D₁) (hinter : A ∩ B = D₀ ∪ D₁)
    {q : (Fin 3 → ℝ) → E3} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀) :
    ∃ f : (Fin 3 → ℝ) × ℝ → E3,
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (A ∪ B) ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = q x := by
  classical
  let _ : DecidableEq E3 := Classical.decEq _
  have hD₀ : IsPLBall 2 D₀ := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKA⟩ := hA.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLB⟩ := hB.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 3 K.space := hKA.symm ▸ hA
  have hL : IsPLBall 3 L.space := hLB.symm ▸ hB
  have hKL : K.space ∩ L.space = D₀ ∪ D₁ := by rw [hKA, hLB, hinter]
  have hDK := disk_pair_subset_boundaryComplex K hK hL hD₀ hD₁ hKL
  have hDL := disk_pair_subset_boundaryComplex L hL hK hD₀ hD₁
    ((inter_comm L.space K.space).trans hKL)
  obtain ⟨f, hf, hbase⟩ := exists_cylindricalDiagram_of_ball_pair (isPLBall_stdSimplex 2) K L
    hK hL hD₁ hdis (subset_union_left.trans hDK) (subset_union_right.trans hDK)
    (subset_union_left.trans hDL) (subset_union_right.trans hDL) hKL hq
  refine ⟨f, ?_, hbase⟩
  rwa [hKA, hLB] at hf

private theorem cyclic_ball_seam_zero_one_is_essential {n : ℕ}
    (C : Fin (n + 3) → Set E3) (hC : ∀ i, IsPLBall 3 (C i))
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬ (SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅)
    {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (C 0 ∩ C 1)) :
    IsConnected (frontier (⋃ i, C i) \ q '' stdSimplexBoundary 2) ∧
      ¬ ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ frontier (⋃ i, C i) ∧
          q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 := by
  classical
  obtain ⟨M, hMfin, hMsp⟩ :=
    (IsPolyhedron.iUnion fun i => (hC i).isPolyhedron).exists_simplicialComplex
  have : Finite M.faces := hMfin.to_subtype
  have hM := isCombinatorialManifoldWithBoundary_of_cyclic_ball_union C hC hnext hdis htriple M hMsp
  let B := ⋃ i : Fin (n + 2), C i.succ
  have hB : IsPLBall 3 B := hM.isPLBall_iUnion_succ_of_cycle C hC
    (fun i => hMsp.symm ▸ subset_iUnion C i) hnext hdis
  have hcover : C 0 ∪ B = ⋃ i, C i := by
    ext x
    simp only [B, mem_union, mem_iUnion]
    constructor
    · rintro (hx | ⟨i, hi⟩)
      · exact ⟨0, hx⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Or.inl hi
      · exact Or.inr ⟨j, hi⟩
  have hmeet : C 0 ∩ B = (C 0 ∩ C 1) ∪ (C 0 ∩ C (Fin.last (n + 2))) := by
    ext x
    simp only [B, mem_inter_iff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hx0, i, hi⟩
      by_cases h1 : i.succ = 1
      · exact Or.inl ⟨hx0, h1 ▸ hi⟩
      by_cases hl : i.succ = Fin.last (n + 2)
      · exact Or.inr ⟨hx0, hl ▸ hi⟩
      have h2 : 2 ≤ i.succ.val := by
        have : i.succ.val ≠ 1 := fun h => h1 (Fin.ext (by simpa using h))
        have hpos : 0 < i.succ.val := by simp [Fin.val_succ]
        omega
      have hle : i.succ.val ≤ n + 1 := by
        have : i.succ.val ≠ n + 2 := fun h => hl (Fin.ext h)
        have := i.succ.isLt
        omega
      exact (Set.disjoint_left.mp (hdis 0 i.succ (Ne.symm (Fin.succ_ne_zero i))
        (not_cycleGraph_adj_zero h2 hle)) hx0 hi).elim
    · rintro (⟨hx0, hx1⟩ | ⟨hx0, hxl⟩)
      · exact ⟨hx0, 0, by simpa using hx1⟩
      · exact ⟨hx0, Fin.last (n + 1), by simpa using hxl⟩
  have hDdis : Disjoint (C 0 ∩ C 1) (C 0 ∩ C (Fin.last (n + 2))) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨hx0, hx1⟩ ⟨-, hxl⟩
    have ht := htriple 0 1 (Fin.last (n + 2)) (by simp) (by simp)
      (by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_one, Fin.val_last] at hh;
          omega)
    exact Set.notMem_empty x (ht ▸ ⟨⟨hx0, hx1⟩, hxl⟩)
  obtain ⟨f, hf, hf0⟩ := exists_cylindricalDiagram_with_base_of_ball_pair (hC 0) hB
    (hnext 0 _ cycleGraph_adj_zero_last) hDdis hmeet hq
  have hfM : IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M.space := by
    rw [hMsp, ← hcover]
    exact hf
  have hbase : f '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) = q '' stdSimplexBoundary 2 := by
    rw [prod_singleton, image_image]
    exact Set.EqOn.image_eq fun x hx => hf0 x hx.1
  have hess := hfM.boundary_slice_is_essential M hM
  rwa [hMsp, hbase] at hess

theorem cyclic_ball_seam_is_essential {n : ℕ}
    (C : Fin (n + 3) → Set E3) (hC : ∀ i, IsPLBall 3 (C i))
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬ (SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅)
    {i j : Fin (n + 3)} (hij : (SimpleGraph.cycleGraph (n + 3)).Adj i j)
    {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (C i ∩ C j)) :
    IsConnected (frontier (⋃ i, C i) \ q '' stdSimplexBoundary 2) ∧
      ¬ ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ frontier (⋃ i, C i) ∧
          q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 := by
  have key (a b : Fin (n + 3)) (hab : b - a = 1)
      (hqab : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (C a ∩ C b)) :
      IsConnected (frontier (⋃ i, C i) \ q '' stdSimplexBoundary 2) ∧
        ¬ ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
          IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ frontier (⋃ i, C i) ∧
            q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 := by
    let e := Equiv.addRight a
    let C' := C ∘ e
    have he : ∀ x y, (SimpleGraph.cycleGraph (n + 3)).Adj (e x) (e y) ↔
        (SimpleGraph.cycleGraph (n + 3)).Adj x y := by
      intro x y
      rw [SimpleGraph.cycleGraph_adj, SimpleGraph.cycleGraph_adj]
      change ((x + a) - (y + a) = 1 ∨ (y + a) - (x + a) = 1) ↔ _
      simp only [add_sub_add_right_eq_sub]
    have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (C' 0 ∩ C' 1) := by
      have hb : b = 1 + a := sub_eq_iff_eq_add.mp hab
      change IsPLHomeomorphOn q _ (C (0 + a) ∩ C (1 + a))
      rwa [zero_add, ← hb]
    have hess := cyclic_ball_seam_zero_one_is_essential C' (fun i => hC (e i))
      (fun i j h => hnext (e i) (e j) ((he i j).mpr h))
      (fun i j hne hno => hdis (e i) (e j) (e.injective.ne hne)
        (fun h => hno ((he i j).mp h)))
      (fun i j k hij hik hjk => htriple (e i) (e j) (e k)
        (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk)) hq'
    have hU : (⋃ i, C' i) = ⋃ i, C i := e.surjective.iUnion_comp C
    rwa [hU] at hess
  rcases SimpleGraph.cycleGraph_adj.mp hij with h | h
  · exact key j i h (by rw [inter_comm]; exact hq)
  · exact key i j h hq

end DifferentialGeometry.Topology.PiecewiseLinear
