/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex
import DifferentialGeometry.Topology.PiecewiseLinear.EulerCellOperations

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.SimplicialComplex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem eulerChar_coneComplex {p : E} {L : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) [Finite L.faces] [Finite (coneComplex h).faces] :
    eulerChar (coneComplex h) = 1 := by
  classical
  have hmemFL : ∀ s : Finset E, s ∈ (Set.toFinite L.faces).toFinset ↔ s ∈ L.faces := by
    intro s
    rw [Set.Finite.mem_toFinset]
  have hpnot : ∀ s ∈ L.faces, p ∉ s := fun _ hs => h.notMem_face hs
  have hcone : (Set.toFinite (coneComplex h).faces).toFinset =
      ((Set.toFinite L.faces).toFinset ∪ {({p} : Finset E)}) ∪
        (Set.toFinite L.faces).toFinset.image (insert p) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, hmemFL,
      Set.Finite.mem_toFinset]
    rw [mem_coneComplex_faces_iff]
    constructor
    · rintro (ht | rfl | ⟨σ, hσ, rfl⟩)
      · exact Or.inl (Or.inl ht)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨σ, hσ, rfl⟩
    · rintro ((ht | rfl) | ⟨σ, hσ, rfl⟩)
      · exact Or.inl ht
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨σ, hσ, rfl⟩)
  have hdisj1 : Disjoint (Set.toFinite L.faces).toFinset ({({p} : Finset E)} :
      Finset (Finset E)) := by
    rw [Finset.disjoint_singleton_right]
    intro hp
    exact hpnot _ ((hmemFL _).mp hp) (Finset.mem_singleton_self p)
  have hdisj2 : Disjoint ((Set.toFinite L.faces).toFinset ∪ {({p} : Finset E)})
      ((Set.toFinite L.faces).toFinset.image (insert p)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨σ, hσ, hσt⟩ := Finset.mem_image.mp ht'
    rcases Finset.mem_union.mp ht with htL | htp
    · exact hpnot _ ((hmemFL _).mp htL) (hσt ▸ Finset.mem_insert_self p σ)
    · rw [Finset.mem_singleton] at htp
      obtain ⟨x, hx⟩ := L.nonempty_of_mem_faces ((hmemFL _).mp hσ)
      have hxmem : x ∈ ({p} : Finset E) := by
        rw [← htp, ← hσt]
        exact Finset.mem_insert_of_mem hx
      exact hpnot _ ((hmemFL _).mp hσ) (Finset.mem_singleton.mp hxmem ▸ hx)
  have hinj : ∀ x ∈ (Set.toFinite L.faces).toFinset, ∀ y ∈ (Set.toFinite L.faces).toFinset,
      insert p x = insert p y → x = y := by
    intro x hx y hy hxy
    have hex : (insert p x).erase p = x := Finset.erase_insert (hpnot _ ((hmemFL _).mp hx))
    have hey : (insert p y).erase p = y := Finset.erase_insert (hpnot _ ((hmemFL _).mp hy))
    rw [← hex, ← hey, hxy]
  have hcard : ∀ s ∈ (Set.toFinite L.faces).toFinset, (insert p s).card = s.card + 1 :=
    fun s hs => Finset.card_insert_of_notMem (hpnot s ((hmemFL s).mp hs))
  have hthird : (∑ s ∈ (Set.toFinite L.faces).toFinset, -(-1 : ℤ) ^ (insert p s).card) +
      ∑ s ∈ (Set.toFinite L.faces).toFinset, -(-1 : ℤ) ^ s.card = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro s hs
    rw [hcard s hs]
    ring
  rw [eulerChar, faceEulerChar]
  change (∑ t ∈ (Set.toFinite (coneComplex h).faces).toFinset, -(-1 : ℤ) ^ t.card) = 1
  rw [hcone, Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_image hinj,
    Finset.sum_singleton, Finset.card_singleton]
  linarith

open Classical in
theorem eulerChar_eq_add_one_of_faces_union_coneComplex [FiniteDimensional ℝ E]
    (M A : Geometry.SimplicialComplex ℝ E) {p : E} {L : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) [Finite M.faces] [Finite A.faces] [Finite L.faces]
    [Finite (coneComplex h).faces]
    (hfaces : M.faces = A.faces ∪ (coneComplex h).faces)
    (hinter : IsPLSphere 1 (intersectionComplex A (coneComplex h)).space) :
    eulerChar M = eulerChar A + 1 := by
  rw [eulerChar_eq_add_of_faces_union_of_isPLSphere_one M A (coneComplex h) hfaces hinter,
    eulerChar_coneComplex h]

end DifferentialGeometry.Topology.PiecewiseLinear
