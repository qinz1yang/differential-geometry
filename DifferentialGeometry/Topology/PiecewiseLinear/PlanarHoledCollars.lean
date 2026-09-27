/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarOuterCollar
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplementFamily
import Mathlib.Order.Filter.Finite

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_boundary_collars_holed_disk
    {ι : Type*} [Finite ι] {D : Set Plane} {H : ι → Set Plane}
    (hD : IsPLBall 2 D) (hH : ∀ i, IsPLBall 2 (H i))
    (hHD : ∀ i, H i ⊆ interior D)
    (hdis : Pairwise fun i j => Disjoint (H i) (H j)) :
    let J : Option ι → Set Plane := fun i => Option.elim i (frontier D) (fun j => frontier (H j))
    ∃ (A : Option ι → Set Plane) (B : Set Plane) (ρ : Option ι → Plane × ℝ → Plane),
      IsPolyhedron B ∧ (D \ ⋃ i, interior (H i)) = B ∪ ⋃ i, A i ∧
      (∀ i, IsPLHomeomorphOn (ρ i) (J i ×ˢ Icc (0 : ℝ) 1) (A i)) ∧
      (∀ i x, x ∈ J i → ρ i (x, 1) = x) ∧
      (Pairwise fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, A i ∩ B ⊆ ρ i '' (J i ×ˢ ({0} : Set ℝ)) := by
  classical
  let J : Option ι → Set Plane := fun i => Option.elim i (frontier D) (fun j => frontier (H j))
  let P := D \ ⋃ i, interior (H i)
  let C : Option ι → Set Plane := fun i => Option.elim i (interior D)ᶜ H
  have hC : ∀ i, IsClosed (C i) := by
    rintro (_ | i)
    · exact isOpen_interior.isClosed_compl
    · exact (hH i).isPolyhedron.isClosed
  have hCd : Pairwise fun i j => Disjoint (C i) (C j) := by
    rintro (_ | i) (_ | j) hne
    · exact (hne rfl).elim
    · exact disjoint_left.mpr fun x hx hy => hx (hHD j hy)
    · exact disjoint_left.mpr fun x hx hy => hy (hHD i hx)
    · exact hdis (fun hij => hne (congrArg some hij))
  have hfilters : Pairwise fun i j => Disjoint (𝓝ˢ (C i)) (𝓝ˢ (C j)) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hC i) (hC j) (hCd hij)
  obtain ⟨V, hV, hVdis⟩ := hfilters.exists_mem_filter_of_disjoint
  let U := fun i => interior (V i)
  have hU (i : Option ι) : IsOpen (U i) := isOpen_interior
  have hCU (i : Option ι) : C i ⊆ U i := subset_interior_iff_mem_nhdsSet.mpr (hV i)
  have hUdis : Pairwise fun i j => Disjoint (U i) (U j) :=
    fun i j hij => (hVdis hij).mono interior_subset interior_subset
  have hJC (i : Option ι) : J i ⊆ C i := by
    cases i with
    | none => exact fun _ hx => hx.2
    | some i => exact (hH i).isPolyhedron.isClosed.frontier_subset
  let Q : Option ι → Set Plane := fun i => Option.elim i D (fun j => D \ interior (H j))
  have hlocal (i : Option ι) : ∃ (A R : Set Plane) (ρ : Plane × ℝ → Plane),
      IsPolyhedron A ∧ IsPolyhedron R ∧ A ⊆ U i ∧ Q i = R ∪ A ∧
      IsPLHomeomorphOn ρ (J i ×ˢ Icc (0 : ℝ) 1) A ∧
      (∀ x ∈ J i, ρ (x, 1) = x) ∧
      A ∩ R = ρ '' (J i ×ˢ ({0} : Set ℝ)) := by
    cases i with
    | none =>
      obtain ⟨r, hr⟩ := id hD
      have hUn : U none ∈ 𝓝ˢ[D] (r '' stdSimplexBoundary 2) := by
        rw [hr.image_stdSimplexBoundary]
        exact mem_nhdsSetWithin.mpr
          ⟨U none, hU none, (hJC none).trans (hCU none), inter_subset_left⟩
      obtain ⟨A, R, ρ, hA, hR, hAU, hcover, hρ, hfix, hmeet, -, -⟩ :=
        hr.exists_disk_boundary_collar hUn
      rw [hr.image_stdSimplexBoundary] at hρ hfix hmeet
      exact ⟨A, R, ρ, hA, hR.isPolyhedron, hAU, hcover, hρ, hfix, hmeet⟩
    | some i =>
      obtain ⟨A, R, ρ, hA, hR, hAU, hcover, hρ, hfix, hmeet, -⟩ :=
        hD.exists_outer_boundary_collar (hH i) (hHD i) (hU (some i))
          ((hJC (some i)).trans (hCU (some i)))
      exact ⟨A, R, ρ, hA, hR, hAU.trans inter_subset_left, hcover, hρ, hfix, hmeet⟩
  choose A R ρ hA hR hAU hcover hρ hfix hmeet using hlocal
  have hPQ (i : Option ι) : P ⊆ Q i := by
    cases i with
    | none => exact sdiff_subset
    | some i => exact fun x hx => ⟨hx.1, fun hi => hx.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩
  have hAP (i : Option ι) : A i ⊆ P := by
    intro x hx
    have hxQ : x ∈ Q i := (hcover i).symm ▸ Or.inr hx
    refine ⟨?_, ?_⟩
    · cases i with
      | none => exact hxQ
      | some i => exact hxQ.1
    · intro hxhole
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxhole
      by_cases hij : i = some j
      · subst i
        exact hxQ.2 hj
      · exact disjoint_left.mp (hUdis hij) (hAU i hx)
          (hCU (some j) (interior_subset hj))
  have hAdis : Pairwise fun i j => Disjoint (A i) (A j) :=
    fun i j hij => (hUdis hij).mono (hAU i) (hAU j)
  have hP : IsPolyhedron P := hD.isPolyhedron.sdiff_iUnion_interior_of_isPLBall hH
  let B := closure (P \ ⋃ i, A i)
  have hB : IsPolyhedron B := hP.closure_sdiff (IsPolyhedron.iUnion hA)
  have hBP : B ⊆ P := closure_minimal sdiff_subset hP.isClosed
  have hBR (i : Option ι) : B ⊆ R i := by
    apply closure_minimal _ (hR i).isClosed
    rintro x ⟨hxP, hxA⟩
    exact ((hcover i) ▸ hPQ i hxP).resolve_right fun hi => hxA (mem_iUnion.mpr ⟨i, hi⟩)
  have hPcover : P = B ∪ ⋃ i, A i := by
    apply Subset.antisymm ?_ (union_subset hBP (iUnion_subset hAP))
    intro x hx
    by_cases hxA : x ∈ ⋃ i, A i
    · exact Or.inr hxA
    · exact Or.inl (subset_closure ⟨hx, hxA⟩)
  refine ⟨A, B, ρ, hB, hPcover, hρ, hfix, hAdis, ?_⟩
  intro i x hx
  exact (hmeet i).subset ⟨hx.1, hBR i hx.2⟩

theorem exists_isPLHomeomorphOn_holed_disk_of_positive_boundary_maps
    {ι : Type*} [Finite ι] {D : Set Plane} {H : ι → Set Plane}
    (hD : IsPLBall 2 D) (hH : ∀ i, IsPLBall 2 (H i))
    (hHD : ∀ i, H i ⊆ interior D)
    (hdis : Pairwise fun i j => Disjoint (H i) (H j))
    {u : Option ι → Plane → Plane}
    (hu : ∀ i, IsPLHomeomorphOn (u i)
      (Option.elim i (frontier D) (fun j => frontier (H j)))
      (Option.elim i (frontier D) (fun j => frontier (H j))))
    (hpos : ∀ i, IsPLCirclePositive
      (Option.elim i (frontier D) (fun j => frontier (H j))) (u i)) :
    ∃ g : Plane → Plane,
      IsPLHomeomorphOn g (D \ ⋃ i, interior (H i)) (D \ ⋃ i, interior (H i)) ∧
      ∀ i, EqOn g (u i) (Option.elim i (frontier D) (fun j => frontier (H j))) := by
  let J : Option ι → Set Plane := fun i => Option.elim i (frontier D) (fun j => frontier (H j))
  have hJ : ∀ i, IsPLSphere 1 (J i) := by
    rintro (_ | i)
    · exact hD.isPLSphere_frontier
    · exact (hH i).isPLSphere_frontier
  obtain ⟨A, B, ρ, hB, hcover, hρ, hfix, hAdis, hmeet⟩ :=
    exists_boundary_collars_holed_disk hD hH hHD hdis
  obtain ⟨g, hg, -, -, hgu, -⟩ :=
    exists_isPLHomeomorphOn_of_circle_collars hJ hB hρ hAdis hmeet hu hpos
  refine ⟨g, hcover.symm ▸ hg, ?_⟩
  intro i x hx
  have h := hgu i x hx
  rw [hfix i x hx, hfix i (u i x) ((hu i).bijOn.mapsTo hx)] at h
  exact h

end DifferentialGeometry.Topology.PiecewiseLinear
