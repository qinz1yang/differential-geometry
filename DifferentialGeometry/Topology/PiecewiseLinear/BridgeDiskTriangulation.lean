/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeArcShrinking

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem singleton_mem_faces_of_restrict_space_singleton
    (K : Geometry.SimplicialComplex ℝ E) {x : E}
    (hx : (restrict K {x}).space = {x}) : {x} ∈ K.faces := by
  obtain ⟨s, hs, _⟩ := (restrict K {x}).mem_space_iff.mp (hx.symm ▸ mem_singleton x)
  obtain ⟨v, hv⟩ := (restrict K {x}).nonempty_of_mem_faces hs
  have hvx : v = x := hs.2 (subset_convexHull ℝ (s : Set E) hv)
  subst v
  exact K.down_closed hs.1 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty x)

open Classical in
theorem IsBridgeDisk.exists_compatible_triangulation
    {C A B : Set E} {a b x : E} (h : IsBridgeDisk C A B a b)
    (hC : IsPolyhedron C) (hx : x ∈ B ∩ frontier C) :
    ∃ T : Geometry.SimplicialComplex ℝ E, T.faces.Finite ∧ C ⊆ interior T.space ∧
      (restrict T C).space = C ∧ (restrict T B).space = B ∧
      (restrict T A).space = A ∧ (restrict T (B ∩ frontier C)).space = B ∩ frontier C ∧
      {a} ∈ T.faces ∧ {b} ∈ T.faces ∧ {x} ∈ T.faces := by
  have hcopy := h
  obtain ⟨q, hq, hBC, hbase, _, _, _⟩ := hcopy
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨γ, hγ, _, _⟩ := h.exists_parametrization
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  have hAB : A ⊆ B := by
    rw [← hbase]
    exact (image_mono (fun _ hz => hz.1)).trans hq.image_eq.subset
  have ha : a ∈ C := h.subset (h.inter_frontier.symm.subset (Or.inl rfl)).1
  have hb : b ∈ C := h.subset (h.inter_frontier.symm.subset (Or.inr rfl)).1
  obtain ⟨N, hN, hCN, _⟩ := exists_isPolyhedron_neighborhood hC.isCompact isOpen_univ
    (subset_univ C)
  obtain ⟨K, hKfin, hKN⟩ := hN.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let Q : Fin 7 → Set E := ![C, B, A, B ∩ frontier C, {a}, {b}, {x}]
  have hQ : ∀ i, IsPolyhedron (Q i) := by
    intro i
    fin_cases i <;> dsimp [Q]
    · exact hC
    · exact hB.isPolyhedron
    · exact hA.isPolyhedron
    · exact h.isPLBall_inter_frontier.isPolyhedron
    · exact (isPLBall_zero_iff.mpr ⟨a, rfl⟩).isPolyhedron
    · exact (isPLBall_zero_iff.mpr ⟨b, rfl⟩).isPolyhedron
    · exact (isPLBall_zero_iff.mpr ⟨x, rfl⟩).isPolyhedron
  have hQC : ∀ i, Q i ⊆ C := by
    intro i
    fin_cases i <;> dsimp [Q]
    · exact Subset.rfl
    · exact hBC
    · exact hAB.trans hBC
    · exact inter_subset_left.trans hBC
    · exact singleton_subset_iff.mpr ha
    · exact singleton_subset_iff.mpr hb
    · exact singleton_subset_iff.mpr (hBC hx.1)
  obtain ⟨T, hTK, hTfin, hQT⟩ := exists_isSubdivision_subcomplexes K Q hQ
    (fun i => (hQC i).trans (hCN.trans (interior_subset.trans hKN.symm.subset)))
  have hres : ∀ i, (restrict T (Q i)).space = Q i :=
    fun i => restrict_space_of_eq_biUnion T (Q i) (hQT i)
  refine ⟨T, hTfin, ?_, hres 0, hres 1, hres 2, hres 3,
    singleton_mem_faces_of_restrict_space_singleton T (hres 4),
    singleton_mem_faces_of_restrict_space_singleton T (hres 5),
    singleton_mem_faces_of_restrict_space_singleton T (hres 6)⟩
  rw [hTK.space_eq, hKN]
  exact hCN

end DifferentialGeometry.Topology.PiecewiseLinear
