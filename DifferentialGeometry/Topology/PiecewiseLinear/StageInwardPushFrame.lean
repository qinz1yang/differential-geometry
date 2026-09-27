/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteBoundaryExhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteLocalModel

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section LocalModel

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq_frontier_of_isCompact
    {K : Set X} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K)
    {A C : Set X} (hA : IsCompact A) (hC : IsCompact C) (hAK : A ⊆ K \ interior K)
    (hCK : C ⊆ interior K) :
    ∃ O : Set X, IsOpen O ∧ A ⊆ O ∧ C ⊆ O ∧ ∃ P : Set X,
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ K ∧ O ∩ K = O ∩ P ∧
        A ⊆ frontier P ∧ C ⊆ interior P ∧ frontier P ∩ O ⊆ K \ interior K := by
  obtain ⟨O, hO, hACO, P, hP, hPK, hOP⟩ :=
    hK.exists_isOpen_inter_eq_of_isCompact (hA.union hC)
      (union_subset (hAK.trans Set.sdiff_subset) (hCK.trans interior_subset))
  have hAO : A ⊆ O := subset_union_left.trans hACO
  have hCO : C ⊆ O := subset_union_right.trans hACO
  have hint : O ∩ interior K = O ∩ interior P :=
    inter_interior_eq_inter_interior_of_inter_eq hO hOP
  have hPcl : IsClosed P := hP.isCompact.isClosed
  refine ⟨O, hO, hAO, hCO, P, hP, hPK, hOP, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hxP : x ∈ P := (hOP.subset ⟨hAO hx, (hAK hx).1⟩).2
    rw [hPcl.frontier_eq]
    exact ⟨hxP, fun hxi => (hAK hx).2 (hint.symm.subset ⟨hAO hx, hxi⟩).2⟩
  · exact (hint.subset ⟨hCO hx, hCK hx⟩).2
  · rw [hPcl.frontier_eq] at hx
    refine ⟨(hOP.symm.subset ⟨hx.2, hx.1.1⟩).2, fun hxi => hx.1.2 ?_⟩
    exact (hint.subset ⟨hx.2, hxi⟩).2

omit [T2Space X] in
theorem isPLOn_of_isPLOn_local_of_eqOn_id {K P O S : Set X} {f : X → X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) (hO : IsOpen O)
    (hOP : O ∩ K = O ∩ P) (hS : IsClosed S) (hSO : S ⊆ O)
    (hf : IsPLOn (m + 1) (m + 1) f P) (hid : EqOn f id (K \ S)) :
    IsPLOn (m + 1) (m + 1) f K := by
  refine isPLOn_of_forall_exists_isOpen_inter_eq fun x hx => ?_
  by_cases hxO : x ∈ O
  · exact ⟨O, hO, hxO, P, hOP, hf x (hOP.subset ⟨hxO, hx⟩).2⟩
  · refine ⟨univ, isOpen_univ, mem_univ x, K, rfl, ?_⟩
    have hxS : x ∉ S := fun hmem => hxO (hSO hmem)
    refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
      (hK.isPLOn_id x hx) ?_ hx
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hS.isOpen_compl.mem_nhds hxS)] with z hz hzS
    exact hid ⟨hz, hzS⟩

end LocalModel

section Transport

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPiece.isPLOn_transport {Y : Set X} (T : PLPiece n X Y)
    {F : EuclideanSpace ℝ (Fin T.ambientDim) → EuclideanSpace ℝ (Fin T.ambientDim)}
    (hF : IsPiecewiseAffineOn F T.piece.complex.space)
    (hFmap : MapsTo F T.piece.complex.space T.piece.complex.space) :
    IsPLOn n n
      (fun x => T.piece.map (F (Function.invFunOn T.piece.map T.piece.complex.space x))) Y := by
  refine T.piece.isPLOn_of_eqOn_comp_invFunOn (w := fun y => T.piece.map (F y)) ?_ fun _ _ => rfl
  exact T.piece.isPLOn_comp hF hFmap

end Transport

section Height

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPolyhedron_nonneg_piecewiseAffineOn_pos {B A U : Set E} (hB : IsPolyhedron B)
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ Z : Set E, IsPolyhedron Z ∧ B \ U ⊆ interior Z ∧
      ∃ g : E → ℝ, IsPiecewiseAffineOn g univ ∧ (∀ y : E, 0 ≤ g y) ∧
        (∀ y ∈ A, 0 < g y) ∧ ∀ y ∈ Z, g y = 0 := by
  obtain ⟨Z, hZ, hsub, hZA⟩ :=
    exists_isPolyhedron_neighborhood (hB.isCompact.diff hU) hA.isClosed.isOpen_compl
      fun y hy hyA => hy.2 (hAU hyA)
  obtain ⟨g, hgpl, hg0, hgzero⟩ := hZ.exists_nonneg_piecewiseAffine_zero_set
  refine ⟨Z, hZ, hsub, g, hgpl, hg0, fun y hy => ?_, fun y hy => (hgzero y).mpr hy⟩
  exact lt_of_le_of_ne (hg0 y) fun hzero => hZA ((hgzero y).mp hzero.symm) hy

end Height

end DifferentialGeometry.Topology.PiecewiseLinear
