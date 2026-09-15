import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalArc
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PlanarJordan.ArcGap
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.interior_eq_inside_frontier {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) : interior C = Schoenflies.inside (frontier C) :=
  PlanarJordan.interior_eq_inside_frontier_of_isCompact hC.isPolyhedron.isCompact
    (isJordanCurve_of_isPLSphere_one hC.isPLSphere_frontier) hC.interior_nonempty

theorem IsPLBall.isConnected_interior {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) : IsConnected (interior C) := by
  rw [hC.interior_eq_inside_frontier]
  exact (Schoenflies.jordan_curve_theorem
    (isJordanCurve_of_isPLSphere_one hC.isPLSphere_frontier)).isConnected_inside

theorem exists_isCrosscut_subset_frontier_of_isPLBall_two
    {C D : Set (EuclideanSpace ℝ (Fin 2))} (hC : IsPLBall 2 C) (hD : IsPLBall 2 D)
    (hCD : C ⊆ D) (htrace : (frontier C ∩ frontier D).Nontrivial)
    (hne : ¬frontier C ⊆ frontier D) :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))) (p q : EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ A ⊆ frontier C ∧ Schoenflies.IsCrosscut (frontier D) A p q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := htrace
  obtain ⟨A, B, hcut, _, _⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    hC.isPLSphere_frontier hp.1 hq.1 hpq
  have hbad : ¬A ⊆ frontier D ∨ ¬B ⊆ frontier D := by
    by_contra h
    push Not at h
    exact hne (hcut.union_eq.symm.subset.trans (union_subset h.1 h.2))
  have hgap (P : Set (EuclideanSpace ℝ (Fin 2)))
      (harc : Schoenflies.IsArcBetween P p q) (hPC : P ⊆ frontier C)
      (hPF : ¬P ⊆ frontier D) :
      ∃ (A : Set (EuclideanSpace ℝ (Fin 2))) (p q : EuclideanSpace ℝ (Fin 2)),
        IsPLBall 1 A ∧ A ⊆ frontier C ∧ Schoenflies.IsCrosscut (frontier D) A p q := by
    obtain ⟨Q, a, b, hQ, hQP, ha, hb, hQoff⟩ :=
      PlanarJordan.exists_isArcBetween_sdiff_pair_subset_compl harc isClosed_frontier hp.2 hq.2 hPF
    have hQC : Q ⊆ frontier C := hQP.trans hPC
    have hPL := isPLBall_of_isArc_subset_isPLSphere hC.isPLSphere_frontier hQ.isArc hQC
    refine ⟨Q, a, b, hPL, hQC,
      isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier, hQ,
      hPL.isPolyhedron.isPolygonal_of_isArcBetween hQ, ha, hb, ?_⟩
    rw [← hD.interior_eq_inside_frontier]
    intro x hx
    have hxD : x ∈ D := hCD (hC.isPolyhedron.isClosed.closure_eq ▸ frontier_subset_closure (hQC hx.1))
    exact (mem_interior_iff_notMem_frontier hxD).mpr (hQoff hx)
  exact hbad.elim (hgap A hcut.fst hcut.fst_subset) (hgap B hcut.snd hcut.snd_subset)

theorem exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut
    {D A : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D) (hA : IsPLBall 1 A)
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCrosscut (frontier D) A p q) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 U ∧ IsPLBall 2 V ∧ U ∪ V = D ∧ U ∩ V = A ∧
      frontier U ⊆ frontier D ∪ A ∧ frontier V ⊆ frontier D ∪ A ∧
      A ⊆ frontier U ∧ A ⊆ frontier V ∧
      IsPLBall 1 (U ∩ frontier D) ∧ IsPLBall 1 (V ∩ frontier D) ∧
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 C → C ⊆ D →
        Disjoint (interior C) A → C ⊆ U ∨ C ⊆ V := by
  have hpq : p ≠ q := by
    obtain ⟨f, _, hi, _, hf0, hf1⟩ := h.arc
    intro hpq
    exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (hf0.trans (hpq.trans hf1.symm)))
  obtain ⟨B, C, hcut, hB, hC⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    hD.isPLSphere_frontier h.left_mem h.right_mem hpq
  have hBU := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hA h hcut
  have hCV := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hA h hcut.symm
  let U := closure (Schoenflies.inside (B ∪ A))
  let V := closure (Schoenflies.inside (C ∪ A))
  have hU : IsPLBall 2 U := isPLBall_closure_inside_of_isPLSphere_one hBU
  have hV : IsPLBall 2 V := isPLBall_closure_inside_of_isPLSphere_one hCV
  have hUF : frontier U = B ∪ A := frontier_closure_inside_of_isPLSphere_one hBU
  have hVF : frontier V = C ∪ A := frontier_closure_inside_of_isPLSphere_one hCV
  refine ⟨U, V, hU, hV, ?_, PlanarJordan.closure_inside_inter_of_isCrosscut h hcut,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show U ∪ V = closure (Schoenflies.inside (frontier D)) from
      PlanarJordan.closure_inside_union_of_isCrosscut h hcut, ← hD.interior_eq_inside_frontier]
    exact hD.closure_interior
  · rw [hUF]
    exact union_subset_union_left A hcut.fst_subset
  · rw [hVF]
    exact union_subset_union_left A hcut.snd_subset
  · rw [hUF]
    exact subset_union_right
  · rw [hVF]
    exact subset_union_right
  · change IsPLBall 1 (closure (Schoenflies.inside (B ∪ A)) ∩ frontier D)
    rw [h.closure_side_inter (fun _ => Schoenflies.jordan_curve_theorem) hcut]
    exact hB
  · change IsPLBall 1 (closure (Schoenflies.inside (C ∪ A)) ∩ frontier D)
    rw [h.closure_side_inter (fun _ => Schoenflies.jordan_curve_theorem) hcut.symm]
    exact hC
  · intro E hE hED hEA
    have hjordan : ∀ S : Set Schoenflies.Plane, Schoenflies.IsJordanCurve S →
        Schoenflies.IsSeparating S := fun _ => Schoenflies.jordan_curve_theorem
    have hcover : interior E ⊆ Schoenflies.inside (B ∪ A) ∪ Schoenflies.inside (C ∪ A) := by
      rw [← h.inside_diff_eq hjordan hcut h.hasArcCollars, ← hD.interior_eq_inside_frontier]
      exact fun x hx => ⟨interior_mono hED hx, disjoint_left.mp hEA hx⟩
    have hsplit := IsPreconnected.subset_or_subset
      (hjordan _ (isJordanCurve_of_isPLSphere_one hBU)).isOpen_inside
      (hjordan _ (isJordanCurve_of_isPLSphere_one hCV)).isOpen_inside
      (h.disjoint_sides hjordan hcut) hcover hE.isConnected_interior.isPreconnected
    have hclose (P : Set (EuclideanSpace ℝ (Fin 2))) (hEP : interior E ⊆ P) :
        E ⊆ closure P := hE.closure_interior.symm.subset.trans (closure_mono hEP)
    exact hsplit.imp (hclose _) (hclose _)

theorem exists_isPLBall_pair_of_isCrosscut
    {D A : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D) (hA : IsPLBall 1 A)
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCrosscut (frontier D) A p q) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 U ∧ IsPLBall 2 V ∧ U ∪ V = D ∧ U ∩ V = A ∧
      frontier U ⊆ frontier D ∪ A ∧ frontier V ⊆ frontier D ∪ A ∧
      A ⊆ frontier U ∧ A ⊆ frontier V ∧
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 C → C ⊆ D →
        Disjoint (interior C) A → C ⊆ U ∨ C ⊆ V := by
  obtain ⟨U, V, hU, hV, hu, hi, hfU, hfV, hAU, hAV, _, _, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut hD hA h
  exact ⟨U, V, hU, hV, hu, hi, hfU, hfV, hAU, hAV, hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
