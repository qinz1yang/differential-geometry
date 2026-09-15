import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLBall_pair_inter_eq_of_frontier_inter
    {C D : Set (EuclideanSpace ℝ (Fin 2))} (hC : IsPLBall 2 C) (hD : IsPLBall 2 D)
    (hCD : C ⊆ D) (htrace : (frontier C ∩ frontier D).Nontrivial)
    (hbad : ¬frontier C ⊆ frontier D) (hnotfree : ¬IsPLBall 1 (frontier D ∩ C)) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 U ∧ IsPLBall 2 V ∧ U ∪ V = D ∧ U ∩ V = C ∧
      U ≠ D ∧ V ≠ D ∧ C ≠ U ∧ C ≠ V ∧
      frontier U ⊆ frontier D ∪ C ∧ frontier V ⊆ frontier D ∪ C ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 E → E ⊆ D →
        Disjoint (interior E) C → E ⊆ U ∨ E ⊆ V := by
  obtain ⟨A, p, q, hA, hAC, hcut⟩ :=
    exists_isCrosscut_subset_frontier_of_isPLBall_two hC hD hCD htrace hbad
  have hAC' : A ⊆ C := hAC.trans hC.isPolyhedron.isClosed.frontier_subset
  obtain ⟨U, V, hU, hV, hunion, hinter, hfU, hfV, hAU, hAV, htrU, htrV, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut hD hA hcut
  have hCA : Disjoint (interior C) A := by
    rw [disjoint_left]
    exact fun x hx hxA => (hAC hxA).2 hx
  obtain ⟨U, V, hU, hV, hunion, hinter, hfU, hfV, hAV, htrU, hCU, hside⟩ :
      ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
        IsPLBall 2 U ∧ IsPLBall 2 V ∧ U ∪ V = D ∧ U ∩ V = A ∧
        frontier U ⊆ frontier D ∪ A ∧ frontier V ⊆ frontier D ∪ A ∧
        A ⊆ frontier V ∧ IsPLBall 1 (U ∩ frontier D) ∧ C ⊆ U ∧
        ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 E → E ⊆ D →
          Disjoint (interior E) A → E ⊆ U ∨ E ⊆ V := by
    rcases hside C hC hCD hCA with hCU | hCV
    · exact ⟨U, V, hU, hV, hunion, hinter, hfU, hfV, hAV, htrU, hCU, hside⟩
    · refine ⟨V, U, hV, hU, (union_comm V U).trans hunion,
        (inter_comm V U).trans hinter, hfV, hfU, hAU, htrV, hCV, ?_⟩
      exact fun E hE hED hEA => (hside E hE hED hEA).symm
  have hUD : U ⊆ D := hunion ▸ subset_union_left
  have hVD : V ⊆ D := hunion ▸ subset_union_right
  have hCV : C ∩ V = A := by
    refine Subset.antisymm ((inter_subset_inter_left V hCU).trans hinter.subset) ?_
    exact fun x hx => ⟨hAC' hx, (hinter.symm.subset hx).2⟩
  have hball : IsPLBall 2 (C ∪ V) :=
    (isPLBall_union_and_finite_frontier_inter hC hV (hCV.symm ▸ hA)
      (hCV.symm ▸ hAC) (hCV.symm ▸ hAV)).1
  have hVnotU : ¬V ⊆ U := by
    intro hVU
    obtain ⟨x, hx⟩ := hV.interior_nonempty
    have hxA : x ∈ A := hinter ▸ ⟨hVU (interior_subset hx), interior_subset hx⟩
    exact (hAV hxA).2 hx
  have hCneU : C ≠ U := by
    intro heq
    apply hnotfree
    simpa only [← heq, inter_comm] using htrU
  have hmeet : U ∩ (C ∪ V) = C := by
    rw [inter_union_distrib_left, inter_eq_right.mpr hCU, hinter, union_eq_left.mpr hAC']
  refine ⟨U, C ∪ V, hU, hball, ?_, hmeet, ?_, ?_, hCneU, ?_, ?_, ?_, ?_⟩
  · rw [← union_assoc, union_eq_left.mpr hCU, hunion]
  · exact fun heq => hVnotU (heq.symm ▸ hVD)
  · intro heq
    apply hCneU
    apply Subset.antisymm hCU
    intro x hx
    exact hmeet.subset ⟨hx, heq.symm ▸ hUD hx⟩
  · intro heq
    exact hVnotU (subset_union_right.trans (heq.symm.subset.trans hCU))
  · exact hfU.trans (union_subset_union_right _ hAC')
  · apply (frontier_union_subset C V).trans
    refine union_subset (inter_subset_left.trans
      (hC.isPolyhedron.isClosed.frontier_subset.trans subset_union_right)) ?_
    exact inter_subset_right.trans (hfV.trans (union_subset_union_right _ hAC'))
  · intro E hE hED hEC
    exact (hside E hE hED (hEC.mono_right hAC')).imp_right fun hEV => hEV.trans subset_union_right

end DifferentialGeometry.Topology.PiecewiseLinear
