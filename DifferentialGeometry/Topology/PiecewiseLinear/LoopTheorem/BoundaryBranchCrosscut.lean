import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchPreimage
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
private theorem boundaryComplex_space_eq_pair_of_space_eq_Icc
    (R : Geometry.SimplicialComplex ℝ ℝ) [Finite R.faces]
    (hRspace : R.space = Icc 0 1) (hRball : IsPLBall 1 R.space) :
    (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space = {(0 : ℝ), 1} := by
  have hsub : (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space ⊆
      frontier R.space :=
    boundaryComplex_space_subset_frontier_of_finrank (n := 0) (by simp) R
      hRball.isCombinatorialManifoldWithBoundary
  rw [hRspace, frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)] at hsub
  have hsphere : IsPLSphere 0
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall R hRball
  obtain ⟨a, b, hab, hboundary⟩ := isPLSphere_zero_iff.mp hsphere
  rw [hboundary] at hsub
  have ha : a ∈ ({(0 : ℝ), 1} : Set ℝ) := hsub (Or.inl rfl)
  have hb : b ∈ ({(0 : ℝ), 1} : Set ℝ) := hsub (Or.inr rfl)
  rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
  · exact (hab rfl).elim
  · exact hboundary
  · rw [hboundary, pair_comm]
  · exact (hab rfl).elim

open Classical in
theorem IsPLHomeomorphOn.exists_parametrization_Icc_boundaryComplex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {A : Set E} (hA : IsPLBall 1 A)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces]
    {f : E → F} (hf : IsPLHomeomorphOn f A K.space) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) A ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1 K).space ↔
          t = 0 ∨ t = 1 := by
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hA
  obtain ⟨R, hRfinite, hRspace⟩ :=
    (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfinite.to_subtype
  have hRball : IsPLBall 1 R.space := by
    rw [hRspace]
    exact isPLBall_Icc (by norm_num)
  have hcomp : IsPLHomeomorphOn (f ∘ γ) R.space K.space := by
    rw [hRspace]
    exact hγ.trans hf
  have hsourceBoundary :
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 R).space = {(0 : ℝ), 1} :=
    boundaryComplex_space_eq_pair_of_space_eq_Icc R hRspace hRball
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have htR : t ∈ R.space := hRspace.symm ▸ ht
  have hiff := mem_boundaryComplex_space_iff_of_isPLHomeomorphOn R K
    hRball.isCombinatorialManifoldWithBoundary hcomp htR
  rw [hsourceBoundary] at hiff
  simpa only [Function.comp_apply, mem_insert_iff, mem_singleton_iff] using hiff

namespace NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

private theorem disjoint_isPLBall_of_isCrosscut_of_subset_interior
    {P A Q : Set (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)}
    (h : Schoenflies.IsCrosscut (frontier P) A p q)
    (hQ : IsPLBall 2 Q) (hQP : Q ⊆ interior P)
    (hdisjoint : Disjoint A (frontier Q)) : Disjoint A Q := by
  have hcover : A ⊆ interior Q ∪ Qᶜ := by
    intro x hxA
    by_cases hxQ : x ∈ Q
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxQ).mpr
        (Set.disjoint_left.mp hdisjoint hxA))
    · exact Or.inr hxQ
  have hsplit := IsPreconnected.subset_or_subset isOpen_interior
    hQ.isPolyhedron.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover
    h.arc.isArc.isConnected.isPreconnected
  rcases hsplit with hAin | hAout
  · exact (h.left_mem.2 (hQP (interior_subset (hAin h.arc.left_mem)))).elim
  · exact Set.disjoint_left.mpr fun x hxA hxQ => hAout hxA hxQ

open Classical in
theorem exists_isCrosscut_of_isPLBall_subset_branchPreimage
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsPLBall 1 A)
    (hAsub : A ⊆ hD.branchPreimage c)
    (hcoordinate : IsPLHomeomorphOn (hD.branchCoordinate c) A
      (hD.singularSet.branchComplex c).space) :
    ∃ p q : EuclideanSpace ℝ (Fin 2),
      Schoenflies.IsCrosscut (frontier D.domain) A p q := by
  let L := hD.singularSet.branchComplex c
  let _ : Finite L.faces :=
    (hD.singularSet.branchComplex_faces_finite c).to_subtype
  obtain ⟨γ, hγ, hγboundary⟩ :=
    IsPLHomeomorphOn.exists_parametrization_Icc_boundaryComplex hA L hcoordinate
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ t ∈ hD.branchPreimage c :=
    hAsub (hγ.bijOn.mapsTo ht)
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      D (γ t) ∈ BdM ↔ t = 0 ∨ t = 1 := by
    have htpre := hsource t ht
    have htcoord := hD.branchCoordinate_mem c htpre
    have hmap := hD.singularSet.branchComplex_boundary_iff_map_mem_boundary c htcoord
    have hDcoord : D (γ t) =
        hD.singularSet.piece.piece.map (hD.branchCoordinate c (γ t)) := by
      simpa only [NormalSingularSetTriangulation.branchPieceIn_map] using
        (hD.branchPieceIn_map_branchCoordinate c htpre).symm
    rw [hDcoord]
    exact hmap.symm.trans (hγboundary t ht)
  have hopen : γ '' Ioo (0 : ℝ) 1 ⊆ interior D.domain := by
    rintro x ⟨t, ht, rfl⟩
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htpre := hsource t htIcc
    apply (mem_interior_iff_notMem_frontier htpre.1).mpr
    intro htfrontier
    have hrange : D (γ t) ∈ Set.range D.boundary :=
      ⟨⟨γ t, htfrontier⟩, rfl⟩
    have hDboundary : D (γ t) ∈ BdM := by
      have hinter : D (γ t) ∈ D '' D.domain ∩ BdM := by
        rw [hD.image_inter_boundary]
        exact hrange
      exact hinter.2
    rcases (hboundary t htIcc).mp hDboundary with ht0 | ht1
    · exact ht.1.ne' ht0
    · exact ht.2.ne ht1
  have hendpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hend : t = 0 ∨ t = 1) : γ t ∈ frontier D.domain := by
    have htpre := hsource t ht
    have hdouble : D (γ t) ∈ doublePointSet D D.domain :=
      (hD.branchPreimage_subset_doublePointPreimage c htpre).2
    have hDboundary : D (γ t) ∈ BdM := (hboundary t ht).mpr hend
    obtain ⟨e, -, hySource, N, hcrossing⟩ :=
      hD.exists_boundary_crossing_chart ⟨hdouble, hDboundary⟩
    exact hD.fiber_subset_frontier_of_boundary_crossing hySource hcrossing
      ⟨htpre.1, rfl⟩
  refine ⟨γ 0, γ 1,
    hγ.isCrosscut_of_image_Ioo_subset_interior D.isPLBall_domain ?_ ?_ hopen⟩
  · exact hendpoint 0 (by norm_num) (Or.inl rfl)
  · exact hendpoint 1 (by norm_num) (Or.inr rfl)

open Classical in
theorem exists_two_isCrosscuts_branchPreimage_of_boundaryBranch_with_coordinate
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) A
          (hD.singularSet.branchComplex c).space ∧
        IsPLHomeomorphOn (hD.branchCoordinate c) C
          (hD.singularSet.branchComplex c).space ∧
        (∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
          IsPLHomeomorphOn g A C ∧ EqOn D (D ∘ g) A) ∧
        (∃ p q, Schoenflies.IsCrosscut (frontier D.domain) A p q) ∧
        ∃ r s, Schoenflies.IsCrosscut (frontier D.domain) C r s := by
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, hAcoordinate, hCcoordinate⟩ :=
    hD.exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate hc
  have hAsub : A ⊆ hD.branchPreimage c := by
    rw [hcover]
    exact subset_union_left
  have hCsub : C ⊆ hD.branchPreimage c := by
    rw [hcover]
    exact subset_union_right
  obtain ⟨p, q, hAcrosscut⟩ :=
    hD.exists_isCrosscut_of_isPLBall_subset_branchPreimage c hA hAsub hAcoordinate
  obtain ⟨r, s, hCcrosscut⟩ :=
    hD.exists_isCrosscut_of_isPLBall_subset_branchPreimage c hC hCsub hCcoordinate
  obtain ⟨g, hg, hcompat⟩ :=
    hD.exists_isPLHomeomorphOn_eqOn_of_branchCoordinate c hAsub hCsub
      hAcoordinate hCcoordinate
  exact ⟨A, C, hA, hC, hdisjoint, hcover, hAcoordinate, hCcoordinate,
    ⟨g, hg, hcompat⟩, ⟨p, q, hAcrosscut⟩, r, s, hCcrosscut⟩

open Classical in
theorem exists_two_isCrosscuts_branchPreimage_of_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ A C : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
        hD.branchPreimage c = A ∪ C ∧
        (∃ p q, Schoenflies.IsCrosscut (frontier D.domain) A p q) ∧
        ∃ r s, Schoenflies.IsCrosscut (frontier D.domain) C r s := by
  obtain ⟨A, C, hA, hC, hdisjoint, hcover, -, -, -, hAcrosscut, hCcrosscut⟩ :=
    hD.exists_two_isCrosscuts_branchPreimage_of_boundaryBranch_with_coordinate
      hc
  exact ⟨A, C, hA, hC, hdisjoint, hcover, hAcrosscut, hCcrosscut⟩

open Classical in
private theorem doublePointPreimage_inter_eq_of_closedBranch_inter_eq
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch}
    {J Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hc : ¬hD.singularSet.IsBoundaryBranch c)
    (hJsub : J ⊆ hD.branchPreimage c) (hQ : IsPLBall 2 Q)
    (hQsub : Q ⊆ interior D.domain) (hfrontier : frontier Q = J)
    (hclosedInter : (⋃ d : {d : hD.singularSet.Branch //
        ¬hD.singularSet.IsBoundaryBranch d}, hD.branchPreimage d.1) ∩ Q = J) :
    doublePointPreimage D D.domain ∩ Q = J := by
  apply Subset.antisymm
  · intro x hx
    have hxunion : x ∈ ⋃ d : hD.singularSet.Branch, hD.branchPreimage d := by
      rw [hD.iUnion_branchPreimage]
      exact hx.1
    obtain ⟨d, hxd⟩ := mem_iUnion.mp hxunion
    by_cases hd : hD.singularSet.IsBoundaryBranch d
    · obtain ⟨A, C, -, -, -, hcover, hAcrosscut, hCcrosscut⟩ :=
        hD.exists_two_isCrosscuts_branchPreimage_of_boundaryBranch hd
      have hdc : d ≠ c := by
        intro h
        subst d
        exact hc hd
      have hpreDisjoint : Disjoint (hD.branchPreimage d) (hD.branchPreimage c) :=
        hD.pairwise_disjoint_branchPreimage hdc
      have hAsub : A ⊆ hD.branchPreimage d := by
        rw [hcover]
        exact subset_union_left
      have hCsub : C ⊆ hD.branchPreimage d := by
        rw [hcover]
        exact subset_union_right
      have hAfrontier : Disjoint A (frontier Q) := by
        rw [hfrontier]
        exact Disjoint.mono hAsub hJsub hpreDisjoint
      have hCfrontier : Disjoint C (frontier Q) := by
        rw [hfrontier]
        exact Disjoint.mono hCsub hJsub hpreDisjoint
      obtain ⟨p, q, hAcrosscut⟩ := hAcrosscut
      obtain ⟨r, s, hCcrosscut⟩ := hCcrosscut
      have hAQ : Disjoint A Q :=
        disjoint_isPLBall_of_isCrosscut_of_subset_interior hAcrosscut hQ hQsub hAfrontier
      have hCQ : Disjoint C Q :=
        disjoint_isPLBall_of_isCrosscut_of_subset_interior hCcrosscut hQ hQsub hCfrontier
      rcases hcover.subset hxd with hxA | hxC
      · exact (Set.disjoint_left.mp hAQ hxA hx.2).elim
      · exact (Set.disjoint_left.mp hCQ hxC hx.2).elim
    · have hxclosed : x ∈ ⋃ d : {d : hD.singularSet.Branch //
          ¬hD.singularSet.IsBoundaryBranch d}, hD.branchPreimage d.1 :=
        mem_iUnion.mpr ⟨⟨d, hd⟩, hxd⟩
      exact hclosedInter.subset ⟨hxclosed, hx.2⟩
  · intro x hxJ
    refine ⟨hD.branchPreimage_subset_doublePointPreimage c (hJsub hxJ), ?_⟩
    exact hQ.isPolyhedron.isClosed.closure_eq ▸
      frontier_subset_closure (hfrontier.symm.subset hxJ)

open Classical in
theorem exists_innermost_isPLBall_doublePointPreimage_decomposition_of_exists_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          doublePointPreimage D D.domain ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ T : Set (EuclideanSpace ℝ (Fin 2)),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T) := by
  obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hclosedInter, hsplit⟩ :=
    hD.exists_innermost_isPLBall_branchPreimage_decomposition_of_exists_not_boundaryBranch
      hclosed
  have hJsub : J ⊆ hD.branchPreimage c := by
    rcases hsplit with hsingle | ⟨T, -, -, hcover⟩
    · rw [hsingle]
    · rw [hcover]
      exact subset_union_left
  have hfull := doublePointPreimage_inter_eq_of_closedBranch_inter_eq hD hc hJsub hQ
    hQsub hfrontier hclosedInter
  exact ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hfull, hsplit⟩

open Classical in
theorem exists_innermost_isPLBall_doublePointPreimage_decomposition_with_coordinate_of_exists_not_boundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          doublePointPreimage D D.domain ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ T : Set (EuclideanSpace ℝ (Fin 2)),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) J
                    (hD.singularSet.branchComplex c).space ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) T
                    (hD.singularSet.branchComplex c).space) := by
  obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hclosedInter, hsplit⟩ :=
    hD.exists_innermost_isPLBall_branchPreimage_decomposition_with_coordinate_of_exists_not_boundaryBranch
      hclosed
  have hJsub : J ⊆ hD.branchPreimage c := by
    rcases hsplit with hsingle | ⟨T, -, -, hcover, -, -⟩
    · rw [hsingle]
    · rw [hcover]
      exact subset_union_left
  have hfull := doublePointPreimage_inter_eq_of_closedBranch_inter_eq hD hc hJsub hQ
    hQsub hfrontier hclosedInter
  exact ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hfull, hsplit⟩

open Classical in
theorem exists_innermost_isPLBall_doublePointPreimage_with_nonsingular_case_two
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hclosed : ∃ c : hD.singularSet.Branch,
      ¬hD.singularSet.IsBoundaryBranch c) :
    ∃ c : hD.singularSet.Branch,
    ∃ J Q : Set (EuclideanSpace ℝ (Fin 2)),
      ¬hD.singularSet.IsBoundaryBranch c ∧ IsPLSphere 1 J ∧
        IsPLBall 2 Q ∧ Q ⊆ interior D.domain ∧ frontier Q = J ∧
          doublePointPreimage D D.domain ∩ Q = J ∧
            (hD.branchPreimage c = J ∨
              ∃ (T : Set (EuclideanSpace ℝ (Fin 2))) (A : SingularTwoCell M),
                IsPLSphere 1 T ∧ Disjoint J T ∧ hD.branchPreimage c = J ∪ T ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) J
                    (hD.singularSet.branchComplex c).space ∧
                  IsPLHomeomorphOn (hD.branchCoordinate c) T
                    (hD.singularSet.branchComplex c).space ∧
                  A.IsNonsingular ∧ A '' A.domain = D '' Q ∧
                    Set.range A.boundary = D '' J) := by
  obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hfull, hsplit⟩ :=
    hD.exists_innermost_isPLBall_doublePointPreimage_decomposition_with_coordinate_of_exists_not_boundaryBranch
      hclosed
  refine ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontier, hfull, ?_⟩
  rcases hsplit with hsingle | ⟨T, hT, hdisjoint, hcover, hJcoordinate, hTcoordinate⟩
  · exact Or.inl hsingle
  · right
    have hJsub : J ⊆ hD.branchPreimage c := by
      rw [hcover]
      exact subset_union_left
    have hQdomain : Q ⊆ D.domain := hQsub.trans interior_subset
    let A := D.restrict hQ hQdomain
    have hA :=
      hD.restrict_isNonsingular_of_doublePointPreimage_inter_eq_of_branchCoordinate
        hJsub hQ hQdomain hfrontier hfull hJcoordinate
    refine ⟨T, A, hT, hdisjoint, hcover, hJcoordinate, hTcoordinate,
      hA.1, ?_, hA.2⟩
    change D '' Q = D '' Q
    rfl

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
