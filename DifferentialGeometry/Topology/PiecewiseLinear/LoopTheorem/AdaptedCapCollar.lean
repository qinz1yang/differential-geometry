/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchNestedDescent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem twoSidedCollar_halves_of_upper_inside {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)} (hQ : IsClosed Q)
    (hfrontQ : frontier Q = J) (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) C)
    (hρ0 : ∀ x ∈ J, ρ (x, 0) = x) (hup : ρ '' (J ×ˢ Ioc (0 : ℝ) 1) ⊆ interior Q)
    (hlo : Disjoint (ρ '' (J ×ˢ Ico (-1 : ℝ) 0)) Q) :
    C ∩ Q = ρ '' (J ×ˢ Icc (0 : ℝ) 1) ∧ C \ interior Q = ρ '' (J ×ˢ Icc (-1 : ℝ) 0) := by
  have hJQ : ∀ x ∈ J, x ∈ Q ∧ x ∉ interior Q := by
    intro x hx
    have hxfr : x ∈ frontier Q := hfrontQ.symm.subset hx
    rw [hQ.frontier_eq] at hxfr
    exact hxfr
  constructor
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨⟨x, t⟩, hmem, rfl⟩ := hρ.bijOn.surjOn hy.1
      have hx : x ∈ J := hmem.1
      have ht : t ∈ Icc (-1 : ℝ) 1 := hmem.2
      rcases lt_or_ge t 0 with h | h
      · exact absurd hy.2 (Set.disjoint_left.mp hlo ⟨(x, t), ⟨hx, ht.1, h⟩, rfl⟩)
      · exact ⟨(x, t), ⟨hx, h, ht.2⟩, rfl⟩
    · rintro _ ⟨⟨x, t⟩, hmem, rfl⟩
      have hx : x ∈ J := hmem.1
      have ht : t ∈ Icc (0 : ℝ) 1 := hmem.2
      refine ⟨hρ.bijOn.mapsTo ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hρ0 x hx]
        exact (hJQ x hx).1
      · exact interior_subset (hup ⟨(x, t), ⟨hx, h, ht.2⟩, rfl⟩)
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨⟨x, t⟩, hmem, rfl⟩ := hρ.bijOn.surjOn hy.1
      have hx : x ∈ J := hmem.1
      have ht : t ∈ Icc (-1 : ℝ) 1 := hmem.2
      rcases le_or_gt t 0 with h | h
      · exact ⟨(x, t), ⟨hx, ht.1, h⟩, rfl⟩
      · exact absurd (hup ⟨(x, t), ⟨hx, h, ht.2⟩, rfl⟩) hy.2
    · rintro _ ⟨⟨x, t⟩, hmem, rfl⟩
      have hx : x ∈ J := hmem.1
      have ht : t ∈ Icc (-1 : ℝ) 0 := hmem.2
      refine ⟨hρ.bijOn.mapsTo ⟨hx, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h, hρ0 x hx]
        exact (hJQ x hx).2
      · exact fun hcon =>
          Set.disjoint_left.mp hlo ⟨(x, t), ⟨hx, ht.1, h⟩, rfl⟩ (interior_subset hcon)

private theorem isPLHomeomorphOn_neg_Icc_symm :
    IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap isHPolytope_Icc)
  refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
  · intro t ht
    change -1 ≤ -t ∧ -t ≤ 1
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro t ht
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩

open Classical in
theorem exists_twoSidedCollar_of_frontier_eq {P Q G : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q) (hJP : frontier Q ⊆ interior P)
    (hG : IsOpen G) (hJG : frontier Q ⊆ G) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin 2)))
      (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)),
      IsPolyhedron W ∧ W ⊆ G ∩ interior P ∧ (∀ x ∈ frontier Q, W ∈ 𝓝 x) ∧
        IsPLHomeomorphOn ρ (frontier Q ×ˢ Icc (-1 : ℝ) 1) W ∧
          (∀ x ∈ frontier Q, ρ (x, 0) = x) ∧
            W ∩ Q = ρ '' (frontier Q ×ˢ Icc (0 : ℝ) 1) ∧
              W \ interior Q = ρ '' (frontier Q ×ˢ Icc (-1 : ℝ) 0) := by
  classical
  set J := frontier Q with hJdef
  have hJ : IsPLSphere 1 J := hQ.isPLSphere_frontier
  have hJdom : J ⊆ P := hJP.trans interior_subset
  have hJconn : IsConnected J := IsPLSphere.isConnected (n := 0) hJ
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hJQ : ∀ x ∈ J, x ∈ Q ∧ x ∉ interior Q := by
    intro x hx
    have hxfr : x ∈ frontier Q := hx
    rw [hQclosed.frontier_eq] at hxfr
    exact hxfr
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  have _ : Finite K.faces := hKfin.to_subtype
  have hKball : IsPLBall 2 K.space := by rw [hKspace]; exact hP
  have hKman : IsCombinatorialManifoldWithBoundary 2 K :=
    IsPLBall.isCombinatorialManifoldWithBoundary (n := 1) hKball
  have hJK : J ⊆ K.space := hJdom.trans hKspace.symm.subset
  have hUopen : IsOpen (G ∩ interior P) := hG.inter isOpen_interior
  have hJU : J ⊆ G ∩ interior P := fun x hx => ⟨hJG hx, hJP hx⟩
  obtain ⟨W, ρ, hWpoly, -, hWU, hWnhds, hρ, hρ0⟩ :=
    hKman.exists_bicollar_of_isPLSphere_one K (isOrientable_of_isPLBall hKball) hJ hJK
      (by
        rw [← frontier_space_eq_boundaryComplex_space_of_finrank (d := _) (n := 1) (by simp) K
          hKman, hKspace]
        exact Set.disjoint_left.mpr fun x hxJ hxfr =>
          (mem_interior_iff_notMem_frontier (hJdom hxJ)).mp (hJP hxJ) hxfr)
      (Filter.mem_inf_of_left (mem_nhdsSet_iff_forall.mpr fun x hx => hUopen.mem_nhds (hJU hx)))
  have hJW : J ⊆ W := by
    intro x hx
    have hmem := hρ.bijOn.mapsTo
      (⟨hx, by norm_num⟩ : ((x, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈
        J ×ˢ Icc (-1 : ℝ) 1)
    rwa [hρ0 x hx] at hmem
  have hWnhd : ∀ x ∈ J, W ∈ 𝓝 x := by
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hWnhds
    intro x hx
    refine Filter.mem_of_superset ((hO.inter isOpen_interior).mem_nhds ⟨hJO hx, hJP hx⟩)
      fun y hy => hOW ⟨hy.1, hKspace.symm.subset (interior_subset hy.2)⟩
  have hclass : ∀ y ∈ W,
      y ∈ ρ '' (J ×ˢ Ico (-1 : ℝ) 0) ∨ y ∈ J ∨ y ∈ ρ '' (J ×ˢ Ioc (0 : ℝ) 1) := by
    intro y hy
    obtain ⟨⟨x, t⟩, hmem, rfl⟩ := hρ.bijOn.surjOn hy
    have hx : x ∈ J := hmem.1
    have ht : t ∈ Icc (-1 : ℝ) 1 := hmem.2
    rcases lt_trichotomy t 0 with h | h | h
    · exact Or.inl ⟨(x, t), ⟨hx, ht.1, h⟩, rfl⟩
    · subst h
      refine Or.inr (Or.inl ?_)
      rw [hρ0 x hx]
      exact hx
    · exact Or.inr (Or.inr ⟨(x, t), ⟨hx, h, ht.2⟩, rfl⟩)
  have hpre' : ∀ S : Set ℝ, S ⊆ Icc (-1 : ℝ) 1 → IsPreconnected S →
      IsPreconnected (ρ '' (J ×ˢ S)) := fun S hS hSconn =>
    (hJconn.isPreconnected.prod hSconn).image _
      (hρ.isPiecewiseAffineOn.continuousOn.mono (prod_mono Subset.rfl hS))
  have hdisjJ : ∀ S : Set ℝ, S ⊆ Icc (-1 : ℝ) 1 → (0 : ℝ) ∉ S →
      Disjoint (ρ '' (J ×ˢ S)) J := by
    intro S hS h0
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨x, t⟩, hmem, rfl⟩ hJmem
    have hx : x ∈ J := hmem.1
    have ht : t ∈ S := hmem.2
    have hpair : ((ρ (x, t), (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) = (x, t) :=
      hρ.bijOn.injOn ⟨hJmem, by norm_num⟩ ⟨hx, hS ht⟩ (hρ0 _ hJmem)
    have hzero : (0 : ℝ) = t := congrArg Prod.snd hpair
    apply h0
    rw [hzero]
    exact ht
  have hIoc : Ioc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hIco : Ico (-1 : ℝ) 0 ⊆ Icc (-1 : ℝ) 1 := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hupdich := subset_interior_or_disjoint_of_isPreconnected
    (hpre' _ hIoc (convex_Ioc (0 : ℝ) 1).isPreconnected) hQclosed
    (hdisjJ _ hIoc (by simp))
  have hlodich := subset_interior_or_disjoint_of_isPreconnected
    (hpre' _ hIco (convex_Ico (-1 : ℝ) 0).isPreconnected) hQclosed
    (hdisjJ _ hIco (by simp))
  obtain ⟨x₀, hx₀⟩ := hJconn.nonempty
  obtain ⟨ρ', hρ', hρ'0, hup, hlo⟩ :
      ∃ ρ' : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2),
        IsPLHomeomorphOn ρ' (J ×ˢ Icc (-1 : ℝ) 1) W ∧ (∀ x ∈ J, ρ' (x, 0) = x) ∧
          ρ' '' (J ×ˢ Ioc (0 : ℝ) 1) ⊆ interior Q ∧
            Disjoint (ρ' '' (J ×ˢ Ico (-1 : ℝ) 0)) Q := by
    rcases hupdich with hupin | hupout
    · rcases hlodich with hloin | hloout
      · refine absurd (mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (hWnhd x₀ hx₀) fun y hy => ?_)) (hJQ x₀ hx₀).2
        rcases hclass y hy with h | h | h
        · exact interior_subset (hloin h)
        · exact (hJQ y h).1
        · exact interior_subset (hupin h)
      · exact ⟨ρ, hρ, hρ0, hupin, hloout⟩
    · rcases hlodich with hloin | hloout
      · refine ⟨ρ ∘ Prod.map (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
          fun t : ℝ => -t,
          (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap isPLHomeomorphOn_neg_Icc_symm).trans hρ,
          fun x hx => ?_, ?_, ?_⟩
        · change ρ (x, -(0 : ℝ)) = x
          rw [neg_zero]
          exact hρ0 x hx
        · rintro _ ⟨⟨x, t⟩, hmem, rfl⟩
          have hx : x ∈ J := hmem.1
          have ht : t ∈ Ioc (0 : ℝ) 1 := hmem.2
          exact hloin ⟨(x, -t), ⟨hx, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
        · refine Set.disjoint_left.mpr ?_
          rintro _ ⟨⟨x, t⟩, hmem, rfl⟩ hQmem
          have hx : x ∈ J := hmem.1
          have ht : t ∈ Ico (-1 : ℝ) 0 := hmem.2
          exact Set.disjoint_left.mp hupout
            ⟨(x, -t), ⟨hx, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩ hQmem
      · obtain ⟨y, hyW, hyQ⟩ := mem_closure_iff_nhds.mp
          (by rw [hQ.closure_interior]; exact (hJQ x₀ hx₀).1) W (hWnhd x₀ hx₀)
        rcases hclass y hyW with h | h | h
        · exact absurd (interior_subset hyQ) (Set.disjoint_left.mp hloout h)
        · exact absurd hyQ (hJQ y h).2
        · exact absurd (interior_subset hyQ) (Set.disjoint_left.mp hupout h)
  obtain ⟨hCQ, hCout⟩ :=
    twoSidedCollar_halves_of_upper_inside hQclosed hJdef.symm hρ' hρ'0 hup hlo
  exact ⟨W, ρ', hWpoly, hWU, hWnhd, hρ', hρ'0, hCQ, hCout⟩

private theorem interior_union_eq_of_isClosed_of_disjoint {X : Type*} [TopologicalSpace X]
    {Q E : Set X} (hQ : IsClosed Q) (hE : IsClosed E) (hQE : Disjoint Q E) :
    interior (Q ∪ E) = interior Q ∪ interior E := by
  apply Subset.antisymm
  · intro x hx
    rcases interior_subset hx with hxQ | hxE
    · have hxE : x ∉ E := Set.disjoint_left.mp hQE hxQ
      have hsub : interior (Q ∪ E) ∩ Eᶜ ⊆ Q := by
        rintro y ⟨hy, hyE⟩
        rcases interior_subset hy with hyQ | hyE'
        · exact hyQ
        · exact absurd hyE' hyE
      exact Or.inl (interior_maximal hsub (isOpen_interior.inter hE.isOpen_compl) ⟨hx, hxE⟩)
    · have hxQ : x ∉ Q := fun hxQ => Set.disjoint_left.mp hQE hxQ hxE
      have hsub : interior (Q ∪ E) ∩ Qᶜ ⊆ E := by
        rintro y ⟨hy, hyQ⟩
        rcases interior_subset hy with hyQ' | hyE
        · exact absurd hyQ' hyQ
        · exact hyE
      exact Or.inr (interior_maximal hsub (isOpen_interior.inter hQ.isOpen_compl) ⟨hx, hxQ⟩)
  · exact union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_isTwoSidedBranchCollar_of_branchPreimage_eq_union [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : ¬hD.singularSet.IsBoundaryBranch c) {J T Q E : Set (EuclideanSpace ℝ (Fin 2))}
    (hpre : hD.branchPreimage c = J ∪ T) (hQ : IsPLBall 2 Q) (hfrontQ : frontier Q = J)
    (hE : IsPLBall 2 E) (hfrontE : frontier E = T) (hdisjoint : Disjoint Q E) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2)))
      (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)),
      hD.IsTwoSidedBranchCollar c (J ∪ T) (Q ∪ E) C ρ ∧
        Disjoint (ρ '' (J ×ˢ Icc (-1 : ℝ) 1)) E ∧ Disjoint (ρ '' (T ×ˢ Icc (-1 : ℝ) 1)) Q := by
  classical
  subst hfrontQ hfrontE
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hEclosed : IsClosed E := hE.isPolyhedron.isCompact.isClosed
  have hJQ : frontier Q ⊆ Q := hQclosed.frontier_subset
  have hTE : frontier E ⊆ E := hEclosed.frontier_subset
  have hJT : Disjoint (frontier Q) (frontier E) := hdisjoint.mono hJQ hTE
  have hJpoly : IsPolyhedron (frontier Q) := hQ.isPLSphere_frontier.isPolyhedron
  have hTpoly : IsPolyhedron (frontier E) := hE.isPLSphere_frontier.isPolyhedron
  have hint : frontier Q ∪ frontier E ⊆ interior D.domain := by
    rw [← hpre]
    exact hD.branchPreimage_subset_interior_of_not_boundaryBranch hc
  have _ : Finite hD.singularSet.Branch := hD.singularSet.finite_branch
  have hrest : doublePointPreimage D D.domain \ (frontier Q ∪ frontier E) =
      ⋃ b ∈ {b : hD.singularSet.Branch | b ≠ c}, hD.branchPreimage b := by
    apply Subset.antisymm
    · intro x hx
      have hxu : x ∈ ⋃ b, hD.branchPreimage b := by
        rw [hD.iUnion_branchPreimage]
        exact hx.1
      obtain ⟨b, hb⟩ := mem_iUnion.mp hxu
      refine mem_biUnion ?_ hb
      intro hbc
      exact hx.2 (hpre.subset (hbc ▸ hb))
    · intro x hx
      obtain ⟨b, hbc, hb⟩ := mem_iUnion₂.mp hx
      refine ⟨hD.branchPreimage_subset_doublePointPreimage b hb, fun hxJT => ?_⟩
      exact Set.disjoint_left.mp (hD.pairwise_disjoint_branchPreimage hbc) hb
        (hpre.symm.subset hxJT)
  have hrestclosed :
      IsClosed (doublePointPreimage D D.domain \ (frontier Q ∪ frontier E)) := by
    rw [hrest]
    exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun b _ =>
      (hD.branchPreimage_isCompact b).isClosed
  have hJTdpp : frontier Q ∪ frontier E ⊆ doublePointPreimage D D.domain := by
    rw [← hpre]
    exact hD.branchPreimage_subset_doublePointPreimage c
  have hrestJ : doublePointPreimage D D.domain \ frontier Q =
      frontier E ∪ (doublePointPreimage D D.domain \ (frontier Q ∪ frontier E)) := by
    ext x
    constructor
    · rintro ⟨hx, hxJ⟩
      by_cases hxT : x ∈ frontier E
      · exact Or.inl hxT
      · exact Or.inr ⟨hx, fun h => h.elim hxJ hxT⟩
    · rintro (hxT | ⟨hx, hxJT⟩)
      · exact ⟨hJTdpp (Or.inr hxT), fun hxJ => Set.disjoint_left.mp hJT hxJ hxT⟩
      · exact ⟨hx, fun hxJ => hxJT (Or.inl hxJ)⟩
  have hrestT : doublePointPreimage D D.domain \ frontier E =
      frontier Q ∪ (doublePointPreimage D D.domain \ (frontier Q ∪ frontier E)) := by
    ext x
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hxJ : x ∈ frontier Q
      · exact Or.inl hxJ
      · exact Or.inr ⟨hx, fun h => h.elim hxJ hxT⟩
    · rintro (hxJ | ⟨hx, hxJT⟩)
      · exact ⟨hJTdpp (Or.inl hxJ), fun hxT => Set.disjoint_left.mp hJT hxJ hxT⟩
      · exact ⟨hx, fun hxT => hxJT (Or.inr hxT)⟩
  have hrestJclosed : IsClosed (doublePointPreimage D D.domain \ frontier Q) := by
    rw [hrestJ]
    exact hTpoly.isCompact.isClosed.union hrestclosed
  have hrestTclosed : IsClosed (doublePointPreimage D D.domain \ frontier E) := by
    rw [hrestT]
    exact hJpoly.isCompact.isClosed.union hrestclosed
  obtain ⟨U₁, U₂, hU₁, hU₂, hJU₁, hTU₂, hU₁₂⟩ :=
    SeparatedNhds.of_isCompact_isCompact hJpoly.isCompact hTpoly.isCompact hJT
  obtain ⟨WJ, ρJ, hWJpoly, hWJsub, hWJnhd, hρJ, hρJ0, hWJQ, hWJout⟩ :=
    exists_twoSidedCollar_of_frontier_eq
      (G := U₁ ∩ (doublePointPreimage D D.domain \ frontier Q)ᶜ ∩ Eᶜ)
      D.isPLBall_domain hQ (fun x hx => hint (Or.inl hx))
      ((hU₁.inter hrestJclosed.isOpen_compl).inter hEclosed.isOpen_compl)
      (fun x hx =>
        ⟨⟨hJU₁ hx, fun h => h.2 hx⟩, fun hxE => Set.disjoint_left.mp hdisjoint (hJQ hx) hxE⟩)
  obtain ⟨WT, ρT, hWTpoly, hWTsub, hWTnhd, hρT, hρT0, hWTE, hWTout⟩ :=
    exists_twoSidedCollar_of_frontier_eq
      (G := U₂ ∩ (doublePointPreimage D D.domain \ frontier E)ᶜ ∩ Qᶜ)
      D.isPLBall_domain hE (fun x hx => hint (Or.inr hx))
      ((hU₂.inter hrestTclosed.isOpen_compl).inter hQclosed.isOpen_compl)
      (fun x hx =>
        ⟨⟨hTU₂ hx, fun h => h.2 hx⟩, fun hxQ => Set.disjoint_left.mp hdisjoint hxQ (hTE hx)⟩)
  have hWJWT : Disjoint WJ WT :=
    hU₁₂.mono (fun x hx => (hWJsub hx).1.1.1) fun x hx => (hWTsub hx).1.1.1
  have hWJE : Disjoint WJ E := Set.disjoint_left.mpr fun x hx => (hWJsub hx).1.2
  have hWTQ : Disjoint WT Q := Set.disjoint_left.mpr fun x hx => (hWTsub hx).1.2
  have hPQ : frontier Q ×ˢ Icc (-1 : ℝ) 1 ∩ frontier E ×ˢ Icc (-1 : ℝ) 1 = ∅ := by
    exact Set.eq_empty_iff_forall_notMem.mpr fun p hp =>
      Set.disjoint_left.mp hJT hp.1.1 hp.2.1
  obtain ⟨ρ, hρ, hρJeq, hρTeq⟩ :
      ∃ ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2),
        IsPLHomeomorphOn ρ ((frontier Q ∪ frontier E) ×ˢ Icc (-1 : ℝ) 1) (WJ ∪ WT) ∧
          EqOn ρ ρJ (frontier Q ×ˢ Icc (-1 : ℝ) 1) ∧
            EqOn ρ ρT (frontier E ×ˢ Icc (-1 : ℝ) 1) := by
    have hpw := hρJ.piecewise hρT (hJpoly.prod isHPolytope_Icc.isPolyhedron)
      (hTpoly.prod isHPolytope_Icc.isPolyhedron) (by rw [hPQ]; exact eqOn_empty _ _)
      (by rw [hPQ, image_empty]; exact (Set.disjoint_iff_inter_eq_empty.mp hWJWT).symm)
    rw [← union_prod] at hpw
    exact ⟨_, hpw, fun p hp => ite_eq_left hp,
      fun p hp => ite_eq_right fun h => Set.disjoint_left.mp hJT h.1 hp.1⟩
  have himage : ∀ S : Set ℝ, S ⊆ Icc (-1 : ℝ) 1 →
      ρ '' ((frontier Q ∪ frontier E) ×ˢ S) =
        ρJ '' (frontier Q ×ˢ S) ∪ ρT '' (frontier E ×ˢ S) := by
    intro S hS
    rw [union_prod, image_union, (hρJeq.mono (prod_mono Subset.rfl hS)).image_eq,
      (hρTeq.mono (prod_mono Subset.rfl hS)).image_eq]
  have hρ0 : ∀ x ∈ frontier Q ∪ frontier E, ρ (x, 0) = x := by
    rintro x (hx | hx)
    · rw [hρJeq ⟨hx, by norm_num, by norm_num⟩]
      exact hρJ0 x hx
    · rw [hρTeq ⟨hx, by norm_num, by norm_num⟩]
      exact hρT0 x hx
  have hJW : frontier Q ⊆ WJ := by
    intro x hx
    have hmem := hρJ.bijOn.mapsTo
      (⟨hx, by norm_num⟩ : ((x, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈
        frontier Q ×ˢ Icc (-1 : ℝ) 1)
    rwa [hρJ0 x hx] at hmem
  have hTW : frontier E ⊆ WT := by
    intro x hx
    have hmem := hρT.bijOn.mapsTo
      (⟨hx, by norm_num⟩ : ((x, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈
        frontier E ×ˢ Icc (-1 : ℝ) 1)
    rwa [hρT0 x hx] at hmem
  have hdpp : doublePointPreimage D D.domain ∩ (WJ ∪ WT) = frontier Q ∪ frontier E := by
    apply Subset.antisymm
    · rintro x ⟨hxd, hxJ | hxT⟩
      · by_contra hxJT
        exact (hWJsub hxJ).1.1.2 ⟨hxd, fun h => hxJT (Or.inl h)⟩
      · by_contra hxJT
        exact (hWTsub hxT).1.1.2 ⟨hxd, fun h => hxJT (Or.inr h)⟩
    · intro x hx
      refine ⟨hJTdpp hx, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl (hJW hx)
      · exact Or.inr (hTW hx)
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by norm_num) le_rfl
  have hIcc10 : Icc (-1 : ℝ) 0 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc le_rfl (by norm_num)
  have hCQ : (WJ ∪ WT) ∩ (Q ∪ E) = ρ '' ((frontier Q ∪ frontier E) ×ˢ Icc (0 : ℝ) 1) := by
    rw [himage _ hIcc01, ← hWJQ, ← hWTE]
    ext x
    constructor
    · rintro ⟨hxJ | hxT, hxQ | hxE⟩
      · exact Or.inl ⟨hxJ, hxQ⟩
      · exact absurd hxE (Set.disjoint_left.mp hWJE hxJ)
      · exact absurd hxQ (Set.disjoint_left.mp hWTQ hxT)
      · exact Or.inr ⟨hxT, hxE⟩
    · rintro (⟨hxJ, hxQ⟩ | ⟨hxT, hxE⟩)
      · exact ⟨Or.inl hxJ, Or.inl hxQ⟩
      · exact ⟨Or.inr hxT, Or.inr hxE⟩
  have hintQE : interior (Q ∪ E) = interior Q ∪ interior E :=
    interior_union_eq_of_isClosed_of_disjoint hQclosed hEclosed hdisjoint
  have hCout : (WJ ∪ WT) \ interior (Q ∪ E) =
      ρ '' ((frontier Q ∪ frontier E) ×ˢ Icc (-1 : ℝ) 0) := by
    rw [himage _ hIcc10, ← hWJout, ← hWTout, hintQE]
    ext x
    constructor
    · rintro ⟨hxJ | hxT, hxint⟩
      · exact Or.inl ⟨hxJ, fun h => hxint (Or.inl h)⟩
      · exact Or.inr ⟨hxT, fun h => hxint (Or.inr h)⟩
    · rintro (⟨hxJ, hxQ⟩ | ⟨hxT, hxE⟩)
      · refine ⟨Or.inl hxJ, ?_⟩
        rintro (h | h)
        · exact hxQ h
        · exact Set.disjoint_left.mp hWJE hxJ (interior_subset h)
      · refine ⟨Or.inr hxT, ?_⟩
        rintro (h | h)
        · exact Set.disjoint_left.mp hWTQ hxT (interior_subset h)
        · exact hxE h
  have hCint : WJ ∪ WT ⊆ interior D.domain :=
    union_subset (fun x hx => (hWJsub hx).2) fun x hx => (hWTsub hx).2
  have hρJimg : ρ '' (frontier Q ×ˢ Icc (-1 : ℝ) 1) = WJ := by
    rw [hρJeq.image_eq, hρJ.image_eq]
  have hρTimg : ρ '' (frontier E ×ˢ Icc (-1 : ℝ) 1) = WT := by
    rw [hρTeq.image_eq, hρT.image_eq]
  refine ⟨WJ ∪ WT, ρ, ⟨hpre, hWJpoly.union hWTpoly, hCint,
    union_subset_union hJW hTW, ?_, hρ, hρ0, hdpp, hCQ, hCout, ?_, ?_, ?_⟩,
    hρJimg ▸ hWJE, hρTimg ▸ hWTQ⟩
  · rintro x (hx | hx)
    · exact Filter.mem_of_superset (hWJnhd x hx) subset_union_left
    · exact Filter.mem_of_superset (hWTnhd x hx) subset_union_right
  · rw [hCQ]
    exact hρ.restrict
      ((hJpoly.union hTpoly).prod (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron)
      (prod_mono Subset.rfl hIcc01)
  · rw [hCout]
    exact hρ.restrict
      ((hJpoly.union hTpoly).prod (isHPolytope_Icc (a := (-1 : ℝ)) (b := 0)).isPolyhedron)
      (prod_mono Subset.rfl hIcc10)
  · apply Subset.antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, hydouble⟩
      exact ⟨z, hdpp.subset ⟨⟨interior_subset (hCint hz.1), hydouble⟩, hz.1⟩, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨z, ⟨?_, ?_⟩, rfl⟩, (hJTdpp hz).2⟩
      · rcases hz with hz | hz
        · exact Or.inl (hJW hz)
        · exact Or.inr (hTW hz)
      · rcases hz with hz | hz
        · exact Or.inl (hJQ hz)
        · exact Or.inr (hTE hz)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
