/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchPreimage
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem subset_interior_or_disjoint_of_preconnected {X : Type*} [TopologicalSpace X]
    {S E : Set X} (hS : IsPreconnected S) (hE : IsClosed E)
    (hdisjoint : Disjoint S (frontier E)) : S ⊆ interior E ∨ Disjoint S E := by
  by_cases hin : (S ∩ E).Nonempty
  · refine Or.inl fun x hx => ?_
    by_contra hxi
    obtain ⟨y, hyS, hyE, hyout⟩ :=
      isPreconnected_closed_iff.mp hS E (interior E)ᶜ hE isOpen_interior.isClosed_compl
        (fun z _ => by
          by_cases hz : z ∈ E
          · exact Or.inl hz
          · exact Or.inr fun hzi => hz (interior_subset hzi))
        hin ⟨x, hx, hxi⟩
    refine Set.disjoint_left.mp hdisjoint hyS ?_
    rw [hE.frontier_eq]
    exact ⟨hyE, hyout⟩
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hin))

private theorem collar_halves_of_upper_inside {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
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

private theorem isPLHomeomorphOn_neg_Icc :
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

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

def IsTwoSidedBranchCollar (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
    (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  hD.branchPreimage c = J ∧ IsPolyhedron C ∧ C ⊆ interior D.domain ∧ J ⊆ C ∧
    (∀ x ∈ J, C ∈ 𝓝 x) ∧ IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) C ∧
      (∀ x ∈ J, ρ (x, 0) = x) ∧ doublePointPreimage D D.domain ∩ C = J ∧
        C ∩ Q = ρ '' (J ×ˢ Icc (0 : ℝ) 1) ∧ C \ interior Q = ρ '' (J ×ˢ Icc (-1 : ℝ) 0) ∧
          IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) (C ∩ Q) ∧
            IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 0) (C \ interior Q) ∧
              D '' (C ∩ Q) ∩ doublePointSet D D.domain = D '' J

open Classical in
theorem exists_isTwoSidedBranchCollar_of_branchPreimage_eq [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : ¬hD.singularSet.IsBoundaryBranch c) {J Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) (hpre : hD.branchPreimage c = J) (hQ : IsPLBall 2 Q)
    (hfrontQ : frontier Q = J) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2)))
      (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)),
      hD.IsTwoSidedBranchCollar c J Q C ρ := by
  classical
  have hJint : J ⊆ interior D.domain := by
    rw [← hpre]
    exact hD.branchPreimage_subset_interior_of_not_boundaryBranch hc
  have hJdom : J ⊆ D.domain := hJint.trans interior_subset
  have hJconn : IsConnected J := IsPLSphere.isConnected (n := 0) hJ
  have hQclosed : IsClosed Q := hQ.isPolyhedron.isCompact.isClosed
  have hJQ : ∀ x ∈ J, x ∈ Q ∧ x ∉ interior Q := by
    intro x hx
    have hxfr : x ∈ frontier Q := hfrontQ.symm.subset hx
    rw [hQclosed.frontier_eq] at hxfr
    exact hxfr
  obtain ⟨K, hKfin, hKspace⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  have _ : Finite K.faces := hKfin.to_subtype
  have hKball : IsPLBall 2 K.space := by rw [hKspace]; exact D.isPLBall_domain
  have hKman : IsCombinatorialManifoldWithBoundary 2 K :=
    IsPLBall.isCombinatorialManifoldWithBoundary (n := 1) hKball
  have hJK : J ⊆ K.space := hJdom.trans hKspace.symm.subset
  have _ : Finite hD.singularSet.Branch := hD.singularSet.finite_branch
  have hrest : doublePointPreimage D D.domain \ J =
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
      refine ⟨hD.branchPreimage_subset_doublePointPreimage b hb, fun hxJ => ?_⟩
      exact Set.disjoint_left.mp (hD.pairwise_disjoint_branchPreimage hbc) hb
        (hpre.symm.subset hxJ)
  have hrestclosed : IsClosed (doublePointPreimage D D.domain \ J) := by
    rw [hrest]
    exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun b _ =>
      (hD.branchPreimage_isCompact b).isClosed
  have hUopen : IsOpen (interior D.domain \ (doublePointPreimage D D.domain \ J)) :=
    isOpen_interior.sdiff hrestclosed
  have hJU : J ⊆ interior D.domain \ (doublePointPreimage D D.domain \ J) :=
    fun x hx => ⟨hJint hx, fun hcon => hcon.2 hx⟩
  obtain ⟨W, ρ, hWpoly, -, hWU, hWnhds, hρ, hρ0⟩ :=
    hKman.exists_bicollar_of_isPLSphere_one K (isOrientable_of_isPLBall hKball) hJ hJK
      (by
        rw [← frontier_space_eq_boundaryComplex_space_of_finrank (d := _) (n := 1) (by simp) K
          hKman, hKspace]
        exact Set.disjoint_left.mpr fun x hxJ hxfr =>
          (mem_interior_iff_notMem_frontier (hJdom hxJ)).mp (hJint hxJ) hxfr)
      (Filter.mem_inf_of_left (mem_nhdsSet_iff_forall.mpr fun x hx => hUopen.mem_nhds (hJU hx)))
  have hWint : W ⊆ interior D.domain := fun x hx => (hWU hx).1
  have hJW : J ⊆ W := by
    intro x hx
    have hmem := hρ.bijOn.mapsTo
      (⟨hx, by norm_num⟩ : ((x, (0 : ℝ)) : EuclideanSpace ℝ (Fin 2) × ℝ) ∈
        J ×ˢ Icc (-1 : ℝ) 1)
    rwa [hρ0 x hx] at hmem
  have hWdpp : doublePointPreimage D D.domain ∩ W = J := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxJ
      exact (hWU hx.2).2 ⟨hx.1, hxJ⟩
    · intro x hx
      exact ⟨hD.branchPreimage_subset_doublePointPreimage c (hpre.symm.subset hx), hJW hx⟩
  have hWnhd : ∀ x ∈ J, W ∈ 𝓝 x := by
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hWnhds
    intro x hx
    refine Filter.mem_of_superset ((hO.inter isOpen_interior).mem_nhds ⟨hJO hx, hJint hx⟩)
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
  have hupdich := subset_interior_or_disjoint_of_preconnected
    (hpre' _ hIoc (convex_Ioc (0 : ℝ) 1).isPreconnected) hQclosed
    (by rw [hfrontQ]; exact hdisjJ _ hIoc (by simp))
  have hlodich := subset_interior_or_disjoint_of_preconnected
    (hpre' _ hIco (convex_Ico (-1 : ℝ) 0).isPreconnected) hQclosed
    (by rw [hfrontQ]; exact hdisjJ _ hIco (by simp))
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
          (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap isPLHomeomorphOn_neg_Icc).trans hρ,
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
  obtain ⟨hCQ, hCout⟩ := collar_halves_of_upper_inside hQclosed hfrontQ hρ' hρ'0 hup hlo
  refine ⟨W, ρ', hpre, hWpoly, hWint, hJW, hWnhd, hρ', hρ'0, hWdpp, hCQ, hCout, ?_, ?_, ?_⟩
  · rw [hCQ]
    exact hρ'.restrict
      (hJ.isPolyhedron.prod (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron)
      (prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl))
  · rw [hCout]
    exact hρ'.restrict
      (hJ.isPolyhedron.prod (isHPolytope_Icc (a := (-1 : ℝ)) (b := 0)).isPolyhedron)
      (prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num)))
  · apply Subset.antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, hydouble⟩
      exact ⟨z, hWdpp.subset ⟨⟨interior_subset (hWint hz.1), hydouble⟩, hz.1⟩, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨⟨z, ⟨hJW hz, (hJQ z hz).1⟩, rfl⟩,
        (hD.branchPreimage_subset_doublePointPreimage c (hpre.symm.subset hz)).2⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
