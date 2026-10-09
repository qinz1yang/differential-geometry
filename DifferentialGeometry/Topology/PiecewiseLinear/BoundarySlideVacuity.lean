/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.ModelSlideLong

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem NormalSingularCellData.branchCarrier_inter_boundary_nontrivial_of_isBoundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    (hD.singularSet.branchCarrier c ∩ BdM).Nontrivial := by
  obtain ⟨A, C, -, -, -, hcover, hAcoord, -, -, ⟨p, q, hcut⟩, -⟩ :=
    hD.exists_two_isCrosscuts_branchPreimage_of_boundaryBranch_with_coordinate hc
  obtain ⟨f, -, hinj, hfA, hf0, hf1⟩ := hcut.arc
  have hpA : p ∈ A := by
    rw [← hfA]
    exact ⟨0, unitInterval.zero_mem, hf0⟩
  have hqA : q ∈ A := by
    rw [← hfA]
    exact ⟨1, unitInterval.one_mem, hf1⟩
  have hpq : p ≠ q := fun h =>
    zero_ne_one (hinj unitInterval.zero_mem unitInterval.one_mem (hf0.trans (h.trans hf1.symm)))
  have hAsub : A ⊆ hD.branchPreimage c := by
    rw [hcover]
    exact subset_union_left
  have hDinjA : InjOn D A := by
    intro x hx z hz hxz
    apply hAcoord.bijOn.injOn hx hz
    apply (hD.singularSet.branchPieceIn c).bijOn.injOn
      (hAcoord.bijOn.mapsTo hx) (hAcoord.bijOn.mapsTo hz)
    calc
      (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c x) = D x :=
        hD.branchPieceIn_map_branchCoordinate c (hAsub hx)
      _ = D z := hxz
      _ = (hD.singularSet.branchPieceIn c).map (hD.branchCoordinate c z) :=
        (hD.branchPieceIn_map_branchCoordinate c (hAsub hz)).symm
  have hbd : ∀ z ∈ frontier D.domain, D z ∈ BdM := by
    intro z hz
    have hmem : D z ∈ Set.range D.boundary := ⟨⟨z, hz⟩, D.boundary_apply ⟨z, hz⟩⟩
    rw [← hD.image_inter_boundary] at hmem
    exact hmem.2
  exact ⟨D p, ⟨(hAsub hpA).2, hbd p hcut.left_mem⟩, D q, ⟨(hAsub hqA).2, hbd q hcut.right_mem⟩,
    fun h => hpq (hDinjA hpA hqA h)⟩

theorem NormalSingularCellData.branchCarrier_inter_boundary_subsingleton_of_slide_chart
    (hD : NormalSingularCellData D BdM B) (cb : hD.singularSet.Branch)
    {W : Set M} {P Pc Q : Set (EuclideanSpace ℝ (Fin 2))} {R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hesrc : e.source ⊆ E.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : hD.singularSet.branchCarrier cb ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : D '' P ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandA c))
    (hB : D '' Q ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandQ a b))
    (hdom : P ∪ Pc = D.domain) (hinjP : InjOn D P) (hinjQ : InjOn D (Q ∩ D ⁻¹' W))
    (hPcQ : Pc ∩ D ⁻¹' W ⊆ Q)
    {Bd₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hBdE : ∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁)
    (hBd₁ : ∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0) :
    (hD.singularSet.branchCarrier cb ∩ BdM).Subsingleton := by
  have hpt : ∀ y ∈ hD.singularSet.branchCarrier cb, y ∈ BdM →
      y = E.symm (e.symm ((0 : ℝ), (0 : ℝ), (0 : ℝ))) := by
    intro y hy hyBd
    have hysupp := hSK hy
    have hyW : y ∈ W := subset_of_mem_nhdsSet hW hysupp
    obtain ⟨x, hx, z, hz, hxz, hxy, hzy⟩ :=
      hD.singularSet.branchCarrier_subset_doublePointSet cb hy
    have hside : ∀ u v, u ∈ D.domain → v ∈ D.domain → D u = y → D v = y →
        u ∈ P → v ∉ P → y ∈ D '' P ∧ y ∈ D '' Q := by
      intro u v _ hv huy hvy huP hvP
      have hvPc : v ∈ Pc := by
        rw [← hdom] at hv
        exact hv.resolve_left hvP
      have hvW : v ∈ D ⁻¹' W := by
        change D v ∈ W
        rw [hvy]
        exact hyW
      exact ⟨⟨u, huP, huy⟩, ⟨v, hPcQ ⟨hvPc, hvW⟩, hvy⟩⟩
    have hPQ : y ∈ D '' P ∧ y ∈ D '' Q := by
      by_cases hxP : x ∈ P
      · by_cases hzP : z ∈ P
        · exact absurd (hinjP hxP hzP (hxy.trans hzy.symm)) hxz
        · exact hside x z hx hz hxy hzy hxP hzP
      · by_cases hzP : z ∈ P
        · exact hside z x hz hx hzy hxy hzP hxP
        · have hxPc : x ∈ Pc := by
            rw [← hdom] at hx
            exact hx.resolve_left hxP
          have hzPc : z ∈ Pc := by
            rw [← hdom] at hz
            exact hz.resolve_left hzP
          have hxW : x ∈ D ⁻¹' W := by
            change D x ∈ W
            rw [hxy]
            exact hyW
          have hzW : z ∈ D ⁻¹' W := by
            change D z ∈ W
            rw [hzy]
            exact hyW
          exact absurd (hinjQ ⟨hPcQ ⟨hxPc, hxW⟩, hxW⟩ ⟨hPcQ ⟨hzPc, hzW⟩, hzW⟩
            (hxy.trans hzy.symm)) hxz
    obtain ⟨_, ⟨pa, hpa, rfl⟩, hpay⟩ := hA ⟨hPQ.1, hysupp⟩
    obtain ⟨_, ⟨qb, hqb, rfl⟩, hqby⟩ := hB ⟨hPQ.2, hysupp⟩
    have hpaT : pa ∈ e.target := hAt hpa
    have hqbT : qb ∈ e.target := hBt hqb
    have hpaE : e.symm pa ∈ E.target := hesrc (e.map_target hpaT)
    have hqbE : e.symm qb ∈ E.target := hesrc (e.map_target hqbT)
    have heq : e.symm pa = e.symm qb := by
      rw [← E.right_inv hpaE, ← E.right_inv hqbE, hpay, hqby]
    have hpq : pa = qb := by
      rw [← e.right_inv hpaT, ← e.right_inv hqbT, heq]
    have hy1 : pa.1 = 0 := by
      have hyE : y ∈ E.source := by
        rw [← hpay]
        exact E.map_target hpaE
      have hEy : E y = e.symm pa := by
        rw [← hpay]
        exact E.right_inv hpaE
      have h := (hBdE y hyE).mp hyBd
      rw [hEy, hBd₁ _ (e.map_target hpaT), e.right_inv hpaT] at h
      exact h
    have hy21 : pa.2.1 = 0 := by
      rw [hpq]
      exact hqb.1
    have hy22 : pa.2.2 = 0 := hpa.1
    have hpa0 : pa = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := Prod.ext hy1 (Prod.ext hy21 hy22)
    rw [← hpay, hpa0]
  intro y₁ hy₁ y₂ hy₂
  rw [hpt y₁ hy₁.1 hy₁.2, hpt y₂ hy₂.1 hy₂.2]

theorem NormalSingularCellData.not_boundary_slide_chart_of_isBoundaryBranch
    [T2Space M] (hD : NormalSingularCellData D BdM B)
    {cb : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch cb)
    {W : Set M} {P Pc Q : Set (EuclideanSpace ℝ (Fin 2))} {R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hesrc : e.source ⊆ E.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : hD.singularSet.branchCarrier cb ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : D '' P ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandA c))
    (hB : D '' Q ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandQ a b))
    (hdom : P ∪ Pc = D.domain) (hinjP : InjOn D P) (hinjQ : InjOn D (Q ∩ D ⁻¹' W))
    (hPcQ : Pc ∩ D ⁻¹' W ⊆ Q)
    {Bd₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hBdE : ∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁)
    (hBd₁ : ∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0) : False :=
  (hD.branchCarrier_inter_boundary_nontrivial_of_isBoundaryBranch hc).not_subsingleton
    (hD.branchCarrier_inter_boundary_subsingleton_of_slide_chart cb E e hesrc hAt hBt hSK hW
      hA hB hdom hinjP hinjQ hPcQ hBdE hBd₁)

end DifferentialGeometry.Topology.PiecewiseLinear
