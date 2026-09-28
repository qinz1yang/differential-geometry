/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import Mathlib.Topology.LocallyFinite

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_union_of_locallyFinite_pieces
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {A : Set E} {B : Set F} {K : Set E}
    {Y : Set F} {P : ι → Set E} {Q : ι → Set F} {F₀ : E → F}
    {f : ι → E → F} (hA : IsClosed A) (hB : IsClosed B)
    (hPclosed : ∀ i, IsClosed (P i)) (hQclosed : ∀ i, IsClosed (Q i))
    (hF : IsPLHomeomorphOn F₀ A B)
    (hf : ∀ i, IsPLHomeomorphOn (f i) (P i) (Q i))
    (hbase : ∀ i, EqOn F₀ (f i) (A ∩ P i))
    (hbaseMeet : ∀ i, F₀ '' (A ∩ P i) = B ∩ Q i)
    (hcompat : ∀ i j, EqOn (f i) (f j) (P i ∩ P j))
    (hmeet : ∀ i j, f i '' (P i ∩ P j) = Q i ∩ Q j)
    (hK : A ∪ ⋃ i, P i = K) (hY : B ∪ ⋃ i, Q i = Y)
    (hsourceLocal : ∀ x ∈ K, ∃ U ∈ 𝓝 x,
      {i | (P i ∩ U).Nonempty}.Finite)
    (htargetLocal : ∀ y ∈ Y, ∃ U ∈ 𝓝 y,
      {i | (Q i ∩ U).Nonempty}.Finite) :
    ∃ G : E → F, IsPLHomeomorphOn G K Y ∧ EqOn G F₀ A ∧
      ∀ i, EqOn G (f i) (P i) ∧ G '' P i = Q i := by
  classical
  let G : E → F := fun x =>
    if hx : x ∈ A then F₀ x
    else if hx' : ∃ i, x ∈ P i then f (Classical.choose hx') x
    else 0
  have hGEqA : EqOn G F₀ A := by
    intro x hx
    simp [G, hx]
  have hGEqP : ∀ i, EqOn G (f i) (P i) := by
    intro i x hx
    by_cases hxA : x ∈ A
    · rw [show G x = F₀ x by simp [G, hxA], hbase i ⟨hxA, hx⟩]
    · have hx' : ∃ j, x ∈ P j := ⟨i, hx⟩
      simp only [G, dite_eq_right hxA, dite_eq_left hx']
      exact hcompat _ i ⟨Classical.choose_spec hx', hx⟩
  have hGmaps : MapsTo G K Y := by
    intro x hx
    rw [← hK] at hx
    rcases hx with hxA | hxP
    · rw [hGEqA hxA]
      exact hY ▸ Or.inl (hF.bijOn.mapsTo hxA)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
      rw [hGEqP i hxi]
      exact hY ▸ Or.inr (mem_iUnion.mpr ⟨i, (hf i).bijOn.mapsTo hxi⟩)
  have hcrossA : ∀ i, ∀ x ∈ A, ∀ y ∈ P i, G x = G y → x = y := by
    intro i x hxA y hy hxy
    have hyim : G y ∈ B ∩ Q i := by
      have hxB : G x ∈ B := by
        rw [hGEqA hxA]
        exact hF.bijOn.mapsTo hxA
      refine ⟨hxy ▸ hxB, ?_⟩
      · rw [hGEqP i hy]
        exact (hf i).bijOn.mapsTo hy
    obtain ⟨z, hz, hzy⟩ := (hbaseMeet i).symm.subset hyim
    have hxz : x = z := by
      apply hF.bijOn.injOn hxA hz.1
      calc
        F₀ x = G x := (hGEqA hxA).symm
        _ = G y := hxy
        _ = F₀ z := hzy.symm
    have hzy' : z = y := by
      apply (hf i).bijOn.injOn hz.2 hy
      calc
        f i z = F₀ z := (hbase i ⟨hz.1, hz.2⟩).symm
        _ = G y := hzy
        _ = f i y := hGEqP i hy
    exact hxz.trans hzy'
  have hcross : ∀ i j, ∀ x ∈ P i, ∀ y ∈ P j, G x = G y → x = y := by
    intro i j x hx y hy hxy
    have him : G x ∈ Q i ∩ Q j := by
      refine ⟨?_, ?_⟩
      · rw [hGEqP i hx]
        exact (hf i).bijOn.mapsTo hx
      · rw [hxy, hGEqP j hy]
        exact (hf j).bijOn.mapsTo hy
    obtain ⟨z, hz, hzx⟩ := (hmeet i j).symm.subset him
    have hxz : x = z := by
      apply (hf i).bijOn.injOn hx hz.1
      calc
        f i x = G x := (hGEqP i hx).symm
        _ = f i z := hzx.symm
    have hzy : z = y := by
      apply (hf j).bijOn.injOn hz.2 hy
      calc
        f j z = f i z := (hcompat i j hz).symm
        _ = G x := hzx
        _ = G y := hxy
        _ = f j y := hGEqP j hy
    exact hxz.trans hzy
  have hGinj : InjOn G K := by
    intro x hx y hy hxy
    rw [← hK] at hx hy
    rcases hx with hxA | hxP <;> rcases hy with hyA | hyP
    · exact hF.bijOn.injOn hxA hyA ((hGEqA hxA).symm.trans (hxy.trans (hGEqA hyA)))
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hyP
      exact (hcrossA j x hxA y hj hxy)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
      exact (hcrossA i y hyA x hi hxy.symm).symm
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
      obtain ⟨j, hj⟩ := mem_iUnion.mp hyP
      exact hcross i j x hi y hj hxy
  have hGsurj : SurjOn G K Y := by
    intro y hy
    rw [← hY] at hy
    rcases hy with hyB | hyQ
    · obtain ⟨x, hx, hxy⟩ := hF.bijOn.surjOn hyB
      exact ⟨x, hK ▸ Or.inl hx, (hGEqA hx).trans hxy⟩
    · obtain ⟨i, hyi⟩ := mem_iUnion.mp hyQ
      obtain ⟨x, hx, hxy⟩ := (hf i).bijOn.surjOn hyi
      exact ⟨x, hK ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩), (hGEqP i hx).trans hxy⟩
  have hGbij : BijOn G K Y := ⟨hGmaps, hGinj, hGsurj⟩
  have hGfinite : ∀ s : Finset ι,
      IsPiecewiseAffineOn G (A ∪ ⋃ i ∈ s, P i) := by
    intro s
    have hAaff : IsPiecewiseAffineOn G A :=
      hF.isPiecewiseAffineOn.congr hGEqA
    induction s using Finset.induction_on with
    | empty => simpa using hAaff
    | @insert i s hi ih =>
        have hpiece : IsPiecewiseAffineOn G (P i) :=
          (hf i).isPiecewiseAffineOn.congr (hGEqP i)
        have hrestc : IsClosed (A ∪ ⋃ j ∈ s, P j) := by
          exact hA.union (isClosed_biUnion_finset fun j _ => hPclosed j)
        have hun := ih.union_of_isClosed hpiece hrestc (hPclosed i)
        simpa [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using hun
  have hGpl : IsPiecewiseAffineOn G K := by
    intro x hx
    obtain ⟨U, hU, hfin⟩ := hsourceLocal x hx
    let s : Finset ι := hfin.toFinset
    have hxR : x ∈ A ∪ ⋃ i ∈ s, P i := by
      rw [← hK] at hx
      rcases hx with hxA | hxP
      · exact Or.inl hxA
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxP
        have hi : i ∈ s := hfin.mem_toFinset.mpr ⟨x, hxi, mem_of_mem_nhds hU⟩
        exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩)
    have hlocal := (hGfinite s) x hxR
    have heq : K ∩ U = (A ∪ ⋃ i ∈ s, P i) ∩ U := by
      apply Subset.antisymm
      · intro z hz
        rw [← hK] at hz
        rcases hz.1 with hzA | hzP
        · exact ⟨Or.inl hzA, hz.2⟩
        · obtain ⟨i, hzi⟩ := mem_iUnion.mp hzP
          have hi : i ∈ s := hfin.mem_toFinset.mpr ⟨z, hzi, hz.2⟩
          exact ⟨Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hzi⟩⟩), hz.2⟩
      · intro z hz
        have hzK : z ∈ K := by
          rw [← hK]
          rcases hz.1 with hzA | hzP
          · exact Or.inl hzA
          · obtain ⟨i, hzi⟩ := mem_iUnion.mp hzP
            obtain ⟨hi, hzi⟩ := mem_iUnion.mp hzi
            exact Or.inr (mem_iUnion.mpr ⟨i, hzi⟩)
        exact ⟨hzK, hz.2⟩
    have hlocal' := hlocal.inter_of_mem_nhds hU
    rw [← heq] at hlocal'
    exact hlocal'.of_inter_of_mem_nhds hU
  let H : F → E := Function.invFunOn G K
  have hHEqB : EqOn H (Function.invFunOn F₀ A) B := by
    intro y hy
    have hyY : y ∈ Y := hY ▸ Or.inl hy
    have hHy : H y ∈ K := hGbij.surjOn.mapsTo_invFunOn hyY
    have hFy : Function.invFunOn F₀ A y ∈ A :=
      hF.bijOn.surjOn.mapsTo_invFunOn hy
    apply hGinj hHy (hK ▸ Or.inl hFy)
    rw [hGbij.invOn_invFunOn.2 hyY, hGEqA hFy,
      hF.bijOn.invOn_invFunOn.2 hy]
  have hHEqQ : ∀ i, EqOn H (Function.invFunOn (f i) (P i)) (Q i) := by
    intro i y hy
    have hHy : H y ∈ K := hGbij.surjOn.mapsTo_invFunOn (hY ▸ Or.inr
      (mem_iUnion.mpr ⟨i, hy⟩))
    have hfy : Function.invFunOn (f i) (P i) y ∈ P i :=
      (hf i).bijOn.surjOn.mapsTo_invFunOn hy
    apply hGinj hHy (hK ▸ Or.inr (mem_iUnion.mpr ⟨i, hfy⟩))
    rw [hGbij.invOn_invFunOn.2 (hY ▸ Or.inr (mem_iUnion.mpr ⟨i, hy⟩)),
      hGEqP i hfy, (hf i).bijOn.invOn_invFunOn.2 hy]
  have hHfinite : ∀ s : Finset ι,
      IsPiecewiseAffineOn H (B ∪ ⋃ i ∈ s, Q i) := by
    intro s
    have hBaff : IsPiecewiseAffineOn H B :=
      hF.isPiecewiseAffineOn_invFunOn.congr hHEqB
    induction s using Finset.induction_on with
    | empty => simpa using hBaff
    | @insert i s hi ih =>
        have hpiece : IsPiecewiseAffineOn H (Q i) :=
          (hf i).isPiecewiseAffineOn_invFunOn.congr (hHEqQ i)
        have hrestc : IsClosed (B ∪ ⋃ j ∈ s, Q j) := by
          exact hB.union (isClosed_biUnion_finset fun j _ => hQclosed j)
        have hun := ih.union_of_isClosed hpiece hrestc (hQclosed i)
        simpa [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using hun
  have hHpl : IsPiecewiseAffineOn H Y := by
    intro y hy
    obtain ⟨U, hU, hfin⟩ := htargetLocal y hy
    let s : Finset ι := hfin.toFinset
    have hyR : y ∈ B ∪ ⋃ i ∈ s, Q i := by
      rw [← hY] at hy
      rcases hy with hyB | hyQ
      · exact Or.inl hyB
      · obtain ⟨i, hyi⟩ := mem_iUnion.mp hyQ
        have hi : i ∈ s := hfin.mem_toFinset.mpr ⟨y, hyi, mem_of_mem_nhds hU⟩
        exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hyi⟩⟩)
    have hlocal := (hHfinite s) y hyR
    have heq : Y ∩ U = (B ∪ ⋃ i ∈ s, Q i) ∩ U := by
      apply Subset.antisymm
      · intro z hz
        rw [← hY] at hz
        rcases hz.1 with hzB | hzQ
        · exact ⟨Or.inl hzB, hz.2⟩
        · obtain ⟨i, hzi⟩ := mem_iUnion.mp hzQ
          have hi : i ∈ s := hfin.mem_toFinset.mpr ⟨z, hzi, hz.2⟩
          exact ⟨Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hzi⟩⟩), hz.2⟩
      · intro z hz
        have hzY : z ∈ Y := by
          rw [← hY]
          rcases hz.1 with hzB | hzQ
          · exact Or.inl hzB
          · obtain ⟨i, hzi⟩ := mem_iUnion.mp hzQ
            obtain ⟨hi, hzi⟩ := mem_iUnion.mp hzi
            exact Or.inr (mem_iUnion.mpr ⟨i, hzi⟩)
        exact ⟨hzY, hz.2⟩
    have hlocal' := hlocal.inter_of_mem_nhds hU
    rw [← heq] at hlocal'
    exact hlocal'.of_inter_of_mem_nhds hU
  refine ⟨G, ⟨hGbij, hGpl, hHpl⟩, hGEqA, ?_⟩
  · intro i
    refine ⟨hGEqP i, ?_⟩
    calc
      G '' P i = f i '' P i := image_congr (hGEqP i)
      _ = Q i := (hf i).image_eq

end DifferentialGeometry.Topology.PiecewiseLinear
