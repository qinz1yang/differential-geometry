/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollarCoreShrinking

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem collar_shell_cover_and_inter {C S W : Set E3} {c : E3 × ℝ → E3}
    (hc : IsPLHomeomorphOn c (S ×ˢ Icc (0 : ℝ) 2) W) (hWC : W ⊆ C) :
    c '' (S ×ˢ Icc (0 : ℝ) 1) ∪ (C \ c '' (S ×ˢ Ico (0 : ℝ) 1)) = C ∧
      c '' (S ×ˢ Icc (0 : ℝ) 1) ∩ (C \ c '' (S ×ˢ Ico (0 : ℝ) 1)) =
        c '' (S ×ˢ {(1 : ℝ)}) := by
  have hsub : S ×ˢ Icc (0 : ℝ) 1 ⊆ S ×ˢ Icc (0 : ℝ) 2 :=
    prod_mono subset_rfl (fun _ ht => ⟨ht.1, ht.2.trans (by norm_num)⟩)
  have hcut : S ×ˢ Ico (0 : ℝ) 1 ⊆ S ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono subset_rfl Ico_subset_Icc_self
  constructor
  · apply Subset.antisymm
    · exact union_subset ((image_mono hsub).trans (hc.image_eq.subset.trans hWC))
        sdiff_subset
    · intro y hy
      by_cases hys : y ∈ c '' (S ×ˢ Ico (0 : ℝ) 1)
      · exact Or.inl (image_mono hcut hys)
      · exact Or.inr ⟨hy, hys⟩
  · apply Subset.antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, -, hnot⟩
      have ht : z.2 = 1 := by
        apply le_antisymm hz.2.2
        by_contra h
        exact hnot ⟨z, ⟨hz.1, hz.2.1, lt_of_not_ge h⟩, rfl⟩
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      have hz1 : z.2 = 1 := hz.2
      have hzS : z ∈ S ×ˢ Icc (0 : ℝ) 1 := ⟨hz.1, by rw [hz1]; norm_num⟩
      refine ⟨⟨z, hzS, rfl⟩, hWC (hc.bijOn.mapsTo (hsub hzS)), ?_⟩
      rintro ⟨w, hw, hwz⟩
      have h := congrArg Prod.snd (hc.bijOn.injOn (hsub (hcut hw)) (hsub hzS) hwz)
      linarith [hw.2.2]

theorem exists_isPLHomeomorphOn_eq_on_collars
    {C D W Z : Set E3} (hC : IsPLBall 3 C) (hD : IsPLBall 3 D)
    {c d : E3 × ℝ → E3}
    (hc : IsPLHomeomorphOn c (frontier C ×ˢ Icc (0 : ℝ) 2) W)
    (hd : IsPLHomeomorphOn d (frontier D ×ˢ Icc (0 : ℝ) 2) Z)
    (hWC : W ⊆ C) (hZD : Z ⊆ D)
    (hc0 : ∀ x ∈ frontier C, c (x, 0) = x)
    (hd0 : ∀ y ∈ frontier D, d (y, 0) = y)
    {b : E3 → E3} (hb : IsPLHomeomorphOn b (frontier C) (frontier D)) :
    ∃ F : E3 → E3, IsPLHomeomorphOn F C D ∧ EqOn F b (frontier C) ∧
      ∀ x ∈ frontier C, ∀ t ∈ Icc (0 : ℝ) 1, F (c (x, t)) = d (b x, t) := by
  classical
  obtain ⟨-, -, hCcore, hCfront, -, -⟩ :=
    hC.exists_isPLHomeomorphOn_collar_core (by simp) hc hWC hc0
  obtain ⟨-, -, hDcore, hDfront, -, -⟩ :=
    hD.exists_isPLHomeomorphOn_collar_core (by simp) hd hZD hd0
  let P := c '' (frontier C ×ˢ Icc (0 : ℝ) 1)
  let Q := d '' (frontier D ×ˢ Icc (0 : ℝ) 1)
  let K := C \ c '' (frontier C ×ˢ Ico (0 : ℝ) 1)
  let L := D \ d '' (frontier D ×ˢ Ico (0 : ℝ) 1)
  have hCbd := hC.isPLSphere_frontier.isPolyhedron
  have hDbd := hD.isPLSphere_frontier.isPolyhedron
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 2 :=
    fun _ ht => ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hcP := hc.restrict (hCbd.prod isHPolytope_Icc.isPolyhedron)
    (prod_mono subset_rfl hsub)
  have hdQ := hd.restrict (hDbd.prod isHPolytope_Icc.isPolyhedron)
    (prod_mono subset_rfl hsub)
  let f := d ∘ Prod.map b id ∘ Function.invFunOn c (frontier C ×ˢ Icc (0 : ℝ) 1)
  have hf : IsPLHomeomorphOn f P Q := hcP.symm.trans
    ((hb.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hdQ)
  have hfc : ∀ x ∈ frontier C, ∀ t ∈ Icc (0 : ℝ) 1,
      f (c (x, t)) = d (b x, t) := by
    intro x hx t ht
    change d (Prod.map b id
      (Function.invFunOn c (frontier C ×ˢ Icc (0 : ℝ) 1) (c (x, t)))) = _
    rw [hcP.bijOn.invOn_invFunOn.1
      (show (x, t) ∈ frontier C ×ˢ Icc (0 : ℝ) 1 from ⟨hx, ht⟩)]
    rfl
  have hP : IsPolyhedron P :=
    (hCbd.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hcP.isPiecewiseAffineOn hcP.bijOn.injOn
  obtain ⟨hcoverC, hmeetC⟩ := collar_shell_cover_and_inter hc hWC
  obtain ⟨hcoverD, hmeetD⟩ := collar_shell_cover_and_inter hd hZD
  have hKfrontP : frontier K ⊆ P := by
    rw [hCfront]
    exact image_mono (prod_mono subset_rfl (singleton_subset_iff.mpr (by norm_num)))
  have hfrontmap : f '' frontier K = frontier L := by
    rw [hCfront, hDfront]
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, rfl⟩
      have ht1 : t = 1 := ht
      subst t
      exact ⟨(b x, 1), ⟨hb.bijOn.mapsTo hx, rfl⟩,
        (hfc x hx 1 (by norm_num)).symm⟩
    · rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      have ht1 : t = 1 := ht
      subst t
      obtain ⟨x, hx, rfl⟩ := hb.bijOn.surjOn hy
      exact ⟨c (x, 1), ⟨(x, 1), ⟨hx, rfl⟩, rfl⟩, hfc x hx 1 (by norm_num)⟩
  have hfbd : IsPLHomeomorphOn f (frontier K) (frontier L) := by
    rw [← hfrontmap]
    exact hf.restrict hCcore.isPLSphere_frontier.isPolyhedron hKfrontP
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_frontier hCcore hDcore hfbd
  have heq : EqOn f G (P ∩ K) := by
    intro y hy
    exact (hGf (hCfront.symm.subset (hmeetC.subset hy))).symm
  have him : f '' (P ∩ K) = Q ∩ L := by
    rw [show P ∩ K = frontier K from hmeetC.trans hCfront.symm,
      hfrontmap, hDfront]
    exact hmeetD.symm
  have hF := hf.piecewise hG hP hCcore.isPolyhedron heq him
  rw [hcoverC, hcoverD] at hF
  have hFc : ∀ x ∈ frontier C, ∀ t ∈ Icc (0 : ℝ) 1,
      P.piecewise f G (c (x, t)) = d (b x, t) := by
    intro x hx t ht
    rw [P.piecewise_eq_of_mem f G (show c (x, t) ∈ P from ⟨(x, t), ⟨hx, ht⟩, rfl⟩)]
    exact hfc x hx t ht
  refine ⟨P.piecewise f G, hF, ?_, hFc⟩
  intro x hx
  have h := hFc x hx 0 (by norm_num)
  rwa [hc0 x hx, hd0 (b x) (hb.bijOn.mapsTo hx)] at h

end DifferentialGeometry.Topology.PiecewiseLinear
