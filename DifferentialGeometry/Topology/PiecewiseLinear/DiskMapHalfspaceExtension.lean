/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundaryExtension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_isPLHomeomorphOn_extension_halfspaces {P : Set Plane} (hP : IsPLBall 2 P)
    {u : Plane → Plane} (hu : IsPLHomeomorphOn u P P) (hfix : EqOn u id (frontier P)) :
    ∃ Φ : (Plane × ℝ) ≃ₜ (Plane × ℝ), IsPLHomeomorphOn Φ univ univ ∧
      (∀ x ∈ P, Φ (x, 0) = (u x, 0)) ∧ EqOn Φ id (P ×ˢ Icc (-1 : ℝ) 1)ᶜ ∧
      (∀ z, 0 ≤ (Φ z).2 ↔ 0 ≤ z.2) ∧ (∀ z, (Φ z).2 = 0 ↔ z.2 = 0) := by
  classical
  obtain ⟨q, hq⟩ := id hP
  obtain ⟨F, hF, hF0, hFfix⟩ := exists_isPLHomeomorphOn_prism_eqOn_top_and_side hq hu
    (hq.image_stdSimplexBoundary.symm ▸ hfix)
  rw [hq.image_stdSimplexBoundary] at hFfix
  let R : Plane × ℝ →ᵃ[ℝ] Plane × ℝ :=
    ((LinearMap.fst ℝ Plane ℝ).prod (-(LinearMap.snd ℝ Plane ℝ))).toAffineMap
  have hRapp : ∀ z, R z = (z.1, -z.2) := fun _ => rfl
  have hRR : Function.Involutive R := fun z => by simp only [hRapp, neg_neg]
  have hR : ∀ a b : ℝ, IsPLHomeomorphOn R (P ×ˢ Icc a b) (P ×ˢ Icc (-b) (-a)) := by
    intro a b
    have hp : IsPolyhedron (P ×ˢ Icc a b) := hP.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hp
      ((isPiecewiseAffineOn_of_affine R isOpen_univ).mono_of_isPolyhedron hp (subset_univ _))
      ⟨?_, hRR.injective.injOn, ?_⟩
    · rintro z ⟨hzP, hzlo, hzhi⟩
      exact ⟨hzP, neg_le_neg hzhi, neg_le_neg hzlo⟩
    · rintro z ⟨hzP, hzlo, hzhi⟩
      refine ⟨R z, ⟨hzP, ?_, ?_⟩, hRR z⟩
      · change a ≤ -z.2
        linarith
      · change -z.2 ≤ b
        linarith
  have hRm : IsPLHomeomorphOn R (P ×ˢ Icc (-1 : ℝ) 0) (P ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [neg_zero, neg_neg] using hR (-1) 0
  have hRp : IsPLHomeomorphOn R (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (-1 : ℝ) 0) := by
    simpa only [neg_zero] using hR 0 1
  let G := R ∘ F ∘ R
  have hG : IsPLHomeomorphOn G (P ×ˢ Icc (-1 : ℝ) 0) (P ×ˢ Icc (-1 : ℝ) 0) :=
    (hRm.trans hF).trans hRp
  have hG0 : ∀ x ∈ P, G (x, 0) = (u x, 0) := by
    intro x hx
    simp only [G, Function.comp_apply, hRapp, neg_zero, hF0 x hx]
  have hinter : (P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1) =
      P ×ˢ ({0} : Set ℝ) := by
    ext z
    simp only [mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx, _, ht⟩, _, ht', _⟩
      exact ⟨hx, le_antisymm ht ht'⟩
    · rintro ⟨hx, ht⟩
      rw [ht]
      exact ⟨⟨hx, by norm_num, le_rfl⟩, hx, le_rfl, by norm_num⟩
  have hagree : EqOn G F ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1)) := by
    rw [hinter]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact (hG0 x hx).trans (hF0 x hx).symm
  have hsurj : SurjOn G ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1))
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1)) := by
    rw [hinter]
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have ht0 : t = 0 := ht
    subst t
    obtain ⟨x, hx, hxy⟩ := hu.bijOn.surjOn hy
    exact ⟨(x, 0), ⟨hx, rfl⟩, (hG0 x hx).trans (by rw [hxy])⟩
  have hm : IsPolyhedron (P ×ˢ Icc (-1 : ℝ) 0) :=
    hP.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have hp : IsPolyhedron (P ×ˢ Icc (0 : ℝ) 1) :=
    hP.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  obtain ⟨H, hH, hHG, hHF⟩ := exists_isPLHomeomorphOn_union hm hp hG hF hagree hsurj
  have hunion : (P ×ˢ Icc (-1 : ℝ) 0) ∪ (P ×ˢ Icc (0 : ℝ) 1) =
      P ×ˢ Icc (-1 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  rw [hunion] at hH
  have hH0 : ∀ x ∈ P, H (x, 0) = (u x, 0) := fun x hx =>
    (hHF ⟨hx, by norm_num⟩).trans (hF0 x hx)
  have hHfix : EqOn H id (frontier (P ×ˢ Icc (-1 : ℝ) 1)) := by
    rw [frontier_prod_eq, hP.isPolyhedron.isClosed.closure_eq,
      isClosed_Icc.closure_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    rintro ⟨x, t⟩ (⟨hx, ht | ht⟩ | ⟨hx, ht⟩)
    · have ht1 : t = -1 := ht
      subst t
      rw [hHG ⟨hx, by norm_num⟩]
      change R (F (R (x, -1))) = (x, -1)
      have hR1 : R (x, -1) = (x, 1) := Prod.ext rfl (by change -(-1 : ℝ) = 1; norm_num)
      rw [hR1, hFfix (show (x, (1 : ℝ)) ∈
        P ×ˢ {1} ∪ frontier P ×ˢ Icc (0 : ℝ) 1 from Or.inl ⟨hx, rfl⟩), id_eq, hRapp]
    · have ht1 : t = 1 := ht
      subst t
      exact (hHF ⟨hx, by norm_num⟩).trans (hFfix (Or.inl ⟨hx, rfl⟩))
    · have hxP := hP.isPolyhedron.isClosed.frontier_subset hx
      by_cases ht0 : 0 ≤ t
      · exact (hHF ⟨hxP, ht0, ht.2⟩).trans (hFfix (Or.inr ⟨hx, ht0, ht.2⟩))
      · rw [hHG ⟨hxP, ht.1, le_of_lt (lt_of_not_ge ht0)⟩]
        change R (F (R (x, t))) = (x, t)
        have hRt : (R (x, t)).2 ∈ Icc (0 : ℝ) 1 := by
          change 0 ≤ -t ∧ -t ≤ 1
          constructor <;> linarith [ht.1]
        have hfixR : F (R (x, t)) = R (x, t) := hFfix
          (show R (x, t) ∈ P ×ˢ {1} ∪ frontier P ×ˢ Icc (0 : ℝ) 1 from
            Or.inr ⟨hx, hRt⟩)
        rw [hfixR, hRR]
  have hbox : IsPolyhedron (P ×ˢ Icc (-1 : ℝ) 1) :=
    hP.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  obtain ⟨Φ, hΦ, hΦH, hΦfix⟩ := hH.exists_extension_of_eqOn_frontier hbox hHfix
  have hΦ0 : ∀ x ∈ P, Φ (x, 0) = (u x, 0) := fun x hx =>
    (hΦH ⟨hx, by norm_num⟩).trans (hH0 x hx)
  have hmid : ∀ z, (Φ z).2 = 0 ↔ z.2 = 0 := by
    intro z
    by_cases hz : z ∈ P ×ˢ Icc (-1 : ℝ) 1
    · have hzmap := hH.bijOn.mapsTo hz
      rw [← hΦH hz] at hzmap
      constructor
      · intro ht
        obtain ⟨x, hx, hux⟩ := hu.bijOn.surjOn hzmap.1
        have heq : Φ (x, 0) = Φ z := by rw [hΦ0 x hx, hux]; exact Prod.ext rfl ht.symm
        exact (congrArg Prod.snd (Φ.injective heq)).symm
      · intro ht
        have heq : z = (z.1, 0) := Prod.ext rfl ht
        rw [heq, hΦ0 z.1 hz.1]
    · rw [hΦfix hz]
      rfl
  refine ⟨Φ, hΦ, hΦ0, hΦfix, ?_, hmid⟩
  intro z
  by_cases hz : z ∈ P ×ˢ Icc (-1 : ℝ) 1
  · by_cases ht : 0 ≤ z.2
    · have hzplus : z ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hz.1, ht, hz.2.2⟩
      have heq := (hΦH hz).trans (hHF hzplus)
      exact iff_of_true (heq.symm ▸ (hF.bijOn.mapsTo hzplus).2.1) ht
    · have hzminus : z ∈ P ×ˢ Icc (-1 : ℝ) 0 := ⟨hz.1, hz.2.1, le_of_not_ge ht⟩
      have heq := (hΦH hz).trans (hHG hzminus)
      have hle : (Φ z).2 ≤ 0 := heq.symm ▸ (hG.bijOn.mapsTo hzminus).2.2
      have hne : (Φ z).2 ≠ 0 := fun h => ht (le_of_eq ((hmid z).mp h).symm)
      exact iff_of_false (not_le_of_gt (lt_of_le_of_ne hle hne)) ht
  · rw [hΦfix hz]
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
