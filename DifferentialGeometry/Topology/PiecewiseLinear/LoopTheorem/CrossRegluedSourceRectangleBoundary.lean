/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def rect (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)

private def horizontal (a b t : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' (Icc a b ×ˢ {t})

private theorem mem_rect {a b : ℝ} {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ rect a b ↔ (seamWitnessPlane.symm z).1 ∈ Icc a b ∧
      (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1 := mem_image_seamWitnessPlane

private theorem mem_horizontal {a b t : ℝ} {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ horizontal a b t ↔ (seamWitnessPlane.symm z).1 ∈ Icc a b ∧
      (seamWitnessPlane.symm z).2 = t := mem_image_seamWitnessPlane

private theorem isArcBetween_horizontal {a b : ℝ} (hab : a < b) (t : ℝ) :
    Schoenflies.IsArcBetween (horizontal a b t)
      (seamWitnessPlane (a, t)) (seamWitnessPlane (b, t)) := by
  refine ⟨fun r => seamWitnessPlane (a + (b - a) * r, t),
    (seamWitnessPlane.continuous.comp
      ((continuous_const.add (continuous_const.mul continuous_id)).prodMk
        continuous_const)).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro u _ v _ huv
    have := congrArg Prod.fst (seamWitnessPlane.injective huv)
    dsimp at this
    nlinarith
  · apply Subset.antisymm
    · rintro z ⟨r, hr, rfl⟩
      refine ⟨(a + (b - a) * r, t), ⟨⟨?_, ?_⟩, rfl⟩, rfl⟩ <;>
        nlinarith [hr.1, hr.2]
    · rintro z ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩
      have hs' : s = t := hs
      subst s
      refine ⟨(r - a) / (b - a), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr hab).le
      · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hr.2])
      · change seamWitnessPlane (a + (b - a) * ((r - a) / (b - a)), t) = _
        apply congrArg seamWitnessPlane
        apply Prod.ext
        · field_simp [(sub_pos.mpr hab).ne']
          ring
        · rfl
  · simp
  · change seamWitnessPlane (a + (b - a) * 1, t) = seamWitnessPlane (b, t)
    apply congrArg seamWitnessPlane
    exact Prod.ext (by ring) rfl

theorem exists_boundaryParam_four_paths_of_rectangle {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ (p q u v : frontier (seamWitnessPlane '' (Icc a d ×ˢ Icc (0 : ℝ) 1)))
      (σ : Path p q) (τ : Path q u) (υ : Path u v) (φ : Path v p)
      (e : loopCircle ≃ₜ frontier (seamWitnessPlane '' (Icc a d ×ˢ Icc (0 : ℝ) 1))),
      (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (b, 0) ∧
      (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (b, 1) ∧
      (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (c, 1) ∧
      (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (c, 0) ∧
      Set.range (fun t => (σ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)) ∩
          frontier (seamWitnessPlane '' (Icc a d ×ˢ Icc (0 : ℝ) 1)) ∧
      Set.range (fun t => (τ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc b c ×ˢ {(1 : ℝ)})) ∧
      Set.range (fun t => (υ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc c d ×ˢ Icc (0 : ℝ) 1)) ∩
          frontier (seamWitnessPlane '' (Icc a d ×ˢ Icc (0 : ℝ) 1)) ∧
      Set.range (fun t => (φ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc b c ×ˢ {(0 : ℝ)})) ∧
      (∀ θ, e θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
      Function.Injective σ ∧ Function.Injective τ ∧
      Function.Injective υ ∧ Function.Injective φ := by
  have hleft := (isCutPair_seamWitnessPlane_rectangle_traces
    hab (hbc.trans hcd)).2.1.snd
  have hright := (isCutPair_seamWitnessPlane_rectangle_traces
    (hab.trans hbc) hcd).2.2.2.snd.reverse
  have hthree : ∀ z ∈ rect c d ∩ frontier (rect a d),
      z ∈ horizontal b c 0 → z = seamWitnessPlane (c, 0) := by
    intro z hz hbot
    have h₁ := mem_rect.mp hz.1
    have h₂ := mem_horizontal.mp hbot
    apply seamWitnessPlane.symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact Prod.ext (by linarith [h₁.1.1, h₂.1.2]) h₂.2
  have htwo : ∀ z ∈ horizontal b c 1,
      z ∈ (rect c d ∩ frontier (rect a d)) ∪
        horizontal b c 0 → z = seamWitnessPlane (c, 1) := by
    intro z hz hz'
    have h₂ := mem_horizontal.mp hz
    rcases hz' with hz' | hz'
    · have h₃ := mem_rect.mp hz'.1
      apply seamWitnessPlane.symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext (by linarith [h₂.1.2, h₃.1.1]) h₂.2
    · have h₄ := mem_horizontal.mp hz'
      exact (by linarith [h₂.2, h₄.2] : False).elim
  have hone : ∀ z ∈ rect a b ∩ frontier (rect a d),
      z ∈ horizontal b c 1 ∪
        ((rect c d ∩ frontier (rect a d)) ∪
          horizontal b c 0) →
        z = seamWitnessPlane (b, 0) ∨ z = seamWitnessPlane (b, 1) := by
    intro z hz hz'
    have h₁ := mem_rect.mp hz.1
    rcases hz' with hz' | hz' | hz'
    · have h₂ := mem_horizontal.mp hz'
      right
      apply seamWitnessPlane.symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext (by linarith [h₁.1.2, h₂.1.1]) h₂.2
    · have h₃ := mem_rect.mp hz'.1
      exact (by linarith [h₁.1.2, h₃.1.1] : False).elim
    · have h₄ := mem_horizontal.mp hz'
      left
      apply seamWitnessPlane.symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext (by linarith [h₁.1.2, h₄.1.1]) h₄.2
  have hfront : frontier (rect a d) =
      (rect a b ∩ frontier (rect a d)) ∪
        (horizontal b c 1 ∪
          ((rect c d ∩ frontier (rect a d)) ∪
            horizontal b c 0)) := by
    ext z
    have hfrontz : z ∈ frontier (rect a d) ↔
        ((seamWitnessPlane.symm z).1 ∈ Icc a d ∧
          ((seamWitnessPlane.symm z).2 = 0 ∨ (seamWitnessPlane.symm z).2 = 1)) ∨
        (((seamWitnessPlane.symm z).1 = a ∨ (seamWitnessPlane.symm z).1 = d) ∧
          (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1) :=
      mem_frontier_seamWitnessPlane_image_Icc_prod (by linarith)
    simp only [mem_union, mem_inter_iff, mem_rect, mem_horizontal, hfrontz,
      mem_Icc]
    constructor
    · rintro (⟨hs, ht | ht⟩ | ⟨hs | hs, ht⟩)
      · by_cases h : (seamWitnessPlane.symm z).1 ≤ b
        · exact Or.inl ⟨⟨⟨hs.1, h⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inl ht⟩⟩
        · by_cases h' : c ≤ (seamWitnessPlane.symm z).1
          · exact Or.inr (Or.inr (Or.inl
              ⟨⟨⟨h', hs.2⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inl ht⟩⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨⟨by linarith, by linarith⟩, ht⟩))
      · by_cases h : (seamWitnessPlane.symm z).1 ≤ b
        · exact Or.inl ⟨⟨⟨hs.1, h⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inr ht⟩⟩
        · by_cases h' : c ≤ (seamWitnessPlane.symm z).1
          · exact Or.inr (Or.inr (Or.inl
              ⟨⟨⟨h', hs.2⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inr ht⟩⟩))
          · exact Or.inr (Or.inl ⟨⟨by linarith, by linarith⟩, ht⟩)
      · exact Or.inl ⟨⟨by rw [hs]; constructor <;> linarith, ht⟩, Or.inr ⟨Or.inl hs, ht⟩⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨⟨by rw [hs]; constructor <;> linarith, ht⟩, Or.inr ⟨Or.inr hs, ht⟩⟩))
    · rintro (⟨-, h⟩ | ⟨hs, ht⟩ | ⟨-, h⟩ | ⟨hs, ht⟩)
      · exact h
      · exact Or.inl ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, Or.inr ht⟩
      · exact h
      · exact Or.inl ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, Or.inl ht⟩
  obtain ⟨p, q, u, v, σ, τ, υ, φ, e, hbody, hinj⟩ :=
    exists_injective_boundaryParam_four_paths hleft (isArcBetween_horizontal hbc 1)
      hright (isArcBetween_horizontal hbc 0).reverse hthree htwo hone hfront
  exact ⟨p, q, u, v, σ, τ, υ, φ, e, hbody.1, hbody.2.1, hbody.2.2.1,
    hbody.2.2.2.1, hbody.2.2.2.2.1, hbody.2.2.2.2.2.1,
    hbody.2.2.2.2.2.2.1, hbody.2.2.2.2.2.2.2.1, hbody.2.2.2.2.2.2.2.2, hinj⟩

end DifferentialGeometry.Topology.PiecewiseLinear
