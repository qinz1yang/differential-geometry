/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.AffinePeriodic
import DifferentialGeometry.Topology.LoopSpace.CircleLiftOrientation

/-! Isotopies of oriented circle homeomorphisms and relative cylinder extension. -/

open Set

namespace DifferentialGeometry.Topology

theorem exists_isotopy_circle_of_hasIncreasingCircleLift (ψ : loopCircle ≃ₜ loopCircle)
    (hψ : HasIncreasingCircleLift ψ) :
    ∃ H : unitInterval → loopCircle ≃ₜ loopCircle,
      Continuous (fun p : unitInterval × loopCircle => H p.1 p.2) ∧
      Continuous (fun p : unitInterval × loopCircle => (H p.1).symm p.2) ∧
      H 0 = Homeomorph.refl loopCircle ∧ H 1 = ψ := by
  have hlift : ∃ F : ℝ ≃ₜ ℝ, StrictMono F ∧ (∀ x, F (x + 1) = F x + 1) ∧
      ∀ x : ℝ, ψ (x : loopCircle) = (F x : loopCircle) := by
    rcases circleHomeomorph_affineLift_or_neg ψ with ⟨F, hp, hm, he⟩ | ⟨F, hp, hm, he⟩
    · exact ⟨F, hm, hp, fun x => he (x : loopCircle)⟩
    · exfalso
      apply not_hasIncreasingCircleLift_of_neg_lift hm hp ?_ hψ
      intro x
      rw [he, affineCircleMap_coe, QuotientAddGroup.mk_neg]
  obtain ⟨F, hFm, hFp, hFl⟩ := hlift
  let u (t : unitInterval) (x : ℝ) : ℝ := (1 - (t : ℝ)) * x + (t : ℝ) * F x
  have hup (t : unitInterval) (x : ℝ) : u t (x + 1) = u t x + 1 := by
    dsimp [u]
    rw [hFp]
    ring
  have huc (t : unitInterval) : Continuous (u t) :=
    (continuous_const.mul continuous_id).add (continuous_const.mul F.continuous)
  have hex (t : unitInterval) : ∃ G : ℝ ≃ₜ ℝ, ∀ x, G x = u t x := by
    by_cases ht : (t : ℝ) = 1
    · exact ⟨F, fun x => by simp [u, ht]⟩
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    obtain ⟨G, _, hG, _⟩ := Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope
      (huc t) (hup t) (sub_pos.mpr ht1) (by
        intro x y hxy
        have h := mul_nonneg t.property.1 (sub_nonneg.mpr (hFm.monotone hxy))
        dsimp [u]
        nlinarith)
    exact ⟨G, hG⟩
  choose G hG using hex
  have hGp (t : unitInterval) (x : ℝ) : G t (x + 1) = G t x + 1 := by
    rw [hG, hG, hup]
  let H (t : unitInterval) : loopCircle ≃ₜ loopCircle := affineCircleHomeomorph (G t) (hGp t)
  have hHval (t : unitInterval) (x : ℝ) : H t (x : loopCircle) = (u t x : loopCircle) := by
    change affineCircleMap (G t) (G t).continuous (hGp t) (x : loopCircle) = _
    rw [affineCircleMap_coe, hG]
  have hcont : Continuous (fun p : unitInterval × loopCircle => H p.1 p.2) := by
    have hq := (_root_.IsOpenQuotientMap.id (X := unitInterval)).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
    apply hq.isQuotientMap.continuous_iff.mpr
    have hcu : Continuous (fun p : unitInterval × ℝ => u p.1 p.2) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).mul (F.continuous.comp continuous_snd))
    convert (AddCircle.continuous_mk' (1 : ℝ)).comp hcu using 1
    funext p
    exact hHval p.1 p.2
  let A : unitInterval × loopCircle → unitInterval × loopCircle :=
    fun p => (p.1, H p.1 p.2)
  have hAc : Continuous A := continuous_fst.prodMk hcont
  have hAb : Function.Bijective A := by
    constructor
    · rintro ⟨s, x⟩ ⟨t, y⟩ h
      have hst : s = t := congrArg Prod.fst h
      subst t
      exact Prod.ext rfl ((H s).injective (congrArg Prod.snd h))
    · rintro ⟨t, y⟩
      exact ⟨(t, (H t).symm y), Prod.ext rfl ((H t).apply_symm_apply y)⟩
  let E : (unitInterval × loopCircle) ≃ₜ (unitInterval × loopCircle) :=
    hAc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective A hAb)
  have hfirst (p : unitInterval × loopCircle) : (E.symm p).1 = p.1 := by
    have h := congrArg (fun q : unitInterval × loopCircle => q.1) (E.apply_symm_apply p)
    exact h
  have hinv (p : unitInterval × loopCircle) : (E.symm p).2 = (H p.1).symm p.2 := by
    apply (H p.1).injective
    rw [(H p.1).apply_symm_apply]
    have he := congrArg Prod.snd (E.apply_symm_apply p)
    change H (E.symm p).1 (E.symm p).2 = p.2 at he
    rwa [hfirst] at he
  refine ⟨H, hcont, (E.symm.continuous.snd).congr hinv, ?_, ?_⟩
  · ext θ
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [hHval]
    simp [u]
  · ext θ
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [hHval, hFl]
    simp [u]

theorem exists_homeomorph_cylinder_of_same_orientation
    (φ ψ : loopCircle ≃ₜ loopCircle)
    (hor : HasIncreasingCircleLift φ ↔ HasIncreasingCircleLift ψ) :
    ∃ E : (unitInterval × loopCircle) ≃ₜ (unitInterval × loopCircle),
      (∀ p, (E p).1 = p.1) ∧ (∀ θ, E (0, θ) = (0, φ θ)) ∧
      ∀ θ, E (1, θ) = (1, ψ θ) := by
  have hrel : HasIncreasingCircleLift (φ.symm.trans ψ) := by
    by_cases hφ : HasIncreasingCircleLift φ
    · exact (hor.mp hφ).comp (hφ.inv φ.surjective φ.symm_apply_apply)
    · have hψ : ¬ HasIncreasingCircleLift ψ := fun h => hφ (hor.mpr h)
      have hφi : ¬ HasIncreasingCircleLift φ.symm := fun h =>
        hφ (h.inv φ.symm.surjective φ.apply_symm_apply)
      exact hasIncreasingCircleLift_comp_of_not_hasIncreasingCircleLift ψ φ.symm hψ hφi
  obtain ⟨H, hH, hHi, hH0, hH1⟩ :=
    exists_isotopy_circle_of_hasIncreasingCircleLift (φ.symm.trans ψ) hrel
  let E : (unitInterval × loopCircle) ≃ₜ (unitInterval × loopCircle) := {
    toFun p := (p.1, H p.1 (φ p.2))
    invFun p := (p.1, φ.symm ((H p.1).symm p.2))
    left_inv p := by simp
    right_inv p := by simp
    continuous_toFun := continuous_fst.prodMk
      (hH.comp (continuous_fst.prodMk (φ.continuous.comp continuous_snd)))
    continuous_invFun := continuous_fst.prodMk (φ.symm.continuous.comp hHi) }
  refine ⟨E, fun _ => rfl, ?_, ?_⟩
  · intro θ
    change (0, H 0 (φ θ)) = (0, φ θ)
    simp only [hH0, Homeomorph.refl_apply, id_eq]
  · intro θ
    change (1, H 1 (φ θ)) = (1, ψ θ)
    rw [hH1, Homeomorph.trans_apply, φ.symm_apply_apply]

end DifferentialGeometry.Topology
