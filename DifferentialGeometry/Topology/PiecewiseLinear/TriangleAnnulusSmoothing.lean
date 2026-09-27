/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCornerSmoothing

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem standardTriangleBoundary_eq_image :
    standardTriangleBoundary =
      (fun p : Fin 3 → ℝ => (p 2 - p 1, p 1 + p 2)) '' stdSimplexBoundary 2 := by
  apply Subset.antisymm
  · intro p hp
    let w : Fin 3 → ℝ := ![1 - p.2, (p.2 - p.1) / 2, (p.2 + p.1) / 2]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hp
    refine ⟨w, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro i
      fin_cases i <;> norm_num [w] <;> linarith
    · change ∑ i, w i = 1
      rw [Fin.sum_univ_three]
      change (1 - p.2) + (p.2 - p.1) / 2 + (p.2 + p.1) / 2 = 1
      ring
    · rcases h₄ with h | h | h
      · refine ⟨1, ?_⟩
        change (p.2 - p.1) / 2 = 0
        rw [h, sub_self, zero_div]
      · refine ⟨2, ?_⟩
        change (p.2 + p.1) / 2 = 0
        rw [h, neg_add_cancel, zero_div]
      · refine ⟨0, ?_⟩
        change 1 - p.2 = 0
        rw [h, sub_self]
    · change ((p.2 + p.1) / 2 - (p.2 - p.1) / 2,
        (p.2 - p.1) / 2 + (p.2 + p.1) / 2) = p
      apply Prod.ext <;> dsimp <;> ring
  · rintro _ ⟨w, ⟨hw, i, hi⟩, rfl⟩
    have h₀ := hw.1 0
    have h₁ := hw.1 1
    have h₂ := hw.1 2
    have hsum : w 0 + w 1 + w 2 = 1 := by
      have hh : (∑ i : Fin 3, w i) = 1 := hw.2
      rwa [Fin.sum_univ_three] at hh
    change w 2 - w 1 ≤ w 1 + w 2 ∧ -(w 2 - w 1) ≤ w 1 + w 2 ∧
      w 1 + w 2 ≤ 1 ∧ (w 1 + w 2 = w 2 - w 1 ∨
        w 1 + w 2 = -(w 2 - w 1) ∨ w 1 + w 2 = 1)
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    fin_cases i
    · change w 0 = 0 at hi
      exact Or.inr (Or.inr (by linarith))
    · change w 1 = 0 at hi
      exact Or.inl (by linarith)
    · change w 2 = 0 at hi
      exact Or.inr (Or.inl (by linarith))

theorem exists_isotopy_smoothing_triangle_annulus {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 8) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ K : ℝ → ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ),
        Continuous (fun q : ℝ × ((ℝ × ℝ) × ℝ) => K q.1 q.2) ∧
        Continuous (fun q : ℝ × ((ℝ × ℝ) × ℝ) => (K q.1).symm q.2) ∧
        K 0 = Homeomorph.refl ((ℝ × ℝ) × ℝ) ∧
        (∀ t p, (K t p).2 = p.2) ∧
        (∀ t, EqOn (K t) id
          ((⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η) ×ˢ
            ball (1 / 2 : ℝ) 1)ᶜ) ∧
        (∃ J : Set ((ℝ × ℝ) × ℝ), IsCompact J ∧
          ∀ t, EqOn (K t) id Jᶜ ∧ EqOn (K t).symm id Jᶜ) ∧
        ∃ d : Fin 3 → ((ℝ × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × ℝ),
          (∀ i p, d i p =
            ((triangleVertexChart i).symm
              (p.1.1, Real.smoothAbs δ p.1.1 + p.1.2), p.2)) ∧
          (∀ i : Fin 3, ∀ p : ℝ × ℝ, ∀ z ∈ Icc (0 : ℝ) 1,
            |p.2| ≤ η / 8 → cornerShear p ∈ ball (0 : ℝ × ℝ) (2 * η) →
            K 1 ((triangleVertexChart i).symm (cornerShear p), z) = d i (p, z)) ∧
          ∀ p ∈ K 1 '' (standardTriangleBoundary ×ˢ Icc (0 : ℝ) 1),
            ∃ e : ((ℝ × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × ℝ),
              (∀ q, (e q).2 = q.2) ∧ ∃ V : Set ((ℝ × ℝ) × ℝ),
                IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V,
                  (q ∈ K 1 '' (standardTriangleBoundary ×ˢ Icc (0 : ℝ) 1) ↔
                    (e q).1.2 = 0 ∧ (e q).2 ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨δ, hδ, hδη, G, hG, hGi, hG0, hfix, d, hd, hframe, hcharts⟩ :=
    exists_isotopy_smoothing_triangle_boundary hη hηsmall
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hK : Continuous (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
      (G (q.1 * b q.2.2) q.2.1, q.2.2)) :=
    (hG.comp ((continuous_fst.mul (b.continuous.comp continuous_snd.snd)).prodMk
      continuous_snd.fst)).prodMk continuous_snd.snd
  have hKi : Continuous (fun q : ℝ × ((ℝ × ℝ) × ℝ) =>
      ((G (q.1 * b q.2.2)).symm q.2.1, q.2.2)) :=
    (hGi.comp ((continuous_fst.mul (b.continuous.comp continuous_snd.snd)).prodMk
      continuous_snd.fst)).prodMk continuous_snd.snd
  let K (t : ℝ) : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) :=
    { toFun := fun p => (G (t * b p.2) p.1, p.2)
      invFun := fun p => ((G (t * b p.2)).symm p.1, p.2)
      left_inv := fun _ => by simp only [Homeomorph.symm_apply_apply]
      right_inv := fun _ => by simp only [Homeomorph.apply_symm_apply]
      continuous_toFun := hK.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := hKi.comp (continuous_const.prodMk continuous_id) }
  have hb (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : b z = 1 := by
    apply b.one_of_mem_closedBall
    change dist z (1 / 2) ≤ 1 / 2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hformula (p : ℝ × ℝ) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      K 1 (p, z) = (G 1 p, z) := by
    change (G (1 * b z) p, z) = _
    rw [hb z hz, one_mul]
  have hfixed (t : ℝ) : EqOn (K t) id
      ((⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η) ×ˢ
        ball (1 / 2 : ℝ) 1)ᶜ := by
    intro p hp
    change (G (t * b p.2) p.1, p.2) = p
    by_cases hz : p.2 ∈ ball (1 / 2 : ℝ) 1
    · rw [(hfix _).1 (fun hx => hp ⟨hx, hz⟩)]
      rfl
    · have hzero : b p.2 = 0 := b.zero_of_le_dist (le_of_not_gt hz)
      rw [hzero, mul_zero, hG0]
      rfl
  let J : Set ((ℝ × ℝ) × ℝ) :=
    (⋃ i : Fin 3, triangleVertexChart i ⁻¹' closedBall (0 : ℝ × ℝ) η) ×ˢ
      closedBall (1 / 2 : ℝ) 1
  have hJ : IsCompact J := (isCompact_iUnion fun i =>
    (triangleVertexChart i).toHomeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (0 : ℝ × ℝ) η)).prod (isCompact_closedBall (1 / 2 : ℝ) 1)
  have hJfix (t : ℝ) : EqOn (K t) id Jᶜ := by
    apply (hfixed t).mono
    apply compl_subset_compl.mpr
    rintro p ⟨hp, hz⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩, ball_subset_closedBall hz⟩
  let d₃ (i : Fin 3) : ((ℝ × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × ℝ) :=
    { toEquiv := (d.trans (triangleVertexChart i).symm).toEquiv.prodCongr (Equiv.refl ℝ)
      contMDiff_toFun := (((d.trans (triangleVertexChart i).symm).contDiff.comp
        contDiff_fst).prodMk contDiff_snd).contMDiff
      contMDiff_invFun := (((d.trans (triangleVertexChart i).symm).symm.contDiff.comp
        contDiff_fst).prodMk contDiff_snd).contMDiff }
  have himage (q : (ℝ × ℝ) × ℝ) :
      q ∈ K 1 '' (standardTriangleBoundary ×ˢ Icc (0 : ℝ) 1) ↔
        q.1 ∈ G 1 '' standardTriangleBoundary ∧ q.2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hformula x.1 x.2 hx.2]
      exact ⟨⟨x.1, hx.1, rfl⟩, hx.2⟩
    · rintro ⟨⟨x, hx, hxeq⟩, hz⟩
      exact ⟨(x, q.2), ⟨hx, hz⟩, by rw [hformula x q.2 hz, hxeq]⟩
  refine ⟨δ, hδ, hδη, K, hK, hKi, ?_, fun _ _ => rfl, hfixed,
    ⟨J, hJ, ?_⟩, d₃, ?_, ?_, ?_⟩
  · apply Homeomorph.ext
    intro p
    change (G (0 * b p.2) p.1, p.2) = p
    rw [zero_mul, hG0]
    rfl
  · intro t
    refine ⟨hJfix t, fun p hp => ?_⟩
    apply (K t).injective
    rw [(K t).apply_symm_apply, id_eq, hJfix t hp]
    rfl
  · intro i p
    change ((triangleVertexChart i).symm (d p.1), p.2) = _
    rw [hd]
  · intro i p z hz hu hp
    rw [hformula _ z hz, hframe i p hu hp]
    rfl
  · intro p hp
    obtain ⟨e, V, hV, hpV, he⟩ := hcharts p.1 ((himage p).mp hp).1
    let e₃ : ((ℝ × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × ℝ) :=
      { toEquiv := e.toEquiv.prodCongr (Equiv.refl ℝ)
        contMDiff_toFun := ((e.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
        contMDiff_invFun := ((e.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
    refine ⟨e₃, fun _ => rfl, Prod.fst ⁻¹' V, hV.preimage continuous_fst, hpV, ?_⟩
    intro q hq
    exact (himage q).trans (and_congr_left (fun _ => he q.1 hq))

end DifferentialGeometry.Topology.PiecewiseLinear
