import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphGood
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCore

/-!
# The pieces of the spherical fold cover the triangle outside the core

Lane CF-S3, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, review 23 §6.1). Every point of the triangle
other than `v₃ = 0` and outside the inner core disc `‖rotTwo z - c‖ < r - m` lies in one of the
nine pieces of `CompactFoldSphGood` (`mem_sphGoodSet`); this is the hypothesis `hcover` of the
core replacement `exists_sphFoldCore`. The validity conditions hold pointwise on `T`:
* the lens switch of the corner at `v₁`: with `ζ = rotTwo z`, `t = t₁₂` and `q = sphMoeb t ζ`,
  `Re((ζ - t)(1 + tζ)) = Re q · |1 + tζ|² - 2t (Im ζ)²`, and `Re q ≤ 0` on `T`, so this is
  negative on `T` minus `v₁` (`sph_hlam_one`); at `v₂`, `Re ζ ≥ 0` on `T` and `Re ζ = 0` forces
  `Im ζ = ‖ζ‖` (`sph_hlam_two`);
* the outer blend saturates on the boundary circles of the corner discs because the canonical
  sums `Tᵢ + Tⱼ` are nonnegative on `T` (`sphFoldBlend_gt_of_cornerOne`,
  `sphFoldBlend_lt_of_cornerTwo`), and on the walls `0`, `1` by the helper lemmas of
  `CompactFoldSphWalls`;
* the lens arc and the switch windows lie in the inner core (`sphInCore_of_band`), so outside
  the core the side coordinate is below `sphLensWidth` or above `sphSwitchTop`.
The core disc together with its margin lies in the open triangle (`sphCore_hin`, the hypothesis
`hin` of `exists_sphFoldCore`), so the walls lie outside it (`sphCore_add_le_of_wall`) and
`wall i ∩ T \ {0}` lies in the good set (`wall_mem_sphGoodSet`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sph_hlam_one {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne) :
    ((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re < 0 := by
  have hq := re_sphMoeb_nonpos_of_mem hs hz
  have hne := rotTwo_ne_tOneTwo_sph hs (one_add_vertexTwo_ne_sph hs hz) h1
  have hx := re_rotTwo_nonneg_sph hs hz
  have hy := (sector_two_sph hs hz).1
  set ζ := σ.rotTwo z
  set t := σ.sphTOneTwo
  have ht := tOneTwo_pos_sph hs
  have hden : 0 < Complex.normSq (1 + (t : ℂ) * ζ) := by
    rw [normSq_one_add_real_sph]
    positivity
  have hre : (sphMoeb (t : ℂ) ζ).re * Complex.normSq (1 + (t : ℂ) * ζ) =
      ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 + ζ.im ^ 2) - t := by
    rw [sphMoeb, Complex.conj_ofReal, Complex.div_re, add_mul, div_mul_cancel₀ _ hden.ne',
      div_mul_cancel₀ _ hden.ne']
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re,
      one_im]
    ring
  have hA : ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 + ζ.im ^ 2) - t ≤ 0 := by
    rw [← hre]
    exact mul_nonpos_of_nonpos_of_nonneg hq hden.le
  have e : ((ζ - t) * (1 + t * ζ)).re = ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 - ζ.im ^ 2) - t := by
    simp only [mul_re, sub_re, add_re, ofReal_re, ofReal_im, one_re, sub_im, add_im, one_im,
      mul_im]
    ring
  rw [e]
  rcases hy.lt_or_eq with hy | hy
  · nlinarith [mul_pos ht (pow_pos hy 2)]
  · have hxt : ζ.re ≠ t := fun h => hne (Complex.ext (by simpa using h) (by simpa using hy.symm))
    have h1x : 0 < 1 + t * ζ.re := by
      have := mul_nonneg ht.le hx
      linarith
    have hne' : (ζ.re - t) * (1 + t * ζ.re) ≠ 0 := mul_ne_zero (sub_ne_zero.2 hxt) h1x.ne'
    have e2 : ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 - ζ.im ^ 2) - t =
        (ζ.re - t) * (1 + t * ζ.re) := by
      rw [← hy]
      ring
    have e3 : ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 + ζ.im ^ 2) - t =
        (ζ.re - t) * (1 + t * ζ.re) := by
      rw [← hy]
      ring
    rw [e2]
    rw [e3] at hA
    exact lt_of_le_of_ne hA hne'

theorem sph_hlam_two {z : ℂ} (hz : z ∈ σ.triangle) (hd : σ.sphSwitchTop < ‖σ.rotTwo z‖) :
    0 < (σ.rotTwo z).re ∨ σ.sphSwitchTop < σ.sphSideTwo z ∨ σ.sphSideTwo z < σ.sphLensWidth := by
  rcases (re_rotTwo_nonneg_sph hs hz).lt_or_eq with h | h
  · exact Or.inl h
  · right
    left
    have hy := (sector_two_sph hs hz).1
    have hn := Complex.norm_le_abs_re_add_abs_im (σ.rotTwo z)
    rw [← h, abs_zero, zero_add, abs_of_nonneg hy] at hn
    change σ.sphSwitchTop < (σ.rotTwo z).im
    linarith

theorem sphCanon_le_of_cornerRad {j : Fin 3} {z : ℂ} (h : σ.sphDist j z ≤ σ.sphCornerRad j) :
    σ.sphCanon j z ≤ -σ.sphCornerShrink := by
  have hd := one_add_sphDist_mul_pos hs j z
  have t0 := sphTau_pos hs j
  have hδ := (sphParams hs).1
  have hden : 0 < 1 + σ.sphTau j * σ.sphCornerShrink := by positivity
  have hc : σ.sphCornerRad j * (1 + σ.sphTau j * σ.sphCornerShrink) =
      σ.sphTau j - σ.sphCornerShrink := by
    unfold sphCornerRad
    field_simp
  have hm := mul_le_mul_of_nonneg_right h hden.le
  rw [sphCanon, div_le_iff₀ hd]
  nlinarith

omit hs in
theorem sphFoldBlend_eq (z : ℂ) : σ.sphFoldBlend z = (2 * discAngle z / σ.θ₃ - 1) +
    (σ.sphCanon 1 z - σ.sphCanon 0 z) / σ.sphCornerShrink := by
  unfold sphFoldBlend sphBlendThree
  ring

theorem sphFoldBlend_gt_of_cornerOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hd : ‖σ.rotOne z‖ ≤ σ.sphCornerRad 0) : 1 < σ.sphFoldBlend z := by
  have hδ := (sphParams hs).1
  have hT := sphCanon_le_of_cornerRad hs (j := 0) hd
  have hsum := sphCanon_add_two_nonneg hs hz
  have him : 0 < z.im := by
    rcases (im_nonneg_of_mem_sph hs hz).lt_or_eq with h | h
    · exact h
    · exfalso
      have := tauZero_le_of_wallZero_sph hs hz h.symm
      linarith [(sphCornerRad_bounds hs 0).2]
  obtain ⟨s1, s2⟩ := sector_three_sph hs hz
  have hψ := (discAngle_sector σ.θ₃_pos_sph σ.θ₃_le_sph
    (pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz)) s1 s2).2.2.1 him
  have hθ := σ.θ₃_pos_sph
  have hq : 2 ≤ (σ.sphCanon 1 z - σ.sphCanon 0 z) / σ.sphCornerShrink := by
    rw [le_div_iff₀ hδ]
    linarith
  have : 0 < 2 * discAngle z / σ.θ₃ := by positivity
  rw [sphFoldBlend_eq]
  linarith

theorem sphFoldBlend_lt_of_cornerTwo {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hd : ‖σ.rotTwo z‖ ≤ σ.sphCornerRad 1) : σ.sphFoldBlend z < -1 := by
  have hδ := (sphParams hs).1
  have hT := sphCanon_le_of_cornerRad hs (j := 1) hd
  have hsum := sphCanon_add_two_nonneg hs hz
  obtain ⟨s1, s2⟩ := sector_three_sph hs hz
  have hw : 0 < -(exp (-((σ.θ₃ : ℂ) * I)) * z).im := by
    rw [← wallSide_one_eq_neg_im_sph]
    rcases (((mem_triangle_iff_sph hs).1 hz).2.1).lt_or_eq with h | h
    · exact h
    · exfalso
      have := tauOne_le_of_wallOne_sph hs hz h.symm
      linarith [(sphCornerRad_bounds hs 1).2]
  have hψ := (discAngle_sector σ.θ₃_pos_sph σ.θ₃_le_sph
    (pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz)) s1 s2).2.2.2.1 hw
  have hθ := σ.θ₃_pos_sph
  have hq : (σ.sphCanon 1 z - σ.sphCanon 0 z) / σ.sphCornerShrink ≤ -2 := by
    rw [div_le_iff₀ hδ]
    linarith
  have : 2 * discAngle z / σ.θ₃ < 2 := by
    rw [div_lt_iff₀ hθ]
    linarith
  rw [sphFoldBlend_eq]
  linarith

theorem sphCore_hin {ζ : ℂ}
    (hc : ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin) :
    ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ) := by
  obtain ⟨h2, h0, h1⟩ := sphCore_ineqs hs hc
  refine wallSide_pos_sphChartTwo hs h2 ?_ h1
  have e : σ.sphChartSideZero ζ = Real.sin σ.θ₂ * ζ.re - Real.cos σ.θ₂ * ζ.im := by
    rw [sphChartSideZero, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      conj_re, conj_im]
    ring
  rw [e]
  exact h0

theorem sphCoreMargin_pos : 0 < σ.sphCoreMargin := by
  have := sphScale_pos hs
  unfold sphCoreMargin sphLensWidth
  positivity

theorem sphCore_add_le_of_wall {z : ℂ} (hz : z ∈ σ.triangle) {i : Fin 3}
    (hw : σ.wallSide i z = 0) :
    σ.sphCoreRadius + σ.sphCoreMargin ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ := by
  by_contra hlt
  push Not at hlt
  have := sphCore_hin hs hlt i
  rw [sphChartTwo_rotTwo hs (one_add_vertexTwo_ne_sph hs hz), hw] at this
  exact lt_irrefl 0 this

theorem mem_sphGoodSet {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hc : σ.sphCoreRadius - σ.sphCoreMargin ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖) :
    z ∈ σ.sphGoodSet := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨hgc1, hgc2, -, -, hc1τ, hc2τ, hg3τ, -, -⟩ := sphLayout_ineqs hs
  obtain ⟨hbc1, hbc2, hβ'g, hb3τ, hgb⟩ := sphGoodConsts hs
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have hv2' : 1 + conj σ.vertexTwo * z ≠ 0 := by rw [conj_vertexTwo_sph]; exact hv2
  have t2 := sphTau_pos hs 2
  by_cases a1 : ‖σ.rotOne z‖ < σ.sphGermRadius
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hv1, a1⟩)))))))
  by_cases a2 : ‖σ.rotTwo z‖ < σ.sphGermRadius
  · have p1 := (sphDist_gt_of_lt_tau_one hs hz (by linarith)).1
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨hv2, a2, hv1, by linarith⟩)))))))
  by_cases o : ‖z‖ < σ.sphOuterGermRadius
  · obtain ⟨p1, p2⟩ := sphDist_gt_of_outer hs hz (by linarith)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨norm_pos_iff.2 h0, o, hv1, by linarith, hv2, by linarith⟩))))))
  rw [not_lt] at a1 a2 o
  have h1 : z ≠ σ.vertexOne := by
    rintro rfl
    rw [rotOne_vertexOne_sph hs, norm_zero] at a1
    linarith
  have h2 : z ≠ σ.vertexTwo := by
    rintro rfl
    rw [rotTwo_vertexTwo_sph hs, norm_zero] at a2
    linarith
  have d1 := mem_sphDomOne hs hz h0 h1
  have d0 := mem_sphDomZero hs hz h0 h2
  have d2 := mem_sphDomTwo hs hz h1 h2
  obtain ⟨hB2l, hB2u⟩ := re_sphBridgeTwo_mem_sph hs hz
  have hy0 : 0 ≤ σ.sphSideTwo z := (sector_two_sph hs hz).1
  by_cases c1 : ‖σ.rotOne z‖ < σ.sphCornerRad 0
  · obtain ⟨q2, q3⟩ := sphDist_gt_of_cornerOne hs hz c1.le
    have hψ := pos_norm_add_re_sph (rotOne_ne_zero_sph hs hv1 h1) (re_rotOne_nonneg_sph hs hz)
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, c1, by linarith,
      by linarith⟩, d1, d2, hψ, three_halves_lt_re_sphBridgeOne hs hz (by linarith), hB2u,
      Or.inl (sph_hlam_one hs hz h1)⟩)))))
  by_cases c2 : ‖σ.rotTwo z‖ < σ.sphCornerRad 1
  · obtain ⟨q1, q3⟩ := sphDist_gt_of_cornerTwo hs hz c2.le
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, c2, by linarith,
      by linarith⟩, d2, d0, hB2l, re_sphBridgeZero_lt_sph hs hz (by linarith),
      sph_hlam_two hs hz (by linarith)⟩))))
  rw [not_lt] at c1 c2
  by_cases l : σ.sphSideTwo z < σ.sphLensWidth
  · have hn := sph_norm_gt_of_lens hs hz (by linarith) c1
    refine Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, by linarith, ?_, ?_⟩, d2, hB2l,
      hB2u⟩)))
    · rwa [abs_of_nonneg hy0]
    · unfold sphOuterGermRadius
      linarith
  rw [not_lt] at l
  have hw : σ.sphSwitchTop < σ.sphSideTwo z := by
    by_contra hle
    have := sphInCore_of_band hs hz l (not_lt.1 hle) c2
      (by rwa [← norm_rotOne_eq_sphMoeb_rotTwo hs hv1 hv2'])
    exact absurd this (not_lt.2 hc)
  by_cases j1 : ‖σ.rotOne z‖ = σ.sphCornerRad 0
  · obtain ⟨q2, q3⟩ := sphDist_gt_of_cornerOne hs hz j1.le
    exact Or.inl (Or.inr ⟨⟨by linarith, by linarith, hw, by linarith,
      sphFoldBlend_gt_of_cornerOne hs hz h0 j1.le⟩, d1,
      pos_norm_add_re_sph h0 (re_nonneg_of_mem_sph hs hz), hv2,
      three_halves_lt_re_sphBridgeOne hs hz (by linarith)⟩)
  by_cases j2 : ‖σ.rotTwo z‖ = σ.sphCornerRad 1
  · obtain ⟨q1, q3⟩ := sphDist_gt_of_cornerTwo hs hz j2.le
    exact Or.inr ⟨⟨by linarith, by linarith, hw, by linarith,
      sphFoldBlend_lt_of_cornerTwo hs hz h0 j2.le⟩, d0, hv1,
      re_sphBridgeZero_lt_sph hs hz (by linarith)⟩
  have e1 : σ.sphCornerRad 0 < ‖σ.rotOne z‖ := lt_of_le_of_ne c1 (Ne.symm j1)
  have e2 : σ.sphCornerRad 1 < ‖σ.rotTwo z‖ := lt_of_le_of_ne c2 (Ne.symm j2)
  have hT := (mem_triangle_iff_sph hs).1 hz
  have hside : (0 < σ.wallSide 0 z ∧ 0 < σ.wallSide 1 z) ∨ 1 < σ.sphFoldBlend z ∨
      σ.sphFoldBlend z < -1 := by
    rcases hT.1.lt_or_eq with p0 | p0
    · rcases hT.2.1.lt_or_eq with p1 | p1
      · exact Or.inl ⟨p0, p1⟩
      · exact Or.inr (Or.inl (sphBlendThree_gt_of_wallOne hs one_pos hδ hz h0 p1.symm))
    · exact Or.inr (Or.inr (sphBlendThree_lt_of_wallZero hs one_pos hδ hz h0 p0.symm))
  refine Or.inl (Or.inl (Or.inr ⟨⟨e1, e2, ?_, by linarith⟩, d1, d0, re_sphBridgeOne_pos hs hz,
    re_sphBridgeZero_neg hs hz, hside⟩))
  rw [abs_of_nonneg hy0]
  linarith

theorem wall_mem_sphGoodSet (i : Fin 3) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide i z = 0) : z ∈ σ.sphGoodSet := by
  have h := sphCore_add_le_of_wall hs hz hw
  have hm := sphCoreMargin_pos hs
  exact mem_sphGoodSet hs hz h0 (by linarith)

end Spherical

end CompactShape

end GC.Seifert
