import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypBijective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypInjective

/-!
# The fold data of the hyperbolic compact triangles

Lane CF-H3, tier 3 (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §7, the interface `CompactShape.FoldData` of
`SF/CompactFoldSpec.lean`, curvature `-1`). The fold is the core-replaced map `F` of
`exists_hypFoldCore_bijOn` (`CompactFoldHypBijective`) for `E = hypPreFold σ (hypLayout σ)` and
the good set `hypGoodSet σ` of `CompactFoldHypPieces` (open, in the disc, covering the triangle
outside the core by `mem_hypGoodSet`, with `E` smooth there and of positive Jacobian off
`v₁, v₂`), given the injectivity of `E` on `T \ {0}` (`foldData_of_injOn`), which is
`injOn_hypPreFold` of `CompactFoldHypInjective` (`CompactShape.exists_foldData_hyperbolic`):
* the wall neighbourhoods are `hypWallNbhd σ L i` of `CompactFoldHypWalls` intersected with
  `U ∩ refl⁻¹ U`, reflection stable since the reflections are involutions of the disc, where `F`
  satisfies the reflection identities;
* the apex radii are `g` (about `v₁`, `v₂`) and `g₃` (about `v₃ = 0`): the germ discs lie in the
  good set, at pseudo-hyperbolic distance at least `a > g` from `v₁`, `v₂` resp. at norm at least
  `b₃ > g₃` on the closed core (`core_far`), so `F = E` is the germ there.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

variable {σ : CompactShape}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem core_far {z : ℂ} (hz : ‖z‖ < 1) (hc : ‖mob (hypCoreCenter σ) z‖ ≤ hypCoreRadius σ) :
    (hypLayout σ).a < hd σ 0 z ∧ (hypLayout σ).a < hd σ 1 z ∧ (hypLayout σ).b₃ < ‖z‖ := by
  have hu := coreUnit_pos h
  have hu1 := coreUnit_small (σ := σ)
  have hr : hypCoreRadius σ = 6 * coreUnit σ := rfl
  have hc' : ‖mob (hypCoreCenter σ) z‖ < 13 / 2 * coreUnit σ := by linarith
  have hb := core_chart_bound h hz hc'
  have hT := (mem_openTriangle_of_core h hz (by unfold hypCoreMargin; linarith)).1
  set X := (pChart σ z).re with hXdef
  set Y := (pChart σ z).im with hYdef
  have hX : |X| < 7 * coreUnit σ := by
    rw [← abs_of_pos (by positivity : 0 < 7 * coreUnit σ)]
    apply sq_lt_sq.1
    nlinarith [sq_nonneg (Y - 12 * coreUnit σ)]
  have hX' := abs_lt.1 hX
  have hYl : 5 * coreUnit σ < Y := by nlinarith [sq_nonneg X]
  have hYu : Y < 19 * coreUnit σ := by nlinarith [sq_nonneg X]
  have hY : |Y| < 19 * coreUnit σ := abs_lt.2 ⟨by linarith, hYu⟩
  have h1 := coreUnit_le_one h
  have h2 := coreUnit_le_two h
  have hx1 : tauOne σ * (1 - tauOne σ ^ 2) ≤ tauOne σ :=
    mul_le_of_le_one_right (tauOne_pos h).le (by nlinarith [tauOne_pos h])
  have hx2 : tauTwo σ * (1 - tauTwo σ ^ 2) ≤ tauTwo σ :=
    mul_le_of_le_one_right (tauTwo_pos h).le (by nlinarith [tauTwo_pos h])
  have hns : normSq (pChart σ z) = X ^ 2 + Y ^ 2 := by rw [normSq_apply]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hd_zero_eq_pChart h hz]
    have := third_lt_norm_mob (tauOne_pos h) tauOne_lt_one hu (by linarith) hX hY
    simp only [hypLayout]
    linarith [tauMin_le_one (σ := σ)]
  · rw [hd_one_eq_pChart h hz, ← norm_mob_ofReal_neg_conj]
    have := third_lt_norm_mob (Z := -conj (pChart σ z)) (tauTwo_pos h) tauTwo_lt_one hu
      (by linarith) (by simpa using hX) (by simpa using hY)
    simp only [hypLayout]
    linarith [tauMin_le_two (σ := σ)]
  · have hng := norm_ge_of_pChart h hT
    have hZn : ‖pChart σ z‖ < 21 * coreUnit σ := by
      have h0 : ‖pChart σ z‖ ^ 2 < (21 * coreUnit σ) ^ 2 := by
        rw [Complex.sq_norm, hns]
        have : X ^ 2 < 49 * coreUnit σ ^ 2 := by
          have := sq_lt_sq' hX'.1 hX'.2; linarith
        have : Y ^ 2 < 361 * coreUnit σ ^ 2 := by
          have := sq_lt_sq' (by linarith : -(19 * coreUnit σ) < Y) hYu; linarith
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h0
    have h3 := coreUnit_le_three (σ := σ)
    have : (hypLayout σ).b₃ ≤ tauThree σ / 2 := min_le_left _ _
    linarith

omit h in
theorem norm_lt_one_of_mob_lt {a z : ℂ} (ha : ‖a‖ < 1) (hne : 1 - conj a * z ≠ 0)
    (hm : ‖mob a z‖ < 1) : ‖z‖ < 1 := by
  have e := one_sub_normSq_mob hne
  have h1 : 0 < 1 - normSq (mob a z) := by
    have := normSq_lt_one_of_norm_lt hm; linarith
  have h2 : 0 < 1 - normSq a := by
    have := normSq_lt_one_of_norm_lt ha; linarith
  have h3 : 0 < normSq (1 - conj a * z) := normSq_pos.2 hne
  rw [e] at h1
  have h4 : 0 < (1 - normSq a) * (1 - normSq z) := by
    by_contra hn
    push Not at hn
    have := div_nonpos_of_nonpos_of_nonneg hn h3.le
    linarith
  have h5 : 0 < 1 - normSq z := pos_of_mul_pos_right h4 h2.le
  rw [← Complex.sq_norm] at h5
  nlinarith [norm_nonneg z]

theorem mem_disc_of_apexDisc {v z : ℂ} (hv : ‖v‖ < 1) {r : ℝ} (hr : r < 1)
    (hz : z ∈ σ.apexDisc v r) : ‖z‖ < 1 ∧ ‖mob v z‖ < r := by
  obtain ⟨hne, hm⟩ := hz
  rw [CompactShape.eps_hyp h] at hne
  rw [CompactShape.disc_eq_mob h] at hm
  have hne' : 1 - conj v * z ≠ 0 := by simpa using hne
  exact ⟨norm_lt_one_of_mob_lt hv hne' (lt_trans hm hr), hm⟩

theorem foldData_of_injOn (hinj : InjOn (hypPreFold σ (hypLayout σ)) (σ.triangle \ {0})) :
    Nonempty σ.FoldData := by
  obtain ⟨F, U, hUo, h0U, hUd, hTU, hGU, hF, hdet, hFE, hrefl, hbij⟩ :=
    exists_hypFoldCore_bijOn h (isOpen_hypGoodSet h) (fun z hz => norm_lt_one_of_hypGoodSet h hz)
      (fun z hz h0 hc => mem_hypGoodSet h hz h0 hc) (fun z hz => (good_hypPreFold h hz).1)
      (fun z hz h1 h2 => (good_hypPreFold h hz).2 h1 h2) hinj
  obtain ⟨hg0, hga, hab, hb1, he, hc1, hc2, hβ0, hββ, hs1, hs2, hg30, hg3a, ha3b, hb3t, hb35⟩ :=
    hypLayout_params h
  have hfar : ∀ z, ‖z‖ < 1 → z ∈ hypGoodSet σ → z ≠ 0 →
      ((hypLayout σ).a ≤ hd σ 0 z → False) ∨ ((hypLayout σ).a ≤ hd σ 1 z → False) ∨
        ((hypLayout σ).b₃ < ‖z‖ → False) →
      z ∈ U ∧ F z = hypPreFold σ (hypLayout σ) z := by
    intro z hz1 hG h0 hn
    have hc : hypCoreRadius σ < ‖mob (hypCoreCenter σ) z‖ := by
      by_contra hle
      push Not at hle
      obtain ⟨a0, a1, a3⟩ := core_far h hz1 hle
      rcases hn with hn | hn | hn
      · exact hn a0.le
      · exact hn a1.le
      · exact hn a3
    exact ⟨hGU z hG h0 hc, hFE z hc.le⟩
  have hz0 : ∀ z : ℂ, z = 0 → (hypLayout σ).g < hd σ 0 z ∧ (hypLayout σ).g < hd σ 1 z := by
    intro z e0
    exact g_lt_hd_of_outer h (by rw [e0, norm_zero]; exact hg30)
  refine ⟨{
    U := U
    f := F
    isOpen_U := hUo
    U_subset_plane := fun z hz => by
      rw [CompactShape.plane_hyp h, Metric.mem_ball, dist_zero_right]; exact hUd z hz
    zero_not_mem_U := h0U
    triangle_diff_subset_U := hTU
    contDiffOn_f := hF
    det_fderiv_pos := hdet
    V := fun i => {z | z ∈ hypWallNbhd σ (hypLayout σ) i ∧ z ∈ U ∧ σ.refl i z ∈ U}
    isOpen_V := fun i => by
      refine isOpen_iff_mem_nhds.2 fun z hz => ?_
      have hz1 := hUd z hz.2.1
      filter_upwards [(isOpen_hypWallNbhd h _ i).mem_nhds hz.1, hUo.mem_nhds hz.2.1,
        (continuousAt_refl h i hz1).preimage_mem_nhds (hUo.mem_nhds hz.2.2)] with u a b c
      exact ⟨a, b, c⟩
    V_subset_U := fun i z hz => hz.2.1
    V_subset_reflChart := fun i z hz => hypWallNbhd_subset_reflChart h _ i hz.1
    foldWall_diff_subset_V := fun i z hz => by
      have hzT : z ∈ σ.triangle \ {0} := ⟨hz.1.1, hz.2⟩
      have hz1 := norm_lt_one_of_mem h hz.1.1
      refine ⟨foldWall_diff_subset_hypWallNbhd h hg0 hga hab hb1 he hc1 hc2 hβ0 hs1 hs2 hg3a
        ha3b hb3t i hz, hTU hzT, ?_⟩
      rw [refl_eq_self h i hz1 hz.1.2]
      exact hTU hzT
    refl_mapsTo_V := fun i z hz => by
      have hz1 := hUd z hz.2.1
      refine ⟨refl_mapsTo_hypWallNbhd h _ i hz.1, hz.2.2, ?_⟩
      rw [refl_refl h i hz1]
      exact hz.2.1
    f_refl := fun i z hz => hrefl i z hz.1
    bijOn_f := hbij
    apexRadius := ![(hypLayout σ).g, (hypLayout σ).g, (hypLayout σ).g₃]
    apexRadius_pos := fun i => by
      fin_cases i
      · exact hg0
      · exact hg0
      · exact hg30
    f_apexOne := fun z hz => by
      obtain ⟨hz1, hm⟩ := mem_disc_of_apexDisc h (norm_vertexOne_lt_one h)
        (by change (hypLayout σ).g < 1; linarith) hz
      have hm' : hd σ 0 z < (hypLayout σ).g := hm
      have hA : z ∈ pieceApexOne σ := ⟨hz1, hm'⟩
      have h0 : z ≠ 0 := fun e0 => by
        have := (hz0 z e0).1
        linarith
      obtain ⟨hU, hFz⟩ := hfar z hz1
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hA)))))))) h0
        (Or.inl fun ha => by linarith)
      exact ⟨hU, by rw [hFz, hypPreFold_eq_apexOne hA]⟩
    f_apexTwo := fun z hz => by
      obtain ⟨hz1, hm⟩ := mem_disc_of_apexDisc h (norm_vertexTwo_lt_one h)
        (by change (hypLayout σ).g < 1; linarith) hz
      have hm' : hd σ 1 z < (hypLayout σ).g := hm
      have hB : z ∈ pieceApexTwo σ := ⟨hz1, hm'⟩
      have h0 : z ≠ 0 := fun e0 => by
        have := (hz0 z e0).2
        linarith
      obtain ⟨hU, hFz⟩ := hfar z hz1
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hB)))))))) h0
        (Or.inr (Or.inl fun ha => by linarith))
      exact ⟨hU, by rw [hFz, hypPreFold_eq_apexTwo h hB]⟩
    f_outer := fun z hpos hz => by
      have hz' : ‖z‖ < (hypLayout σ).g₃ := hz
      have hO : z ∈ pieceOuter σ := ⟨hpos, hz'⟩
      have hz1 : ‖z‖ < 1 := by linarith
      obtain ⟨hU, hFz⟩ := hfar z hz1
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hO))))))) (norm_pos_iff.1 hpos)
        (Or.inr (Or.inr fun hb => by linarith))
      exact ⟨hU, by rw [hFz, hypPreFold_eq_outerPiece h hO]⟩ }⟩

end Hyp

theorem exists_foldData_hyperbolic_of_injOn
    (hinj : ∀ σ : CompactShape, σ.curv = .hyperbolic →
      InjOn (hypPreFold σ (hypLayout σ)) (σ.triangle \ {0}))
    (σ : CompactShape) (h : σ.curv = .hyperbolic) : Nonempty σ.FoldData :=
  foldData_of_injOn h (hinj σ h)

end HypFold

namespace CompactShape

theorem exists_foldData_hyperbolic (σ : CompactShape) (h : σ.curv = .hyperbolic) :
    Nonempty σ.FoldData :=
  HypFold.foldData_of_injOn h (HypFold.injOn_hypPreFold h)

end CompactShape

end GC.Seifert
