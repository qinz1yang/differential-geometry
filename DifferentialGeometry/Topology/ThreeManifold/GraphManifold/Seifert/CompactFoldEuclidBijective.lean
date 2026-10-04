import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCore

/-!
# Bijectivity of the flat compact fold from local data

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §6, the compact form of A4Q's open–closed argument).
`bijOn_of_local` turns the local facts of a fold `F` of a flat triangle (smooth on an open set
containing `T \ {0}` with nonzero Jacobian off `v₁, v₂`, real values on the walls, injective,
`F(T \ {0}) ⊆ basePlusSeven`, `F(v₁) = 3/2`, `F(v₂) = -3/2`, and equal to the outer germ on a
punctured disc about `v₃ = 0`) into `BijOn F (T \ {0}) basePlusSeven`:
* the image of the open triangle is open (inverse function theorem), hence lies in the open upper
  half disc `openHalfSeven`; it is closed in that convex set because near `v₃` the modulus
  `7/2 - ‖z‖^{p₃}/2` of the outer germ is close to `7/2`, which confines the relevant preimages
  to the compact set `T ∩ {‖z‖ ≥ δ}`, and the walls have real image;
* the real segments are reached by the intermediate value theorem along the three walls: wall 1
  from `F(v₁) = 3/2` to the outer germ `7/2 - a^{p₃}/2` near `v₃` (`germ_wallOne`), wall 0 from
  `-3/2` to `-(7/2 - a^{p₃}/2)` (`germ_wallZero`), wall 2 from `-3/2` to `3/2`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem isPreconnected_openHalfSeven : IsPreconnected openHalfSeven := by
  have e : openHalfSeven = ball (0 : ℂ) (7 / 2) ∩ {u : ℂ | 0 < u.im} := by
    ext u
    simp [openHalfSeven]
  rw [e]
  exact ((convex_ball _ _).inter (convex_halfSpace_gt Complex.imLm.isLinear 0)).isPreconnected

theorem isOpen_openHalfSeven : IsOpen openHalfSeven :=
  (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_im)

namespace EuclidShape

variable (σ : EuclidShape)

def interiorSet : Set ℂ := {z | ∀ i, 0 < σ.wallSide i z}

theorem isOpen_interiorSet : IsOpen σ.interiorSet := by
  have e : σ.interiorSet = ⋂ i, {z | 0 < σ.wallSide i z} := by
    ext z
    simp [interiorSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (σ.contDiff_wallSide i).continuous

theorem isClosed_triangle : IsClosed σ.triangle := by
  have e : σ.triangle = ⋂ i, {z | 0 ≤ σ.wallSide i z} := by
    ext z
    simp [triangle]
  rw [e]
  exact isClosed_iInter fun i => isClosed_le continuous_const (σ.contDiff_wallSide i).continuous

theorem isCompact_triangle_cut (δ : ℝ) : IsCompact {z | z ∈ σ.triangle ∧ δ ≤ ‖z‖} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (σ.isClosed_triangle.inter (isClosed_le continuous_const continuous_norm)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset fun z hz => ?_
  rw [mem_closedBall, dist_zero_right]
  exact σ.norm_le_one_of_mem hz.1

theorem half_le_sin_θ₃ : 1 / 2 ≤ Real.sin σ.θ₃ := half_le_sin_aux σ.two_le_p₃ σ.p_le_six.2.2

theorem germ_wallZero {a : ℝ} (ha : 0 < a) :
    compactOuterGerm σ.p₃ (a : ℂ) = ((-(7 / 2 - a ^ σ.p₃ / 2) : ℝ) : ℂ) := by
  have hn : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hq : conj (a : ℂ) / ((a : ℝ) : ℂ) = 1 := by
    rw [Complex.conj_ofReal, div_self (ofReal_ne_zero.2 ha.ne')]
  rw [compactOuterGerm, hn, hq, one_pow, mul_one]
  push_cast
  ring

theorem germ_wallOne {a : ℝ} (ha : 0 < a) :
    compactOuterGerm σ.p₃ ((a : ℂ) * exp ((σ.θ₃ : ℂ) * I)) = ((7 / 2 - a ^ σ.p₃ / 2 : ℝ) : ℂ) := by
  have hn : ‖(a : ℂ) * exp ((σ.θ₃ : ℂ) * I)‖ = a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hc : conj (exp ((σ.θ₃ : ℂ) * I)) = exp (-((σ.θ₃ : ℂ) * I)) := conj_exp_mul_I σ.θ₃
  have hq : conj ((a : ℂ) * exp ((σ.θ₃ : ℂ) * I)) / ((a : ℝ) : ℂ) =
      exp (-((σ.θ₃ : ℂ) * I)) := by
    rw [map_mul, Complex.conj_ofReal, hc, mul_div_right_comm, div_self (ofReal_ne_zero.2 ha.ne'),
      one_mul]
  have hp : exp (-((σ.θ₃ : ℂ) * I)) ^ σ.p₃ = -1 := by
    rw [← Complex.exp_nat_mul, show (σ.p₃ : ℂ) * -((σ.θ₃ : ℂ) * I) =
      -(((σ.θ₃ * σ.p₃ : ℝ) : ℂ) * I) by push_cast; ring, σ.θ₃_mul, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  rw [compactOuterGerm, hn, hq, hp]
  ring

theorem vertexOne_ne_zero : σ.vertexOne ≠ 0 := by
  intro h
  have := σ.norm_vertexOne
  rw [h, norm_zero] at this
  linarith [σ.sin_θ₂_pos]

theorem vertexTwo_ne_zero : σ.vertexTwo ≠ 0 := by
  intro h
  have := σ.norm_vertexTwo
  rw [h, norm_zero] at this
  linarith [σ.sin_θ₁_pos]

section Local

variable {σ}
variable {U : Set ℂ} {F : ℂ → ℂ}

theorem bijOn_of_local (hU : IsOpen U) (hTU : σ.triangle \ {0} ⊆ U) (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ F z).det ≠ 0)
    (hreal : ∀ i, ∀ z ∈ σ.triangle, z ≠ 0 → σ.wallSide i z = 0 → (F z).im = 0)
    (hinj : InjOn F (σ.triangle \ {0})) (hmaps : MapsTo F (σ.triangle \ {0}) basePlusSeven)
    (hv1 : F σ.vertexOne = 3 / 2) (hv2 : F σ.vertexTwo = -(3 / 2)) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hgerm : ∀ z, 0 < ‖z‖ → ‖z‖ < ρ₀ → F z = compactOuterGerm σ.p₃ z) :
    BijOn F (σ.triangle \ {0}) basePlusSeven := by
  have hTi : ∀ z ∈ σ.interiorSet, z ∈ σ.triangle \ {0} := fun z hz =>
    ⟨fun i => (hz i).le, (σ.ne_of_interior hz).1⟩
  have hcont : ∀ z ∈ σ.triangle \ {0}, ContinuousAt F z := fun z hz =>
    (hF.contDiffAt (hU.mem_nhds (hTU hz))).continuousAt
  have hopen : IsOpen (F '' σ.interiorSet) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨-, h1, h2⟩ := σ.ne_of_interior hz
    have hzU := hTU (hTi z hz)
    exact image_mem_nhds_of_det_ne_zero (σ.isOpen_interiorSet.mem_nhds hz)
      (hF.contDiffAt (hU.mem_nhds hzU)) (hdet z hzU h1 h2)
  have hint : ∀ z ∈ σ.interiorSet, F z ∈ openHalfSeven := by
    intro z hz
    have hfz := hmaps (hTi z hz)
    refine ⟨hfz.1, lt_of_le_of_ne hfz.2 fun h0 => ?_⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen (F z) ⟨z, hz, rfl⟩
    have hmem : F z - ((r / 2 : ℝ) : ℂ) * I ∈ Metric.ball (F z) r := by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    obtain ⟨w, hw, hfw⟩ := hball hmem
    have := (hmaps (hTi w hw)).2
    rw [hfw] at this
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at this
    linarith
  have hclosed : closure (F '' σ.interiorSet) ∩ openHalfSeven ⊆ F '' σ.interiorSet := by
    rintro v ⟨hvc, hv7, hvim⟩
    set m := (‖v‖ + 7 / 2) / 2 with hm
    set δ := min (min (ρ₀ / 2) 1) (7 / 2 - ‖v‖) with hδ
    have hδ0 : 0 < δ := lt_min (lt_min (by linarith) one_pos) (by linarith)
    have hδρ : δ < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδv : δ ≤ 7 / 2 - ‖v‖ := min_le_right _ _
    set N := {w : ℂ | ‖w‖ < m} with hN
    have hNo : IsOpen N := isOpen_lt continuous_norm continuous_const
    have hvN : v ∈ N := by
      change ‖v‖ < m
      rw [hm]
      linarith
    set K := {z | z ∈ σ.triangle ∧ δ ≤ ‖z‖} with hK
    have hKmem : ∀ z ∈ σ.triangle \ {0}, F z ∈ N → z ∈ K := by
      intro z hz hfN
      refine ⟨hz.1, ?_⟩
      by_contra hlt
      push Not at hlt
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz.2
      have hpow : ‖z‖ ^ σ.p₃ ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) (by linarith)
        (by have := σ.two_le_p₃; omega)
      have e := norm_compactOuterGerm hz.2 (p := σ.p₃) (by linarith)
      rw [← hgerm z hz0 (by linarith)] at e
      have h1 : ‖F z‖ < m := hfN
      rw [e, hm] at h1
      linarith
    have hKsub : K ⊆ σ.triangle \ {0} := fun z hz => ⟨hz.1, fun h0 => by
      rw [mem_singleton_iff] at h0
      have := hz.2
      rw [h0, norm_zero] at this
      linarith⟩
    have hcomp : IsCompact (F '' K) :=
      (σ.isCompact_triangle_cut δ).image_of_continuousOn
        (fun z hz => (hcont z (hKsub hz)).continuousWithinAt)
    have hv1' : v ∈ closure (N ∩ F '' σ.interiorSet) := hNo.inter_closure ⟨hvN, hvc⟩
    have hv2' : v ∈ F '' K := by
      refine hcomp.isClosed.closure_subset (closure_mono ?_ hv1')
      rintro _ ⟨hwN, z, hz, rfl⟩
      exact ⟨z, hKmem z (hTi z hz) hwN, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := hv2'
    by_cases hzI : z ∈ σ.interiorSet
    · exact ⟨z, hzI, rfl⟩
    · exfalso
      have : ∃ i, σ.wallSide i z = 0 := by
        by_contra hne
        push Not at hne
        exact hzI fun i => lt_of_le_of_ne (hzK.1 i) (hne i).symm
      obtain ⟨i, hi⟩ := this
      have := hreal i z hzK.1 (hKsub hzK).2 hi
      linarith
  have hsub : openHalfSeven ⊆ F '' σ.interiorSet := by
    have hcI : σ.incenter ∈ σ.interiorSet := σ.wallSide_pos_of_near (by simp [σ.inradius_pos])
    exact isPreconnected_openHalfSeven.subset_of_closure_inter_subset hopen
      ⟨_, hint _ hcI, _, hcI, rfl⟩ hclosed
  have hcomp : ∀ {g : ℝ → ℂ} {a b : ℝ}, Continuous g → (∀ t ∈ Icc a b, g t ∈ σ.triangle \ {0}) →
      ContinuousOn (fun t => (F (g t)).re) (Icc a b) := by
    intro g a b hg hmem t ht
    exact (Complex.continuous_re.continuousAt.comp ((hcont _ (hmem t ht)).comp
      hg.continuousAt)).continuousWithinAt
  have hreal' : ∀ i, ∀ z ∈ σ.triangle \ {0}, σ.wallSide i z = 0 → F z = ((F z).re : ℂ) := by
    intro i z hz hw
    exact Complex.ext (by simp) (by simp [hreal i z hz.1 hz.2 hw])
  refine ⟨hmaps, hinj, fun u hu => ?_⟩
  rcases hu.2.lt_or_eq with him | him
  · obtain ⟨z, hz, hzu⟩ := hsub ⟨hu.1, him⟩
    exact ⟨z, hTi z hz, hzu⟩
  have him' : u.im = 0 := him.symm
  have hue : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [him'])
  have hu3 : |u.re| < 7 / 2 := by
    have := hu.1
    rw [hue, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  obtain ⟨a1, a2⟩ := abs_lt.1 hu3
  have hz1 := σ.zero_mem_triangle
  have hs1 := σ.half_le_sin_θ₁
  have hs2 := σ.half_le_sin_θ₂
  have hp3 := σ.two_le_p₃
  rcases le_or_gt (3 / 2) u.re with h1 | h1
  · set a := min (min (ρ₀ / 2) (1 / 2)) ((7 - 2 * u.re) / 2) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
    have haρ : a < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have ha1 : a ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hau : a ≤ (7 - 2 * u.re) / 2 := min_le_right _ _
    have hpow : a ^ σ.p₃ ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
    set t := a / Real.sin σ.θ₂ with ht
    have hsp := σ.sin_θ₂_pos
    have ht0 : 0 < t := div_pos ha0 hsp
    have ht1 : t ≤ 1 := (div_le_one hsp).2 (by linarith)
    set g : ℝ → ℂ := fun s => 0 + (s : ℂ) * (σ.vertexOne - 0) with hg
    have hgc : Continuous g := by fun_prop
    have hgm : ∀ s ∈ Icc t 1, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 1 (g s) = 0 := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ht0 hs.1
      refine ⟨⟨σ.lineMap_mem hz1 σ.vertexOne_mem_triangle hs0.le hs.2, fun h0 => ?_⟩, ?_⟩
      · rw [mem_singleton_iff, hg] at h0
        simp only [zero_add, sub_zero, mul_eq_zero, ofReal_eq_zero] at h0
        rcases h0 with h0 | h0
        · linarith
        · exact σ.vertexOne_ne_zero h0
      · rw [hg, σ.wallSide_lineMap, σ.wallSide_one_zero, σ.wallSide_one_vertexOne]
        ring
    have hgt : g t = ((a : ℝ) : ℂ) * exp ((σ.θ₃ : ℂ) * I) := by
      simp only [hg, zero_add, sub_zero]
      rw [vertexOne, ← mul_assoc, ← ofReal_mul, ht, div_mul_cancel₀ _ hsp.ne']
    have hnt : ‖g t‖ = a := by
      rw [hgt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hFt : (F (g t)).re = 7 / 2 - a ^ σ.p₃ / 2 := by
      rw [hgerm _ (by rw [hnt]; exact ha0) (by rw [hnt]; exact haρ), hgt, σ.germ_wallOne ha0,
        ofReal_re]
    have hF1 : (F (g 1)).re = 3 / 2 := by
      norm_num [hg, hv1]
    obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc' ht1
      (hcomp hgc fun s hs => (hgm s hs).1)
      (show u.re ∈ Icc (F (g 1)).re (F (g t)).re from
        ⟨by rw [hF1]; exact h1, by rw [hFt]; linarith⟩)
    refine ⟨g s, (hgm s hs).1, ?_⟩
    have hsu' : (F (g s)).re = u.re := hsu
    rw [hreal' 1 _ (hgm s hs).1 (hgm s hs).2, hsu', ← hue]
  rcases le_or_gt u.re (-(3 / 2)) with h2 | h2
  · set a := min (min (ρ₀ / 2) (1 / 2)) ((7 + 2 * u.re) / 2) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
    have haρ : a < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have ha1 : a ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hau : a ≤ (7 + 2 * u.re) / 2 := min_le_right _ _
    have hpow : a ^ σ.p₃ ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
    set t := a / Real.sin σ.θ₁ with ht
    have hsp := σ.sin_θ₁_pos
    have ht0 : 0 < t := div_pos ha0 hsp
    have ht1 : t ≤ 1 := (div_le_one hsp).2 (by linarith)
    set g : ℝ → ℂ := fun s => 0 + (s : ℂ) * (σ.vertexTwo - 0) with hg
    have hgc : Continuous g := by fun_prop
    have hgm : ∀ s ∈ Icc t 1, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 0 (g s) = 0 := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ht0 hs.1
      refine ⟨⟨σ.lineMap_mem hz1 σ.vertexTwo_mem_triangle hs0.le hs.2, fun h0 => ?_⟩, ?_⟩
      · rw [mem_singleton_iff, hg] at h0
        simp only [zero_add, sub_zero, mul_eq_zero, ofReal_eq_zero] at h0
        rcases h0 with h0 | h0
        · linarith
        · exact σ.vertexTwo_ne_zero h0
      · rw [hg, σ.wallSide_lineMap, σ.wallSide_zero_zero, σ.wallSide_zero_vertexTwo]
        ring
    have hgt : g t = ((a : ℝ) : ℂ) := by
      simp only [hg, zero_add, sub_zero]
      rw [vertexTwo, ← ofReal_mul, ht, div_mul_cancel₀ _ hsp.ne']
    have hnt : ‖g t‖ = a := by
      rw [hgt, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    have hFt : (F (g t)).re = -(7 / 2 - a ^ σ.p₃ / 2) := by
      rw [hgerm _ (by rw [hnt]; exact ha0) (by rw [hnt]; exact haρ), hgt, σ.germ_wallZero ha0,
        ofReal_re]
    have hF1 : (F (g 1)).re = -(3 / 2) := by
      norm_num [hg, hv2]
    obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc ht1
      (hcomp hgc fun s hs => (hgm s hs).1)
      (show u.re ∈ Icc (F (g t)).re (F (g 1)).re from
        ⟨by rw [hFt]; linarith, by rw [hF1]; exact h2⟩)
    refine ⟨g s, (hgm s hs).1, ?_⟩
    have hsu' : (F (g s)).re = u.re := hsu
    rw [hreal' 0 _ (hgm s hs).1 (hgm s hs).2, hsu', ← hue]
  set g : ℝ → ℂ := fun s => σ.vertexTwo + (s : ℂ) * (σ.vertexOne - σ.vertexTwo) with hg
  have hgc : Continuous g := by fun_prop
  have hw20 : σ.wallSide 2 0 ≠ 0 := by
    rw [wallSide_two_apply]
    simp only [zero_re, zero_im, mul_zero, sub_zero]
    exact (mul_pos σ.sin_θ₁_pos σ.sin_θ₂_pos).ne'
  have hgm : ∀ s ∈ Icc (0 : ℝ) 1, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 2 (g s) = 0 := by
    intro s hs
    have hw : σ.wallSide 2 (g s) = 0 := by
      rw [hg, σ.wallSide_lineMap, σ.wallSide_two_vertexTwo, σ.wallSide_two_vertexOne]
      ring
    refine ⟨⟨σ.lineMap_mem σ.vertexTwo_mem_triangle σ.vertexOne_mem_triangle hs.1 hs.2,
      fun h0 => ?_⟩, hw⟩
    rw [mem_singleton_iff] at h0
    rw [h0] at hw
    exact hw20 hw
  have hF0 : (F (g 0)).re = -(3 / 2) := by
    norm_num [hg, hv2]
  have hF1 : (F (g 1)).re = 3 / 2 := by
    norm_num [hg, hv1]
  obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc zero_le_one
    (hcomp hgc fun s hs => (hgm s hs).1)
    (show u.re ∈ Icc (F (g 0)).re (F (g 1)).re from
      ⟨by rw [hF0]; exact h2.le, by rw [hF1]; exact h1.le⟩)
  refine ⟨g s, (hgm s hs).1, ?_⟩
  have hsu' : (F (g s)).re = u.re := hsu
  rw [hreal' 2 _ (hgm s hs).1 (hgm s hs).2, hsu', ← hue]

end Local

end EuclidShape

end GC.Seifert
