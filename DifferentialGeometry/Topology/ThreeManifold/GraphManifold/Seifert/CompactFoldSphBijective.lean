import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidBijective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGenericWalls

/-!
# Bijectivity of the spherical compact fold from local data

Lane CF-S3w, tier 3, curvature `+1` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §6). Templates: `CompactFoldEuclidBijective`,
`CompactFoldHypBijective`. Every declaration carries `sph`.

`sphBijOn_of_local` turns the local facts of a fold `F` of a spherical triangle (smooth on an
open set containing `T \ {0}` with nonzero Jacobian off `v₁, v₂`, real on the walls, injective,
`F(T \ {0}) ⊆ basePlusSeven`, `F(v₁) = 3/2`, `F(v₂) = -3/2`, the outer germ on `T` near `v₃ = 0`)
into `BijOn F (T \ {0}) basePlusSeven`: the image of the open triangle is open, hence in the open
upper half disc, and closed there (the outer germ confines the relevant preimages to the compact
`T ∩ {‖z‖ ≥ δ}`); the real segments come from the intermediate value theorem along the walls.
In the stereographic chart `T` is convex (walls 0, 1 are lines through `0`, the side function of
wall 2 is concave: `wallSide_two_segment_sph`), so walls 0, 1 are the segments `[0, v₂]`,
`[0, v₁]`. Wall 2 is a circular arc there; it is run as the straight segment `[0, t₁₂]` of the
chart `ζ = rotTwo z`, pulled back by `sphChartTwo` (`sphWallTwoPath`).

For the fold of `exists_sphFoldCore` the hypotheses are derived (`sphFold_bijOn`): the walls lie
outside the core (`far_core_of_wall_sph`), where `F = sphPreFold`, which is real on the walls
(`im_sphPreFold_of_wall`, from the reflection identities of `CompactFoldSphWalls`), takes the
values `±3/2` at `v₁, v₂` and is the outer germ near `0`. `exists_sphFoldCore_bijOn` packages the
core replacement with its bijectivity.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

theorem wallSide_zero_segment_sph (a b : ℂ) (s : ℝ) :
    σ.wallSide 0 (a + (s : ℂ) * (b - a)) = (1 - s) * σ.wallSide 0 a + s * σ.wallSide 0 b := by
  simp only [wallSide_zero_apply_sph, add_im, mul_im, ofReal_re, ofReal_im, sub_re, sub_im,
    zero_mul, add_zero]
  ring

theorem wallSide_one_segment_sph (a b : ℂ) (s : ℝ) :
    σ.wallSide 1 (a + (s : ℂ) * (b - a)) = (1 - s) * σ.wallSide 1 a + s * σ.wallSide 1 b := by
  simp only [wallSide_one_apply_sph, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, sub_re,
    sub_im, zero_mul, sub_zero, add_zero]
  ring

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem wallSide_two_segment_sph (a b : ℂ) (s : ℝ) :
    σ.wallSide 2 (a + (s : ℂ) * (b - a)) = (1 - s) * σ.wallSide 2 a + s * σ.wallSide 2 b +
      Real.sin σ.θ₂ * σ.sphTTwoThree * (s * (1 - s)) * ‖b - a‖ ^ 2 := by
  simp only [wallSide_two_apply_sph hs, sq_norm_eq_sph, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, sub_re, sub_im, zero_mul, sub_zero, add_zero]
  ring

theorem segment_mem_triangle_sph {a b : ℂ} (ha : a ∈ σ.triangle) (hb : b ∈ σ.triangle) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ 1) : a + (s : ℂ) * (b - a) ∈ σ.triangle := by
  obtain ⟨a0, a1, a2⟩ := (mem_triangle_iff_sph hs).1 ha
  obtain ⟨b0, b1, b2⟩ := (mem_triangle_iff_sph hs).1 hb
  refine (mem_triangle_iff_sph hs).2 ⟨?_, ?_, ?_⟩
  · rw [wallSide_zero_segment_sph]
    exact segment_nonneg_sph h0 h1 a0 b0
  · rw [wallSide_one_segment_sph]
    exact segment_nonneg_sph h0 h1 a1 b1
  · rw [wallSide_two_segment_sph hs]
    have := segment_nonneg_sph h0 h1 a2 b2
    have hk : 0 ≤ Real.sin σ.θ₂ * σ.sphTTwoThree * (s * (1 - s)) * ‖b - a‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg σ.sin_θ₂_pos_sph.le (tTwoThree_pos_sph hs).le)
        (mul_nonneg h0 (sub_nonneg.2 h1))) (sq_nonneg _)
    linarith

theorem smul_mem_triangle_sph {v : ℂ} (hv : v ∈ σ.triangle) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (s : ℂ) * v ∈ σ.triangle := by
  have := segment_mem_triangle_sph hs (zero_mem_triangle_sph hs) hv h0 h1
  rwa [zero_add, sub_zero] at this

theorem interior_point_sph : ∀ i, 0 < σ.wallSide i ((σ.vertexOne + σ.vertexTwo) / 4) := by
  have e : (σ.vertexOne + σ.vertexTwo) / 4 =
      0 + ((1 / 2 : ℝ) : ℂ) * ((σ.vertexTwo + ((1 / 2 : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo)) -
        0) := by
    push_cast
    ring
  have w20 := wallSide_two_zero_pos_sph hs
  have w0 := wallSide_zero_vertexOne_pos_sph hs
  have w1 := wallSide_one_vertexTwo_pos_sph hs
  have hm := wallSide_two_segment_sph hs σ.vertexTwo σ.vertexOne (1 / 2)
  rw [wallSide_two_vertexTwo_sph hs, wallSide_two_vertexOne_sph hs] at hm
  have hm0 : 0 ≤ σ.wallSide 2 (σ.vertexTwo + ((1 / 2 : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo)) := by
    rw [hm]
    have := mul_nonneg (mul_nonneg σ.sin_θ₂_pos_sph.le (tTwoThree_pos_sph hs).le)
      (sq_nonneg ‖σ.vertexOne - σ.vertexTwo‖)
    nlinarith
  intro i
  rw [e]
  fin_cases i
  · change 0 < σ.wallSide 0 _
    rw [wallSide_zero_segment_sph, wallSide_zero_segment_sph, wallSide_zero_zero_sph,
      wallSide_zero_vertexTwo_sph]
    linarith
  · change 0 < σ.wallSide 1 _
    rw [wallSide_one_segment_sph, wallSide_one_segment_sph, wallSide_one_zero_sph,
      wallSide_one_vertexOne_sph]
    linarith
  · change 0 < σ.wallSide 2 _
    rw [wallSide_two_segment_sph hs]
    have := mul_nonneg (mul_nonneg σ.sin_θ₂_pos_sph.le (tTwoThree_pos_sph hs).le)
      (sq_nonneg ‖(σ.vertexTwo + ((1 / 2 : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo)) - 0‖)
    nlinarith

theorem isOpen_interior_sph : IsOpen {z : ℂ | ∀ i, 0 < σ.wallSide i z} := by
  have e : {z : ℂ | ∀ i, 0 < σ.wallSide i z} = ⋂ i, {z | 0 < σ.wallSide i z} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_wallSide_sph hs i)

variable (σ) in
def sphWallTwoPath (s : ℝ) : ℂ := σ.sphChartTwo ((s * σ.sphTOneTwo : ℝ) : ℂ)

omit hs in
theorem sphWallTwoPath_zero : σ.sphWallTwoPath 0 = σ.vertexTwo := by
  rw [sphWallTwoPath, zero_mul, ofReal_zero, sphChartTwo_zero]

theorem sphWallTwoPath_one : σ.sphWallTwoPath 1 = σ.vertexOne := by
  rw [sphWallTwoPath, one_mul, ← rotTwo_vertexOne_sph hs]
  exact sphChartTwo_rotTwo hs (one_add_vertexTwo_ne_sph hs (vertexOne_mem_triangle_sph hs))

theorem sphWallTwoPath_region {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ((s * σ.sphTOneTwo : ℝ) : ℂ) ∈ σ.sphChartRegion := by
  have ha := chartRegion_of_mem_triangle_sph hs (vertexTwo_mem_triangle_sph hs)
  have hb := chartRegion_of_mem_triangle_sph hs (vertexOne_mem_triangle_sph hs)
  rw [rotTwo_vertexTwo_sph hs] at ha
  rw [rotTwo_vertexOne_sph hs] at hb
  have := segment_mem_sphChartRegion (tOneTwo_pos_sph hs).le ha hb h0 h1
  rwa [zero_add, sub_zero, ← ofReal_mul] at this

theorem sphWallTwoPath_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    σ.sphWallTwoPath s ∈ σ.triangle \ {0} ∧ σ.wallSide 2 (σ.sphWallTwoPath s) = 0 := by
  obtain ⟨hT, hd⟩ := mem_triangle_sphChartTwo hs (sphWallTwoPath_region hs h0 h1)
  have hw : σ.wallSide 2 (σ.sphWallTwoPath s) = 0 := by
    rw [wallSide_two_eq_sph hs, sphWallTwoPath, rotTwo_sphChartTwo hs hd, ofReal_im, zero_mul]
  refine ⟨⟨hT, fun h => ?_⟩, hw⟩
  rw [mem_singleton_iff] at h
  rw [h] at hw
  exact (wallSide_two_zero_pos_sph hs).ne' hw

theorem continuousOn_sphWallTwoPath : ContinuousOn σ.sphWallTwoPath (Icc 0 1) := fun s hs' => by
  have hd := (mem_triangle_sphChartTwo hs (sphWallTwoPath_region hs hs'.1 hs'.2)).2
  have hc : ContinuousAt (fun t : ℝ => ((t * σ.sphTOneTwo : ℝ) : ℂ)) s := by fun_prop
  have hcomp := ContinuousAt.comp (g := σ.sphChartTwo)
    (f := fun t : ℝ => ((t * σ.sphTOneTwo : ℝ) : ℂ)) (x := s)
    (contDiffAt_sphChartTwo hd).continuousAt hc
  exact hcomp.continuousWithinAt

theorem sphBijOn_of_local {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hTU : σ.triangle \ {0} ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ F z).det ≠ 0)
    (hreal : ∀ i, ∀ z ∈ σ.triangle, z ≠ 0 → σ.wallSide i z = 0 → (F z).im = 0)
    (hinj : InjOn F (σ.triangle \ {0})) (hmaps : MapsTo F (σ.triangle \ {0}) basePlusSeven)
    (hv1 : F σ.vertexOne = 3 / 2) (hv2 : F σ.vertexTwo = -(3 / 2)) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hgerm : ∀ z ∈ σ.triangle, 0 < ‖z‖ → ‖z‖ < ρ₀ → F z = compactOuterGerm σ.p₃ z) :
    BijOn F (σ.triangle \ {0}) basePlusSeven := by
  set Ti := {z : ℂ | ∀ i, 0 < σ.wallSide i z} with hTi_def
  have hTi : ∀ z ∈ Ti, z ∈ σ.triangle \ {0} := fun z hz =>
    ⟨(mem_triangle_iff_sph hs).2 ⟨(hz 0).le, (hz 1).le, (hz 2).le⟩,
      (ne_vertices_of_pos_sph hs hz).1⟩
  have hcont : ∀ z ∈ σ.triangle \ {0}, ContinuousAt F z := fun z hz =>
    (hF.contDiffAt (hU.mem_nhds (hTU hz))).continuousAt
  have hopen : IsOpen (F '' Ti) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨-, h1, h2⟩ := ne_vertices_of_pos_sph hs hz
    have hzU := hTU (hTi z hz)
    exact image_mem_nhds_of_det_ne_zero ((isOpen_interior_sph hs).mem_nhds hz)
      (hF.contDiffAt (hU.mem_nhds hzU)) (hdet z hzU h1 h2)
  have hint : ∀ z ∈ Ti, F z ∈ openHalfSeven := by
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
  have hclosed : closure (F '' Ti) ∩ openHalfSeven ⊆ F '' Ti := by
    rintro v ⟨hvc, hv7, hvim⟩
    set m := (‖v‖ + 7 / 2) / 2 with hm
    set δ := min (ρ₀ / 2) (7 / 2 - ‖v‖) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    have hδρ : δ < ρ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
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
      have hz1 := norm_le_one_of_mem_sph hs hz.1
      have hpow : ‖z‖ ^ σ.p₃ ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1
        (by have := σ.two_le_p₃; omega)
      have e := norm_compactOuterGerm hz.2 (p := σ.p₃) (by linarith)
      rw [← hgerm z hz.1 hz0 (by linarith)] at e
      have h1 : ‖F z‖ < m := hfN
      rw [e, hm] at h1
      linarith
    have hKsub : K ⊆ σ.triangle \ {0} := fun z hz => ⟨hz.1, fun h0 => by
      rw [mem_singleton_iff] at h0
      have := hz.2
      rw [h0, norm_zero] at this
      linarith⟩
    have hKc : IsCompact K :=
      (isCompact_triangle_sph hs).inter_right (isClosed_le continuous_const continuous_norm)
    have hcomp : IsCompact (F '' K) :=
      hKc.image_of_continuousOn fun z hz => (hcont z (hKsub hz)).continuousWithinAt
    have hv1' : v ∈ closure (N ∩ F '' Ti) := hNo.inter_closure ⟨hvN, hvc⟩
    have hv2' : v ∈ F '' K := by
      refine hcomp.isClosed.closure_subset (closure_mono ?_ hv1')
      rintro _ ⟨hwN, z, hz, rfl⟩
      exact ⟨z, hKmem z (hTi z hz) hwN, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := hv2'
    by_cases hzI : z ∈ Ti
    · exact ⟨z, hzI, rfl⟩
    · exfalso
      have hT3 := (mem_triangle_iff_sph hs).1 hzK.1
      have : ∃ i, σ.wallSide i z = 0 := by
        by_contra hne
        push Not at hne
        refine hzI fun i => ?_
        fin_cases i
        · exact lt_of_le_of_ne hT3.1 (hne 0).symm
        · exact lt_of_le_of_ne hT3.2.1 (hne 1).symm
        · exact lt_of_le_of_ne hT3.2.2 (hne 2).symm
      obtain ⟨i, hi⟩ := this
      have := hreal i z hzK.1 (hKsub hzK).2 hi
      linarith
  have hsub : openHalfSeven ⊆ F '' Ti := by
    have hcI : (σ.vertexOne + σ.vertexTwo) / 4 ∈ Ti := interior_point_sph hs
    exact isPreconnected_openHalfSeven.subset_of_closure_inter_subset hopen
      ⟨_, hint _ hcI, _, hcI, rfl⟩ hclosed
  have hcomp : ∀ {g : ℝ → ℂ} {a b : ℝ}, ContinuousOn g (Icc a b) →
      (∀ t ∈ Icc a b, g t ∈ σ.triangle \ {0}) →
      ContinuousOn (fun t => (F (g t)).re) (Icc a b) := by
    intro g a b hg hmem t ht
    exact Complex.continuous_re.continuousAt.comp_continuousWithinAt
      ((hcont _ (hmem t ht)).comp_continuousWithinAt (hg t ht))
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
  have hp3 := σ.two_le_p₃
  rcases le_or_gt (3 / 2) u.re with h1 | h1
  · have hT1 := tOneThree_pos_sph hs
    have hT1' := tOneThree_le_one_sph hs
    set a := min (min (ρ₀ / 2) (σ.sphTOneThree / 2)) ((7 - 2 * u.re) / 2) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have haρ : a < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have haT : a ≤ σ.sphTOneThree / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hau : a ≤ (7 - 2 * u.re) / 2 := min_le_right _ _
    have hpow : a ^ σ.p₃ ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
    set t := a / σ.sphTOneThree with ht
    have ht0 : 0 < t := div_pos ha0 hT1
    have ht1 : t ≤ 1 := (div_le_one hT1).2 (by linarith)
    set g : ℝ → ℂ := fun s => (s : ℂ) * σ.vertexOne with hg
    have hgc : ContinuousOn g (Icc t 1) := by fun_prop
    have hgm : ∀ s ∈ Icc t 1, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 1 (g s) = 0 := by
      intro s hs'
      have hs0 : 0 < s := lt_of_lt_of_le ht0 hs'.1
      refine ⟨⟨smul_mem_triangle_sph hs (vertexOne_mem_triangle_sph hs) hs0.le hs'.2,
        fun h0 => ?_⟩, ?_⟩
      · rw [mem_singleton_iff] at h0
        have := congrArg norm h0
        rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
          norm_vertexOne_sph hs, norm_zero] at this
        have := mul_pos hs0 hT1
        linarith
      · have e := wallSide_one_segment_sph (σ := σ) 0 σ.vertexOne s
        rw [zero_add, sub_zero, wallSide_one_zero_sph, wallSide_one_vertexOne_sph] at e
        change σ.wallSide 1 ((s : ℂ) * σ.vertexOne) = 0
        rw [e]
        ring
    have hgt : g t = ((a : ℝ) : ℂ) * exp ((σ.θ₃ : ℂ) * I) := by
      simp only [hg]
      rw [vertexOne_eq_sph, ← mul_assoc, ← ofReal_mul, ht, div_mul_cancel₀ _ hT1.ne']
    have hnt : ‖g t‖ = a := by
      rw [hgt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hFt : (F (g t)).re = 7 / 2 - a ^ σ.p₃ / 2 := by
      rw [hgerm _ (hgm t ⟨le_rfl, ht1⟩).1.1 (by rw [hnt]; exact ha0) (by rw [hnt]; exact haρ),
        hgt, outerGerm_ray σ.θ₃_mul_sph ha0, ofReal_re]
    have hF1 : (F (g 1)).re = 3 / 2 := by
      norm_num [hg, hv1]
    obtain ⟨s, hs', hsu⟩ := intermediate_value_Icc' ht1
      (hcomp hgc fun s hs' => (hgm s hs').1)
      (show u.re ∈ Icc (F (g 1)).re (F (g t)).re from
        ⟨by rw [hF1]; exact h1, by rw [hFt]; linarith⟩)
    refine ⟨g s, (hgm s hs').1, ?_⟩
    have hsu' : (F (g s)).re = u.re := hsu
    rw [hreal' 1 _ (hgm s hs').1 (hgm s hs').2, hsu', ← hue]
  rcases le_or_gt u.re (-(3 / 2)) with h2 | h2
  · have hT2 := tTwoThree_pos_sph hs
    have hT2' := tTwoThree_le_one_sph hs
    set a := min (min (ρ₀ / 2) (σ.sphTTwoThree / 2)) ((7 + 2 * u.re) / 2) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have haρ : a < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have haT : a ≤ σ.sphTTwoThree / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hau : a ≤ (7 + 2 * u.re) / 2 := min_le_right _ _
    have hpow : a ^ σ.p₃ ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
    set t := a / σ.sphTTwoThree with ht
    have ht0 : 0 < t := div_pos ha0 hT2
    have ht1 : t ≤ 1 := (div_le_one hT2).2 (by linarith)
    set g : ℝ → ℂ := fun s => (s : ℂ) * σ.vertexTwo with hg
    have hgc : ContinuousOn g (Icc t 1) := by fun_prop
    have hgm : ∀ s ∈ Icc t 1, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 0 (g s) = 0 := by
      intro s hs'
      have hs0 : 0 < s := lt_of_lt_of_le ht0 hs'.1
      refine ⟨⟨smul_mem_triangle_sph hs (vertexTwo_mem_triangle_sph hs) hs0.le hs'.2,
        fun h0 => ?_⟩, ?_⟩
      · rw [mem_singleton_iff] at h0
        have := congrArg norm h0
        rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
          norm_vertexTwo_sph hs, norm_zero] at this
        have := mul_pos hs0 hT2
        linarith
      · change σ.wallSide 0 ((s : ℂ) * σ.vertexTwo) = 0
        rw [wallSide_zero_apply_sph, vertexTwo_eq_sph, ← ofReal_mul, ofReal_im]
    have hgt : g t = ((a : ℝ) : ℂ) := by
      simp only [hg]
      rw [vertexTwo_eq_sph, ← ofReal_mul, ht, div_mul_cancel₀ _ hT2.ne']
    have hnt : ‖g t‖ = a := by
      rw [hgt, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    have hFt : (F (g t)).re = -(7 / 2 - a ^ σ.p₃ / 2) := by
      rw [hgerm _ (hgm t ⟨le_rfl, ht1⟩).1.1 (by rw [hnt]; exact ha0) (by rw [hnt]; exact haρ),
        hgt, outerGerm_real σ.p₃ ha0, ofReal_re]
    have hF1 : (F (g 1)).re = -(3 / 2) := by
      norm_num [hg, hv2]
    obtain ⟨s, hs', hsu⟩ := intermediate_value_Icc ht1
      (hcomp hgc fun s hs' => (hgm s hs').1)
      (show u.re ∈ Icc (F (g t)).re (F (g 1)).re from
        ⟨by rw [hFt]; linarith, by rw [hF1]; exact h2⟩)
    refine ⟨g s, (hgm s hs').1, ?_⟩
    have hsu' : (F (g s)).re = u.re := hsu
    rw [hreal' 0 _ (hgm s hs').1 (hgm s hs').2, hsu', ← hue]
  have hgm : ∀ s ∈ Icc (0 : ℝ) 1, σ.sphWallTwoPath s ∈ σ.triangle \ {0} ∧
      σ.wallSide 2 (σ.sphWallTwoPath s) = 0 := fun s hs' => sphWallTwoPath_mem hs hs'.1 hs'.2
  have hF0 : (F (σ.sphWallTwoPath 0)).re = -(3 / 2) := by
    rw [sphWallTwoPath_zero, hv2]
    norm_num
  have hF1 : (F (σ.sphWallTwoPath 1)).re = 3 / 2 := by
    rw [sphWallTwoPath_one hs, hv1]
    norm_num
  obtain ⟨s, hs', hsu⟩ := intermediate_value_Icc zero_le_one
    (hcomp (continuousOn_sphWallTwoPath hs) fun s hs' => (hgm s hs').1)
    (show u.re ∈ Icc (F (σ.sphWallTwoPath 0)).re (F (σ.sphWallTwoPath 1)).re from
      ⟨by rw [hF0]; exact h2.le, by rw [hF1]; exact h1.le⟩)
  refine ⟨σ.sphWallTwoPath s, (hgm s hs').1, ?_⟩
  have hsu' : (F (σ.sphWallTwoPath s)).re = u.re := hsu
  rw [hreal' 2 _ (hgm s hs').1 (hgm s hs').2, hsu', ← hue]

theorem im_sphPreFold_of_wall (i : Fin 3) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide i z = 0) : (σ.sphPreFold z).im = 0 := by
  have hV := wall_mem_sphPreFoldNbhd hs i hz h0 hw (mem_univ z)
  have e := sphPreFold_refl hs i hV
  rw [refl_eq_self_sph hs i (sphWallNbhd_subset_reflChart univ _ i hV) hw] at e
  exact Complex.conj_eq_iff_im.1 e.symm

theorem sphPreFold_vertexOne : σ.sphPreFold σ.vertexOne = 3 / 2 := by
  have h0 : ‖σ.rotOne σ.vertexOne‖ < σ.sphGermRadius := by
    rw [rotOne_vertexOne_sph hs, norm_zero]
    exact (sphParams hs).2.2.2.1
  unfold sphPreFold
  rw [ite_eq_left h0, sphApexOne, rotOne_vertexOne_sph hs, zero_pow (by have := σ.two_le_p₁; omega)]
  ring

theorem sphPreFold_vertexTwo : σ.sphPreFold σ.vertexTwo = -(3 / 2) := by
  have h1 : ¬ ‖σ.rotOne σ.vertexTwo‖ < σ.sphGermRadius := by
    have e : σ.sphTau 0 ≤ ‖σ.rotOne σ.vertexTwo‖ := tau_le_of_sphCanon_nonneg hs (j := 0)
      (by rw [sphCanon_zero_vertexTwo hs]; exact (sphTau_pos hs 1).le)
    have := sphGermRadius_lt_tau hs 0 (by decide)
    exact not_lt.2 (by linarith)
  have h2 : ‖σ.rotTwo σ.vertexTwo‖ < σ.sphGermRadius := by
    rw [rotTwo_vertexTwo_sph hs, norm_zero]
    exact (sphParams hs).2.2.2.1
  unfold sphPreFold
  rw [ite_eq_right h1, ite_eq_left h2, sphApexTwo, rotTwo_vertexTwo_sph hs,
    zero_pow (by have := σ.two_le_p₂; omega)]
  ring

theorem far_core_of_wall_sph
    (hin : ∀ ζ : ℂ, ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin →
      ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ))
    {i : Fin 3} {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide i z = 0) :
    σ.sphCoreRadius + σ.sphCoreMargin ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ := by
  by_contra hc
  push Not at hc
  have := hin _ hc i
  rw [sphChartTwo_rotTwo hs (one_add_vertexTwo_ne_sph hs hz), hw] at this
  exact lt_irrefl 0 this

theorem sphFold_bijOn
    (hin : ∀ ζ : ℂ, ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin →
      ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ))
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hTU : σ.triangle \ {0} ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det)
    (hFE : ∀ z, σ.sphCoreRadius ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ → F z = σ.sphPreFold z)
    (hinj : InjOn F (σ.triangle \ {0})) (hmaps : MapsTo F (σ.triangle \ {0}) basePlusSeven) :
    BijOn F (σ.triangle \ {0}) basePlusSeven := by
  obtain ⟨hm0, -⟩ := sphCore_consts hs
  have hfar : ∀ i, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → F z = σ.sphPreFold z :=
    fun i z hz hw => hFE z (by linarith [far_core_of_wall_sph hs hin hz hw])
  have hreal : ∀ i, ∀ z ∈ σ.triangle, z ≠ 0 → σ.wallSide i z = 0 → (F z).im = 0 := by
    intro i z hz h0 hw
    rw [hfar i z hz hw]
    exact im_sphPreFold_of_wall hs i hz h0 hw
  have h0far := far_core_of_wall_sph hs hin (zero_mem_triangle_sph hs) (i := 0)
    wallSide_zero_zero_sph
  have hr : ContinuousAt σ.rotTwo 0 := (contDiffAt_rotTwo_sph hs (by simp)).continuousAt
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hr σ.sphCoreMargin hm0
  have hog := (sphParams hs).2.2.2.2.2.2.2.1
  set ρ₀ := min η σ.sphOuterGermRadius with hρ₀
  have hgerm : ∀ z ∈ σ.triangle, 0 < ‖z‖ → ‖z‖ < ρ₀ → F z = compactOuterGerm σ.p₃ z := by
    intro z hz hz0 hzρ
    have hd : dist z 0 < η := by
      rw [dist_zero_right]
      exact lt_of_lt_of_le hzρ (min_le_left _ _)
    have h1 := hηb hd
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_le_norm_sub_add_norm_sub (σ.rotTwo 0) (σ.rotTwo z) σ.sphCoreCenter
    have h3 : ‖σ.rotTwo 0 - σ.rotTwo z‖ = ‖σ.rotTwo z - σ.rotTwo 0‖ := norm_sub_rev _ _
    rw [hFE z (by linarith)]
    exact sphPreFold_eq_outerGerm_of_mem hs hz (norm_pos_iff.1 hz0)
      (lt_of_lt_of_le hzρ (min_le_right _ _))
  exact sphBijOn_of_local hs hU hTU hF (fun z hz h1 h2 => (hdet z hz h1 h2).ne') hreal hinj hmaps
    (by rw [hfar 2 _ (vertexOne_mem_triangle_sph hs) (wallSide_two_vertexOne_sph hs),
      sphPreFold_vertexOne hs])
    (by rw [hfar 2 _ (vertexTwo_mem_triangle_sph hs) (wallSide_two_vertexTwo_sph hs),
      sphPreFold_vertexTwo hs])
    (lt_min hη hog) hgerm

theorem exists_sphFoldCore_bijOn {G : Set ℂ} (hGo : IsOpen G)
    (hGsm : ∀ z ∈ G, ContDiffAt ℝ ∞ σ.sphPreFold z)
    (hGdet : ∀ z ∈ G, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ σ.sphPreFold z).det)
    (hcover : ∀ z ∈ σ.triangle, z ≠ 0 →
      σ.sphCoreRadius - σ.sphCoreMargin ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ → z ∈ G)
    (hin : ∀ ζ : ℂ, ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin →
      ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ))
    (hinj : InjOn σ.sphPreFold (σ.triangle \ {0})) :
    ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧ σ.triangle \ {0} ⊆ U ∧
      (∀ z, z ≠ 0 → z ∈ G → σ.sphCoreRadius < ‖σ.rotTwo z - σ.sphCoreCenter‖ → z ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧
      (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
      (∀ z, σ.sphCoreRadius ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ → F z = σ.sphPreFold z) ∧
      InjOn F (σ.triangle \ {0}) ∧ MapsTo F (σ.triangle \ {0}) basePlusSeven ∧
      BijOn F (σ.triangle \ {0}) basePlusSeven := by
  obtain ⟨F, U, hUo, h0U, hTU, hGU, hF, hdet, hFE, hinjF, hmaps⟩ :=
    exists_sphFoldCore hs hGo hGsm hGdet hcover hin hinj
  exact ⟨F, U, hUo, h0U, hTU, hGU, hF, hdet, hFE, hinjF, hmaps,
    sphFold_bijOn hs hin hUo hTU hF hdet hFE hinjF hmaps⟩

end Spherical

end CompactShape

end GC.Seifert
