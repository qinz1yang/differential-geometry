import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGenericShape
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldTopology

/-!
# Wall images and the sign of a compact fold, for every curvature

Lane CF, tier 4 (design `docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§0 and §7; the generic deliverables of `CompactFoldSpec`, with the statements requested by lane
B3 for its curved families). For any `σ : CompactShape` and any fold datum `D : σ.FoldData`:
* `f v₁ = 3/2`, `f v₂ = -3/2` (`f_vertexOne`, `f_vertexTwo`: the vertices lie in their apex
  discs, where `f` is the apex model, and the rotated disc coordinate vanishes there);
* `f` is real on the walls minus `v₃ = 0` (`im_f_of_wall`, from the reflection identity and
  `σ.refl_eq_self`) and has positive imaginary part on the open triangle (`im_f_pos`: the image of
  the open triangle is open by the inverse function theorem and lies in `Im ≥ 0`), so a point of
  `T \ {0}` with real image lies on a wall (`wall_of_im_f_eq_zero`);
* the open walls go to three disjoint real segments: wall `1` into `(3/2, 7/2)`, wall `0` into
  `(-7/2, -3/2)`, wall `2` into `(-3/2, 3/2)` (`re_f_wallOne`, `re_f_wallZero`,
  `re_f_wallTwo`). Walls `1` and `0` are the segments `[0, v₁]`, `[0, v₂]`
  (`CompactFoldGenericShape`); near `0` the fold is the outer germ, real of modulus
  `7/2 - t^{p₃}/2` on both, so every value between `±3/2` and `±7/2` is attained on them by the
  intermediate value theorem (`exists_ray_eq`, `exists_real_eq`), and injectivity of `f` on
  `T \ {0}` together with `f v₁ = 3/2`, `f v₂ = -3/2` and the wall intersections
  `wall 1 ∩ wall 2 = {v₁}`, `wall 0 ∩ wall 2 = {v₂}` places each wall in its segment.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem im_pos_of_mem_nhds {u : ℂ} (h : {v : ℂ | 0 ≤ v.im} ∈ 𝓝 u) : 0 < u.im := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h
  by_contra hle
  push Not at hle
  have hmem : u - ((ε / 2 : ℝ) : ℂ) * I ∈ Metric.ball u ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have := hball hmem
  change 0 ≤ (u - ((ε / 2 : ℝ) : ℂ) * I).im at this
  simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
    add_zero] at this
  linarith

theorem outerGerm_ray {p : ℕ} {θ : ℝ} (hθ : θ * p = Real.pi) {a : ℝ} (ha : 0 < a) :
    compactOuterGerm p ((a : ℂ) * exp ((θ : ℂ) * I)) = ((7 / 2 - a ^ p / 2 : ℝ) : ℂ) := by
  have hn : ‖(a : ℂ) * exp ((θ : ℂ) * I)‖ = a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hc : conj (exp ((θ : ℂ) * I)) = exp (-((θ : ℂ) * I)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hq : conj ((a : ℂ) * exp ((θ : ℂ) * I)) / ((a : ℝ) : ℂ) = exp (-((θ : ℂ) * I)) := by
    rw [map_mul, Complex.conj_ofReal, hc, mul_div_right_comm, div_self (ofReal_ne_zero.2 ha.ne'),
      one_mul]
  have hp : exp (-((θ : ℂ) * I)) ^ p = -1 := by
    rw [← Complex.exp_nat_mul, show (p : ℂ) * -((θ : ℂ) * I) =
      -(((θ * p : ℝ) : ℂ) * I) by push_cast; ring, hθ, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [compactOuterGerm, hn, hq, hp]
  ring

theorem outerGerm_real (p : ℕ) {a : ℝ} (ha : 0 < a) :
    compactOuterGerm p (a : ℂ) = ((-(7 / 2 - a ^ p / 2) : ℝ) : ℂ) := by
  have hn : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hq : conj (a : ℂ) / ((a : ℝ) : ℂ) = 1 := by
    rw [Complex.conj_ofReal, div_self (ofReal_ne_zero.2 ha.ne')]
  rw [compactOuterGerm, hn, hq, one_pow, mul_one]
  push_cast
  ring

namespace CompactShape

variable {σ : CompactShape}

theorem disc_self (v : ℂ) : σ.disc v v = 0 := by
  rw [disc, sub_self, zero_div]

theorem mem_apexDisc_self {v : ℂ} (hv : σ.eps * ‖v‖ ^ 2 < 1) {r : ℝ} (hr : 0 < r) :
    v ∈ σ.apexDisc v r := by
  refine ⟨?_, by rw [disc_self, norm_zero]; exact hr⟩
  have e : (σ.eps : ℂ) * conj v * v = ((σ.eps * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e, ← ofReal_one, ← ofReal_sub, Ne, ofReal_eq_zero]
  linarith

theorem vertexOne_mem_plane : σ.eps * ‖σ.vertexOne‖ ^ 2 < 1 := by
  rw [σ.norm_vertexOne]
  exact σ.eps_sideTanOne_sq_lt

theorem vertexTwo_mem_plane : σ.eps * ‖σ.vertexTwo‖ ^ 2 < 1 := by
  rw [vertexTwo_eq_real, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact σ.eps_sideTanTwo_sq_lt

theorem vertexOne_mem_diff : σ.vertexOne ∈ σ.triangle \ {0} :=
  ⟨σ.vertexOne_mem_triangle, σ.vertexOne_ne_zero⟩

theorem vertexTwo_mem_diff : σ.vertexTwo ∈ σ.triangle \ {0} :=
  ⟨σ.vertexTwo_mem_triangle, σ.vertexTwo_ne_zero⟩

theorem ray_mem_foldWall {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ σ.sideTanOne) :
    (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) ∈ σ.foldWall 1 := by
  refine ⟨σ.ray_mem_triangle ht0 ht, ?_⟩
  rw [wallSide_one_eq, ray_re, ray_im]
  ring

theorem real_mem_foldWall {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ σ.sideTanTwo) :
    (x : ℂ) ∈ σ.foldWall 0 :=
  ⟨σ.real_mem_triangle hx0 hx, by rw [wallSide_zero_eq, ofReal_im]⟩

theorem ray_ne_zero {t : ℝ} (ht : 0 < t) : (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.2 ht.ne') (Complex.exp_ne_zero _)

theorem wallSide_two_zero : σ.wallSide 2 0 = Real.sin σ.θ₂ * σ.sideTanTwo := by
  have h := σ.wallSide_two_real 0
  rw [ofReal_zero] at h
  rw [h]
  ring

namespace FoldData

variable (D : σ.FoldData)

theorem continuousAt_f {z : ℂ} (hz : z ∈ σ.triangle \ {0}) : ContinuousAt D.f z :=
  D.contDiffOn_f.continuousOn.continuousAt (D.isOpen_U.mem_nhds (D.triangle_diff_subset_U hz))

theorem f_vertexOne : D.f σ.vertexOne = 3 / 2 := by
  rw [(D.f_apexOne _ (mem_apexDisc_self vertexOne_mem_plane (D.apexRadius_pos 0))).2, rotOne,
    disc_self, mul_zero, neg_zero, zero_pow (by have := σ.two_le_p₁; omega)]
  norm_num

theorem f_vertexTwo : D.f σ.vertexTwo = -(3 / 2) := by
  rw [(D.f_apexTwo _ (mem_apexDisc_self vertexTwo_mem_plane (D.apexRadius_pos 1))).2, rotTwo,
    disc_self, mul_zero, neg_zero, zero_pow (by have := σ.two_le_p₂; omega)]
  norm_num

theorem im_f_of_wall {i : Fin 3} {z : ℂ} (hz : z ∈ σ.foldWall i) (h0 : z ≠ 0) :
    (D.f z).im = 0 := by
  have hV := D.foldWall_diff_subset_V i ⟨hz, h0⟩
  have h := D.f_refl i z hV
  rw [σ.refl_eq_self (D.V_subset_reflChart i hV) hz.2] at h
  exact Complex.conj_eq_iff_im.1 h.symm

theorem eq_re_of_wall {i : Fin 3} {z : ℂ} (hz : z ∈ σ.foldWall i) (h0 : z ≠ 0) :
    D.f z = ((D.f z).re : ℂ) :=
  Complex.ext (by simp) (by rw [ofReal_im]; exact D.im_f_of_wall hz h0)

theorem im_f_pos {z : ℂ} (hz : z ∈ σ.plane) (h : ∀ i, 0 < σ.wallSide i z) :
    0 < (D.f z).im := by
  have hO : z ∈ σ.openTriangle := ⟨hz, h⟩
  obtain ⟨h0, h1, h2⟩ := σ.ne_of_mem_openTriangle hO
  have hT : z ∈ σ.triangle \ {0} := ⟨σ.openTriangle_subset hO, h0⟩
  have hzU := D.triangle_diff_subset_U hT
  have himg := image_mem_nhds_of_det_ne_zero (σ.isOpen_openTriangle.mem_nhds hO)
    (D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds hzU)) (D.det_fderiv_pos z hzU h1 h2).ne'
  refine im_pos_of_mem_nhds (Filter.mem_of_superset himg ?_)
  rintro _ ⟨w, hw, rfl⟩
  have hw0 := (σ.ne_of_mem_openTriangle hw).1
  exact (D.bijOn_f.mapsTo ⟨σ.openTriangle_subset hw, hw0⟩).2

theorem wall_of_im_f_eq_zero {z : ℂ} (hz : z ∈ σ.triangle) (_h0 : z ≠ 0)
    (h : (D.f z).im = 0) : ∃ i, σ.wallSide i z = 0 := by
  by_contra hne
  push Not at hne
  have := D.im_f_pos hz.1 fun i => lt_of_le_of_ne (hz.2 i) (hne i).symm
  linarith

theorem abs_re_f_lt {z : ℂ} (hz : z ∈ σ.triangle \ {0}) : |(D.f z).re| < 7 / 2 :=
  lt_of_le_of_lt (Complex.abs_re_le_norm _) (D.bijOn_f.mapsTo hz).1

theorem eq_of_f_eq {z w : ℂ} (hz : z ∈ σ.triangle \ {0}) (hw : w ∈ σ.triangle \ {0})
    (h : D.f z = D.f w) : z = w :=
  D.bijOn_f.injOn hz hw h

theorem small_param {R r c : ℝ} (hR : 0 < R) (hr : 0 < r) (hc : 0 < c) (p : ℕ) (hp : 1 ≤ p) :
    ∃ a : ℝ, 0 < a ∧ a < R ∧ a ≤ r ∧ a ^ p ≤ c := by
  set a := min (min (R / 2) (1 / 2)) (min c r) with ha
  have ha0 : 0 < a := lt_min (lt_min (by linarith) (by norm_num)) (lt_min hc hr)
  have ha1 : a ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hpow : a ^ p ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
  exact ⟨a, ha0, lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith),
    le_trans (min_le_right _ _) (min_le_right _ _),
    le_trans hpow (le_trans (min_le_right _ _) (min_le_left _ _))⟩

theorem exists_ray_eq {r u : ℝ} (hr0 : 0 < r) (hr : r ≤ σ.sideTanOne)
    (hu : (D.f ((r : ℂ) * exp ((σ.θ₃ : ℂ) * I))).re ≤ u) (hu7 : u < 7 / 2) :
    ∃ t : ℝ, 0 < t ∧ t ≤ r ∧ (D.f ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I))).re = u := by
  obtain ⟨a, ha0, haR, har, hap⟩ := small_param (D.apexRadius_pos 2) hr0
    (by linarith : 0 < 7 - 2 * u) σ.p₃ (by have := σ.two_le_p₃; omega)
  set γ : ℝ → ℂ := fun t => (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) with hγ
  have hmem : ∀ t ∈ Icc a r, γ t ∈ σ.triangle \ {0} := fun t ht =>
    ⟨σ.ray_mem_triangle (by linarith [ht.1]) (by linarith [ht.2]),
      σ.ray_ne_zero (by linarith [ht.1])⟩
  have hcont : ContinuousOn (fun t => (D.f (γ t)).re) (Icc a r) := fun t ht =>
    (Complex.continuous_re.continuousAt.comp ((D.continuousAt_f (hmem t ht)).comp
      (by fun_prop : Continuous γ).continuousAt)).continuousWithinAt
  have hga : (D.f (γ a)).re = 7 / 2 - a ^ σ.p₃ / 2 := by
    have hn : ‖γ a‖ = a := σ.norm_ray ha0.le
    rw [(D.f_outer (γ a) (by rw [hn]; exact ha0) (by rw [hn]; exact haR)).2, hγ,
      outerGerm_ray σ.θ₃_mul ha0, ofReal_re]
  obtain ⟨t, ht, htu⟩ := intermediate_value_Icc' har hcont
    (show u ∈ Icc (D.f (γ r)).re (D.f (γ a)).re from ⟨hu, by rw [hga]; linarith⟩)
  exact ⟨t, by linarith [ht.1], ht.2, htu⟩

theorem exists_real_eq {r u : ℝ} (hr0 : 0 < r) (hr : r ≤ σ.sideTanTwo)
    (hu : u ≤ (D.f (r : ℂ)).re) (hu7 : -(7 / 2) < u) :
    ∃ x : ℝ, 0 < x ∧ x ≤ r ∧ (D.f (x : ℂ)).re = u := by
  obtain ⟨a, ha0, haR, har, hap⟩ := small_param (D.apexRadius_pos 2) hr0
    (by linarith : 0 < 7 + 2 * u) σ.p₃ (by have := σ.two_le_p₃; omega)
  have hmem : ∀ x ∈ Icc a r, (x : ℂ) ∈ σ.triangle \ {0} := fun x hx =>
    ⟨σ.real_mem_triangle (by linarith [hx.1]) (by linarith [hx.2]),
      ofReal_ne_zero.2 (by linarith [hx.1])⟩
  have hcont : ContinuousOn (fun x : ℝ => (D.f (x : ℂ)).re) (Icc a r) := fun x hx =>
    (Complex.continuous_re.continuousAt.comp ((D.continuousAt_f (hmem x hx)).comp
      Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hga : (D.f (a : ℂ)).re = -(7 / 2 - a ^ σ.p₃ / 2) := by
    have hn : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    rw [(D.f_outer (a : ℂ) (by rw [hn]; exact ha0) (by rw [hn]; exact haR)).2,
      outerGerm_real _ ha0, ofReal_re]
  obtain ⟨x, hx, hxu⟩ := intermediate_value_Icc har hcont
    (show u ∈ Icc (D.f (a : ℂ)).re (D.f (r : ℂ)).re from ⟨by rw [hga]; linarith, hu⟩)
  exact ⟨x, by linarith [hx.1], hx.2, hxu⟩

theorem re_f_wallOne {z : ℂ} (hz : z ∈ σ.foldWall 1) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    3 / 2 < (D.f z).re ∧ (D.f z).re < 7 / 2 := by
  refine ⟨?_, (abs_lt.1 (D.abs_re_f_lt ⟨hz.1, h0⟩)).2⟩
  obtain ⟨r, hr0, hr1, rfl⟩ := σ.eq_ray_of_wallOne hz.1 hz.2
  have hr : 0 < r := lt_of_le_of_ne hr0 fun h => h0 (by rw [← h, ofReal_zero, zero_mul])
  have hrt : r < σ.sideTanOne := lt_of_le_of_ne hr1 fun h => h1 (by rw [h, vertexOne_eq_ray])
  by_contra hle
  push Not at hle
  obtain ⟨t, ht0, htr, htu⟩ := D.exists_ray_eq hr hr1 hle (by norm_num)
  have htT : (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) ∈ σ.triangle \ {0} :=
    ⟨σ.ray_mem_triangle ht0.le (by linarith), σ.ray_ne_zero ht0⟩
  have hft : D.f ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) = D.f σ.vertexOne := by
    rw [D.eq_re_of_wall (σ.ray_mem_foldWall ht0.le (by linarith)) (σ.ray_ne_zero ht0), htu,
      D.f_vertexOne]
    norm_num
  have he := D.eq_of_f_eq htT vertexOne_mem_diff hft
  have hn := congrArg norm he
  rw [σ.norm_ray ht0.le, σ.norm_vertexOne] at hn
  linarith

theorem re_f_wallZero {z : ℂ} (hz : z ∈ σ.foldWall 0) (h0 : z ≠ 0) (h2 : z ≠ σ.vertexTwo) :
    -(7 / 2) < (D.f z).re ∧ (D.f z).re < -(3 / 2) := by
  refine ⟨(abs_lt.1 (D.abs_re_f_lt ⟨hz.1, h0⟩)).1, ?_⟩
  obtain ⟨r, hr0, hr1, rfl⟩ := σ.eq_real_of_wallZero hz.1 hz.2
  have hr : 0 < r := lt_of_le_of_ne hr0 fun h => h0 (by rw [← h, ofReal_zero])
  have hrt : r < σ.sideTanTwo := lt_of_le_of_ne hr1 fun h => h2 (by rw [h, vertexTwo_eq_real])
  by_contra hle
  push Not at hle
  obtain ⟨x, hx0, hxr, hxu⟩ := D.exists_real_eq hr hr1 hle (by norm_num)
  have hxT : (x : ℂ) ∈ σ.triangle \ {0} :=
    ⟨σ.real_mem_triangle hx0.le (by linarith), ofReal_ne_zero.2 hx0.ne'⟩
  have hfx : D.f (x : ℂ) = D.f σ.vertexTwo := by
    rw [D.eq_re_of_wall (σ.real_mem_foldWall hx0.le (by linarith)) (ofReal_ne_zero.2 hx0.ne'),
      hxu, D.f_vertexTwo]
    norm_num
  have he := D.eq_of_f_eq hxT vertexTwo_mem_diff hfx
  rw [vertexTwo_eq_real, ofReal_inj] at he
  linarith

theorem re_f_wallTwo {z : ℂ} (hz : z ∈ σ.foldWall 2) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : -(3 / 2) < (D.f z).re ∧ (D.f z).re < 3 / 2 := by
  have h0 : z ≠ 0 := by
    rintro rfl
    have := hz.2
    rw [wallSide_two_zero] at this
    exact (mul_pos σ.sin_θ₂_pos σ.sideTanTwo_pos).ne' this
  have hzT : z ∈ σ.triangle \ {0} := ⟨hz.1, h0⟩
  have hfz := D.eq_re_of_wall hz h0
  have hb := abs_lt.1 (D.abs_re_f_lt hzT)
  constructor
  · by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨x, hx0, hxr, hxu⟩ := D.exists_real_eq σ.sideTanTwo_pos le_rfl
        (by rw [← vertexTwo_eq_real, D.f_vertexTwo]; norm_num; exact hlt.le) hb.1
      have hxW := σ.real_mem_foldWall hx0.le hxr
      have hxT : (x : ℂ) ∈ σ.triangle \ {0} := ⟨hxW.1, ofReal_ne_zero.2 hx0.ne'⟩
      have he := D.eq_of_f_eq hxT hzT (by
        rw [D.eq_re_of_wall hxW (ofReal_ne_zero.2 hx0.ne'), hxu, ← hfz])
      exact h2 (σ.eq_vertexTwo_of_wallZero hz.1 (he ▸ hxW.2) hz.2)
    · exact h2 (D.eq_of_f_eq hzT vertexTwo_mem_diff (by rw [hfz, heq, D.f_vertexTwo]; norm_num))
  · by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨t, ht0, htr, htu⟩ := D.exists_ray_eq σ.sideTanOne_pos le_rfl
        (by rw [← vertexOne_eq_ray, D.f_vertexOne]; norm_num; exact hlt.le) hb.2
      have htW := σ.ray_mem_foldWall ht0.le htr
      have htT : (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) ∈ σ.triangle \ {0} :=
        ⟨htW.1, σ.ray_ne_zero ht0⟩
      have he := D.eq_of_f_eq htT hzT (by
        rw [D.eq_re_of_wall htW (σ.ray_ne_zero ht0), htu, ← hfz])
      exact h1 (σ.eq_vertexOne_of_wallOne hz.1 (he ▸ htW.2) hz.2)
    · exact h1 (D.eq_of_f_eq hzT vertexOne_mem_diff (by rw [hfz, ← heq, D.f_vertexOne]; norm_num))

end FoldData

end CompactShape

end GC.Seifert
