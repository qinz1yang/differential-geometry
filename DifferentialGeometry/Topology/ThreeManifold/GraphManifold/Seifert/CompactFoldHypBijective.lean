import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidBijective

/-!
# Bijectivity of the hyperbolic compact fold from local data

Lane CF-H3w, tier 3, curvature `-1` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §6). Template: `CompactFoldEuclidBijective`.

`hypBijOn_of_local` turns the local facts of a fold `F` of a hyperbolic triangle (smooth on an
open set containing `T \ {0}` with nonzero Jacobian off `v₁, v₂`, real on the walls, injective,
`F(T \ {0}) ⊆ basePlusSeven`, `F(v₁) = 3/2`, `F(v₂) = -3/2`, the outer germ on `T` near `v₃ = 0`)
into `BijOn F (T \ {0}) basePlusSeven`, as in the flat case: the image of the open triangle is
open, hence in the open upper half disc, and closed there (the outer germ confines the relevant
preimages to the compact `T ∩ {‖z‖ ≥ δ}`); the real segments come from the intermediate value
theorem along the walls. Walls 0 and 1 are straight segments of the disc model. Wall 2 is a
circular arc, so it is parametrised as the straight segment `s ↦ s · mob v₂ v₁` of the chart
`mob v₂` (`wallTwoPath`): there `rotTwo` is real, so `wallSide 2 = 0`, and the other two side
functions stay nonnegative by the transport of `hpForm` along segments from `v₂`
(`wallSide_mobInv_smul_nonneg`, `wallTwoPath_mem`).

For the fold of `exists_hypFoldCore_layout` the hypotheses are derived (`hypFold_bijOn`): wall
reality from the reflection identities on `hypWallNbhd` and `refl_eq_self`, the vertex values
from `F = hypPreFold` outside the core (`vertexOne_far_core`, `hypPreFold_vertexOne`, …), the
outer germ from `core_separation` and `hypPreFold_eq_outer`. `exists_hypFoldCore_bijOn` packages
the core replacement with its bijectivity.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem hypGerm_wallZero (p : ℕ) {a : ℝ} (ha : 0 < a) :
    compactOuterGerm p (a : ℂ) = ((-(7 / 2 - a ^ p / 2) : ℝ) : ℂ) := by
  have hn : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hq : conj (a : ℂ) / ((a : ℝ) : ℂ) = 1 := by
    rw [Complex.conj_ofReal, div_self (ofReal_ne_zero.2 ha.ne')]
  rw [compactOuterGerm, hn, hq, one_pow, mul_one]
  push_cast
  ring

theorem hypGerm_wallOne (σ : CompactShape) {a : ℝ} (ha : 0 < a) :
    compactOuterGerm σ.p₃ ((a : ℂ) * exp ((σ.θ₃ : ℂ) * I)) =
      ((7 / 2 - a ^ σ.p₃ / 2 : ℝ) : ℂ) := by
  have hn : ‖(a : ℂ) * exp ((σ.θ₃ : ℂ) * I)‖ = a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hc : conj (exp ((σ.θ₃ : ℂ) * I)) = exp (-((σ.θ₃ : ℂ) * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hq : conj ((a : ℂ) * exp ((σ.θ₃ : ℂ) * I)) / ((a : ℝ) : ℂ) =
      exp (-((σ.θ₃ : ℂ) * I)) := by
    rw [map_mul, Complex.conj_ofReal, hc, mul_div_right_comm, div_self (ofReal_ne_zero.2 ha.ne'),
      one_mul]
  have hp : exp (-((σ.θ₃ : ℂ) * I)) ^ σ.p₃ = -1 := by
    rw [← Complex.exp_nat_mul, show (σ.p₃ : ℂ) * -((σ.θ₃ : ℂ) * I) =
      -(((σ.θ₃ * σ.p₃ : ℝ) : ℂ) * I) by push_cast; ring, θ₃_mul, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  rw [compactOuterGerm, hn, hq, hp]
  ring

variable {σ : CompactShape}

section Arc

variable (h : σ.curv = .hyperbolic)
include h

theorem wallSide_mobInv_smul_nonneg (i : Fin 3) {p z : ℂ} (hp : ‖p‖ < 1)
    (hpi : 0 ≤ σ.wallSide i p) (hz : ‖z‖ < 1) (hzi : 0 ≤ σ.wallSide i z) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 0 ≤ σ.wallSide i (mobInv p ((s : ℂ) * mob p z)) := by
  obtain ⟨α, u, hw⟩ := wallSide_eq_hpForm h i
  set Z := mob p z with hZ
  have hZ1 : ‖Z‖ < 1 := norm_mob_lt_one hp hz
  have hsZ : ‖(s : ℂ) * Z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    nlinarith [norm_nonneg Z]
  have hD : 1 + conj p * Z ≠ 0 := one_add_conj_mul_ne_zero hp hZ1
  have hDs : 1 + conj p * ((s : ℂ) * Z) ≠ 0 := one_add_conj_mul_ne_zero hp hsZ
  have hzz : mobInv p Z = z := mobInv_mob_of_norm hp hz
  have e0 := hpForm_mobInv α u hD
  rw [hzz, ← hw] at e0
  have hA : 0 ≤ hpForm α u p := by rw [← hw]; exact hpi
  have hnn : 0 ≤ hpForm (hpForm α u p) (4 * α * conj p + u + conj u * conj p ^ 2) Z := by
    rw [← e0]
    exact mul_nonneg hzi (normSq_nonneg _)
  have es := hpForm_mobInv α u hDs
  rw [← hw] at es
  have hge := hpForm_smul_ge hnn hs0
  have hN : 0 < normSq (1 + conj p * ((s : ℂ) * Z)) := normSq_pos.2 hDs
  have hR : normSq Z < 1 := normSq_lt_one_of_norm_lt hZ1
  have hsR : s * normSq Z < 1 := by nlinarith [normSq_nonneg Z]
  have : 0 ≤ σ.wallSide i (mobInv p ((s : ℂ) * Z)) * normSq (1 + conj p * ((s : ℂ) * Z)) := by
    rw [es]
    exact le_trans (mul_nonneg (mul_nonneg hA (sub_nonneg.2 hs1)) (sub_nonneg.2 hsR.le)) hge
  exact nonneg_of_mul_nonneg_left this hN

def wallTwoPath (σ : CompactShape) (s : ℝ) : ℂ :=
  mobInv σ.vertexTwo ((s : ℂ) * mob σ.vertexTwo σ.vertexOne)

theorem norm_smul_mob_lt_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(s : ℂ) * mob σ.vertexTwo σ.vertexOne‖ < 1 := by
  have := norm_mob_lt_one (norm_vertexTwo_lt_one h) (norm_vertexOne_lt_one h)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  nlinarith [norm_nonneg (mob σ.vertexTwo σ.vertexOne)]

theorem wallTwoPath_mem {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    wallTwoPath σ s ∈ σ.triangle \ {0} ∧ σ.wallSide 2 (wallTwoPath σ s) = 0 := by
  have hv2 := norm_vertexTwo_lt_one h
  have hv1 := norm_vertexOne_lt_one h
  have hW := norm_smul_mob_lt_one h hs0 hs1
  have hn : ‖wallTwoPath σ s‖ < 1 := norm_mobInv_lt_one hv2 hW
  have hw2 : σ.wallSide 2 (wallTwoPath σ s) = 0 := by
    rw [wallSide_two_eq_rotTwo h, rotTwo_eq_mul_mob h, wallTwoPath, mob_mobInv_of_norm hv2 hW,
      show -exp ((σ.θ₂ : ℂ) * I) * ((s : ℂ) * mob σ.vertexTwo σ.vertexOne) =
        (s : ℂ) * (-exp ((σ.θ₂ : ℂ) * I) * mob σ.vertexTwo σ.vertexOne) by ring,
      ← rotTwo_eq_mul_mob h, rotTwo_vertexOne h, ← ofReal_mul, ofReal_im, zero_mul]
  have hT1 := vertexOne_mem_triangle h
  have hT2 := vertexTwo_mem_triangle h
  refine ⟨⟨⟨?_, fun i => ?_⟩, fun h0 => ?_⟩, hw2⟩
  · rw [CompactShape.plane_hyp h, mem_ball_zero_iff]
    exact hn
  · fin_cases i
    · exact wallSide_mobInv_smul_nonneg h 0 hv2 (hT2.2 0) hv1 (hT1.2 0) hs0 hs1
    · exact wallSide_mobInv_smul_nonneg h 1 hv2 (hT2.2 1) hv1 (hT1.2 1) hs0 hs1
    · exact (le_of_eq hw2.symm)
  · rw [mem_singleton_iff] at h0
    rw [h0, wallSide_two_zero h] at hw2
    exact (mul_pos (sideTwoThree_pos h) σ.sin_θ₂_pos).ne' hw2

omit h in
theorem wallTwoPath_zero : wallTwoPath σ 0 = σ.vertexTwo := by
  simp [wallTwoPath, mobInv]

theorem wallTwoPath_one : wallTwoPath σ 1 = σ.vertexOne := by
  rw [wallTwoPath, ofReal_one, one_mul]
  exact mobInv_mob_of_norm (norm_vertexTwo_lt_one h) (norm_vertexOne_lt_one h)

theorem continuousOn_wallTwoPath : ContinuousOn (wallTwoPath σ) (Icc 0 1) := fun _ hs =>
  ((continuousAt_mobInv (norm_vertexTwo_lt_one h) (norm_smul_mob_lt_one h hs.1 hs.2)).comp
    (f := fun s : ℝ => (s : ℂ) * mob σ.vertexTwo σ.vertexOne)
    ((continuous_ofReal.mul continuous_const).continuousAt)).continuousWithinAt

end Arc

section Local

variable (h : σ.curv = .hyperbolic)
include h

theorem hypBijOn_of_local {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hTU : σ.triangle \ {0} ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → (fderiv ℝ F z).det ≠ 0)
    (hreal : ∀ i, ∀ z ∈ σ.triangle, z ≠ 0 → σ.wallSide i z = 0 → (F z).im = 0)
    (hinj : InjOn F (σ.triangle \ {0})) (hmaps : MapsTo F (σ.triangle \ {0}) basePlusSeven)
    (hv1 : F σ.vertexOne = 3 / 2) (hv2 : F σ.vertexTwo = -(3 / 2)) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hgerm : ∀ z ∈ σ.triangle, 0 < ‖z‖ → ‖z‖ < ρ₀ → F z = compactOuterGerm σ.p₃ z) :
    BijOn F (σ.triangle \ {0}) basePlusSeven := by
  have hTi : ∀ z ∈ σ.openTriangle, z ∈ σ.triangle \ {0} := fun z hz =>
    ⟨σ.openTriangle_subset hz, (σ.ne_of_mem_openTriangle hz).1⟩
  have hcont : ∀ z ∈ σ.triangle \ {0}, ContinuousAt F z := fun z hz =>
    (hF.contDiffAt (hU.mem_nhds (hTU hz))).continuousAt
  have hopen : IsOpen (F '' σ.openTriangle) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨-, h1, h2⟩ := σ.ne_of_mem_openTriangle hz
    have hzU := hTU (hTi z hz)
    exact image_mem_nhds_of_det_ne_zero (σ.isOpen_openTriangle.mem_nhds hz)
      (hF.contDiffAt (hU.mem_nhds hzU)) (hdet z hzU h1 h2)
  have hint : ∀ z ∈ σ.openTriangle, F z ∈ openHalfSeven := by
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
  have hclosed : closure (F '' σ.openTriangle) ∩ openHalfSeven ⊆ F '' σ.openTriangle := by
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
      have hz1 := norm_lt_one_of_mem h hz.1
      have hpow : ‖z‖ ^ σ.p₃ ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1.le
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
      (isCompact_triangle h).inter_right (isClosed_le continuous_const continuous_norm)
    have hcomp : IsCompact (F '' K) :=
      hKc.image_of_continuousOn fun z hz => (hcont z (hKsub hz)).continuousWithinAt
    have hv1' : v ∈ closure (N ∩ F '' σ.openTriangle) := hNo.inter_closure ⟨hvN, hvc⟩
    have hv2' : v ∈ F '' K := by
      refine hcomp.isClosed.closure_subset (closure_mono ?_ hv1')
      rintro _ ⟨hwN, z, hz, rfl⟩
      exact ⟨z, hKmem z (hTi z hz) hwN, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := hv2'
    by_cases hzI : z ∈ σ.openTriangle
    · exact ⟨z, hzI, rfl⟩
    · exfalso
      have : ∃ i, σ.wallSide i z = 0 := by
        by_contra hne
        push Not at hne
        exact hzI ⟨hzK.1.1, fun i => lt_of_le_of_ne (hzK.1.2 i) (hne i).symm⟩
      obtain ⟨i, hi⟩ := this
      have := hreal i z hzK.1 (hKsub hzK).2 hi
      linarith
  have hsub : openHalfSeven ⊆ F '' σ.openTriangle := by
    have hc := mem_openTriangle_of_core h (norm_hypCoreCenter_lt_one h)
      (by rw [mob_self, norm_zero]; linarith [hypCore_params h (σ := σ)])
    have hcI : hypCoreCenter σ ∈ σ.openTriangle := ⟨hc.1.1, hc.2⟩
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
  · have hT1 := σ.sideTanOne_pos
    have hT1' : σ.sideTanOne < 1 := sideOneThree_lt_one h
    set a := min (min (ρ₀ / 2) (σ.sideTanOne / 2)) ((7 - 2 * u.re) / 2) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have haρ : a < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have haT : a ≤ σ.sideTanOne / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hau : a ≤ (7 - 2 * u.re) / 2 := min_le_right _ _
    have hpow : a ^ σ.p₃ ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
    set g : ℝ → ℂ := fun s => (s : ℂ) * exp ((σ.θ₃ : ℂ) * I) with hg
    have hgc : ContinuousOn g (Icc a σ.sideTanOne) := by fun_prop
    have hgm : ∀ s ∈ Icc a σ.sideTanOne, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 1 (g s) = 0 := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
      refine ⟨⟨σ.ray_mem_triangle hs0.le hs.2, fun h0 => ?_⟩, ?_⟩
      · rw [mem_singleton_iff] at h0
        have := σ.norm_ray hs0.le
        change ‖g s‖ = s at this
        rw [h0, norm_zero] at this
        linarith
      · rw [σ.wallSide_one_eq, hg, σ.ray_re, σ.ray_im]
        ring
    have hnt : ‖g a‖ = a := σ.norm_ray ha0.le
    have hFt : (F (g a)).re = 7 / 2 - a ^ σ.p₃ / 2 := by
      rw [hgerm _ (hgm a ⟨le_rfl, by linarith⟩).1.1 (by rw [hnt]; exact ha0)
        (by rw [hnt]; exact haρ), hg, hypGerm_wallOne σ ha0, ofReal_re]
    have hF1 : (F (g σ.sideTanOne)).re = 3 / 2 := by
      rw [hg]
      dsimp only
      rw [← σ.vertexOne_eq_ray, hv1]
      norm_num
    obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc' (by linarith : a ≤ σ.sideTanOne)
      (hcomp hgc fun s hs => (hgm s hs).1)
      (show u.re ∈ Icc (F (g σ.sideTanOne)).re (F (g a)).re from
        ⟨by rw [hF1]; exact h1, by rw [hFt]; linarith⟩)
    refine ⟨g s, (hgm s hs).1, ?_⟩
    have hsu' : (F (g s)).re = u.re := hsu
    rw [hreal' 1 _ (hgm s hs).1 (hgm s hs).2, hsu', ← hue]
  rcases le_or_gt u.re (-(3 / 2)) with h2 | h2
  · have hT2 := σ.sideTanTwo_pos
    have hT2' : σ.sideTanTwo < 1 := sideTwoThree_lt_one h
    set a := min (min (ρ₀ / 2) (σ.sideTanTwo / 2)) ((7 + 2 * u.re) / 2) with ha
    have ha0 : 0 < a := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have haρ : a < ρ₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have haT : a ≤ σ.sideTanTwo / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hau : a ≤ (7 + 2 * u.re) / 2 := min_le_right _ _
    have hpow : a ^ σ.p₃ ≤ a := pow_le_of_le_one ha0.le (by linarith) (by omega)
    set g : ℝ → ℂ := fun s => (s : ℂ) with hg
    have hgc : ContinuousOn g (Icc a σ.sideTanTwo) := by fun_prop
    have hgm : ∀ s ∈ Icc a σ.sideTanTwo, g s ∈ σ.triangle \ {0} ∧ σ.wallSide 0 (g s) = 0 := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
      refine ⟨⟨σ.real_mem_triangle hs0.le hs.2, fun h0 => ?_⟩, ?_⟩
      · rw [mem_singleton_iff, hg] at h0
        exact hs0.ne' (ofReal_eq_zero.1 h0)
      · rw [σ.wallSide_zero_eq, hg, ofReal_im]
    have hnt : ‖g a‖ = a := by
      rw [hg]
      dsimp only
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    have hFt : (F (g a)).re = -(7 / 2 - a ^ σ.p₃ / 2) := by
      rw [hgerm _ (hgm a ⟨le_rfl, by linarith⟩).1.1 (by rw [hnt]; exact ha0)
        (by rw [hnt]; exact haρ), hg, hypGerm_wallZero σ.p₃ ha0, ofReal_re]
    have hF1 : (F (g σ.sideTanTwo)).re = -(3 / 2) := by
      rw [hg]
      dsimp only
      rw [← σ.vertexTwo_eq_real, hv2]
      norm_num
    obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc (by linarith : a ≤ σ.sideTanTwo)
      (hcomp hgc fun s hs => (hgm s hs).1)
      (show u.re ∈ Icc (F (g a)).re (F (g σ.sideTanTwo)).re from
        ⟨by rw [hFt]; linarith, by rw [hF1]; exact h2⟩)
    refine ⟨g s, (hgm s hs).1, ?_⟩
    have hsu' : (F (g s)).re = u.re := hsu
    rw [hreal' 0 _ (hgm s hs).1 (hgm s hs).2, hsu', ← hue]
  have hgm : ∀ s ∈ Icc (0 : ℝ) 1, wallTwoPath σ s ∈ σ.triangle \ {0} ∧
      σ.wallSide 2 (wallTwoPath σ s) = 0 := fun s hs => wallTwoPath_mem h hs.1 hs.2
  have hF0 : (F (wallTwoPath σ 0)).re = -(3 / 2) := by
    rw [wallTwoPath_zero, hv2]
    norm_num
  have hF1 : (F (wallTwoPath σ 1)).re = 3 / 2 := by
    rw [wallTwoPath_one h, hv1]
    norm_num
  obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc zero_le_one
    (hcomp (continuousOn_wallTwoPath h) fun s hs => (hgm s hs).1)
    (show u.re ∈ Icc (F (wallTwoPath σ 0)).re (F (wallTwoPath σ 1)).re from
      ⟨by rw [hF0]; exact h2.le, by rw [hF1]; exact h1.le⟩)
  refine ⟨wallTwoPath σ s, (hgm s hs).1, ?_⟩
  have hsu' : (F (wallTwoPath σ s)).re = u.re := hsu
  rw [hreal' 2 _ (hgm s hs).1 (hgm s hs).2, hsu', ← hue]

theorem vertexOne_far_core : hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) σ.vertexOne‖ := by
  by_contra hc
  push Not at hc
  have := (mem_openTriangle_of_core h (norm_vertexOne_lt_one h)
    (by linarith [hypCore_params h (σ := σ)])).2 2
  rw [wallSide_two_vertexOne h] at this
  exact lt_irrefl 0 this

theorem vertexTwo_far_core : hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) σ.vertexTwo‖ := by
  by_contra hc
  push Not at hc
  have := (mem_openTriangle_of_core h (norm_vertexTwo_lt_one h)
    (by linarith [hypCore_params h (σ := σ)])).2 2
  rw [wallSide_two_vertexTwo h] at this
  exact lt_irrefl 0 this

theorem hypPreFold_vertexOne : hypPreFold σ (hypLayout σ) σ.vertexOne = 3 / 2 := by
  have hg := (hypLayout_params h (σ := σ)).1
  have h0 : hd σ 0 σ.vertexOne < (hypLayout σ).g := by
    change ‖mob σ.vertexOne σ.vertexOne‖ < _
    rw [mob_self, norm_zero]
    exact hg
  have hr : σ.rotOne σ.vertexOne = 0 := by rw [rotOne_eq_mul_mob h, mob_self, mul_zero]
  unfold hypPreFold
  rw [ite_eq_left h0, hr, zero_pow (by have := σ.two_le_p₁; omega)]
  ring

theorem hypPreFold_vertexTwo : hypPreFold σ (hypLayout σ) σ.vertexTwo = -(3 / 2) := by
  obtain ⟨hg, hga, hab, hb1, he, hc1, -⟩ := hypLayout_params h (σ := σ)
  have h0 : ¬ hd σ 0 σ.vertexTwo < (hypLayout σ).g := not_lt.2 (lt_hd_of_canon_nonneg h 0
    (by rw [canon_zero_vertexTwo h]; exact (tauTwo_pos h).le) (hga.trans hab) hb1 he hc1).le
  have h1 : hd σ 1 σ.vertexTwo < (hypLayout σ).g := by
    change ‖mob σ.vertexTwo σ.vertexTwo‖ < _
    rw [mob_self, norm_zero]
    exact hg
  unfold hypPreFold
  rw [ite_eq_right h0, ite_eq_left h1, rotTwo_vertexTwo h,
    zero_pow (by have := σ.two_le_p₂; omega)]
  ring

theorem hypFold_bijOn {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hTU : σ.triangle \ {0} ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det)
    (hFE : ∀ z, hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) z‖ →
      F z = hypPreFold σ (hypLayout σ) z)
    (hrefl : ∀ i, ∀ z ∈ hypWallNbhd σ (hypLayout σ) i, F (σ.refl i z) = conj (F z))
    (hinj : InjOn F (σ.triangle \ {0})) (hmaps : MapsTo F (σ.triangle \ {0}) basePlusSeven) :
    BijOn F (σ.triangle \ {0}) basePlusSeven := by
  obtain ⟨hg0, hga, hab, hb1, he, hc1, hc2, hβ0, hβ, hs1, hs2, hg₃0, hg₃a, ha₃, hb₃, -⟩ :=
    hypLayout_params h (σ := σ)
  have hreal : ∀ i, ∀ z ∈ σ.triangle, z ≠ 0 → σ.wallSide i z = 0 → (F z).im = 0 := by
    intro i z hz h0 hw
    have hV := foldWall_diff_subset_hypWallNbhd h hg0 hga hab hb1 he hc1 hc2 hβ0 hs1 hs2 hg₃a
      ha₃ hb₃ i ⟨⟨hz, hw⟩, h0⟩
    have e := hrefl i z hV
    rw [refl_eq_self h i (norm_lt_one_of_mem h hz) hw] at e
    exact Complex.conj_eq_iff_im.1 e.symm
  have hgerm : ∀ z ∈ σ.triangle, 0 < ‖z‖ → ‖z‖ < (hypLayout σ).g₃ →
      F z = compactOuterGerm σ.p₃ z := by
    intro z hz _ hzg
    have hfar : hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) z‖ := by
      by_contra hc
      push Not at hc
      have := (core_separation h (norm_lt_one_of_mem h hz) hc).2.2.2.2
      linarith
    rw [hFE z hfar]
    exact hypPreFold_eq_outer h (hga.trans hab) hb1 he hc1 hc2 ((hg₃a.trans ha₃).trans hb₃) hz hzg
  exact hypBijOn_of_local h hU hTU hF (fun z hz h1 h2 => (hdet z hz h1 h2).ne') hreal hinj hmaps
    (by rw [hFE _ (vertexOne_far_core h), hypPreFold_vertexOne h])
    (by rw [hFE _ (vertexTwo_far_core h), hypPreFold_vertexTwo h]) hg₃0 hgerm

theorem exists_hypFoldCore_bijOn {G : Set ℂ} (hGo : IsOpen G) (hGd : ∀ z ∈ G, ‖z‖ < 1)
    (hGT : ∀ z ∈ σ.triangle, z ≠ 0 →
      hypCoreRadius σ - hypCoreMargin σ < ‖mob (hypCoreCenter σ) z‖ → z ∈ G)
    (hEs : ∀ z ∈ G, ContDiffAt ℝ ∞ (hypPreFold σ (hypLayout σ)) z)
    (hEd : ∀ z ∈ G, z ≠ σ.vertexOne → z ≠ σ.vertexTwo →
      0 < (fderiv ℝ (hypPreFold σ (hypLayout σ)) z).det)
    (hinj : InjOn (hypPreFold σ (hypLayout σ)) (σ.triangle \ {0})) :
    ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧ (∀ z ∈ U, ‖z‖ < 1) ∧
      σ.triangle \ {0} ⊆ U ∧
      (∀ z ∈ G, z ≠ 0 → hypCoreRadius σ < ‖mob (hypCoreCenter σ) z‖ → z ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧
      (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
      (∀ z, hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) z‖ → F z = hypPreFold σ (hypLayout σ) z) ∧
      (∀ i, ∀ z ∈ hypWallNbhd σ (hypLayout σ) i, F (σ.refl i z) = conj (F z)) ∧
      BijOn F (σ.triangle \ {0}) basePlusSeven := by
  obtain ⟨F, U, hUo, h0U, hUd, hTU, hGU, hF, hdet, hFE, hrefl, hinjF, hmaps⟩ :=
    exists_hypFoldCore_layout h hGo hGd hGT hEs hEd hinj
  exact ⟨F, U, hUo, h0U, hUd, hTU, hGU, hF, hdet, hFE, hrefl,
    hypFold_bijOn h hUo hTU hF hdet hFE hrefl hinjF hmaps⟩

end Local

end HypFold

end GC.Seifert
