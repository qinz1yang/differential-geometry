import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldInjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCoreJordan

/-!
# The K16f fold with its core replaced by a diffeomorphism

Packet K16f, tier 2 (Jordan core step, design D13 §7–§8). On the open annulus
`1/10 - 1/250 < ‖z - foldCenter‖ < 1/10 + 1/250` the fold `foldMap` is a smooth injective map
with nonzero Jacobian, and the outward ray from `foldMap z₀`, `z₀ = foldCenter + (51/500) i`,
misses the image of the core circle, whose points have modulus at most `foldRho (47/100)`
(`norm_foldMap_sphere_le`). `exists_core_replacement` gives a plane diffeomorphism `Q` equal to
`foldMap` near the circle; `exists_foldCore` sets `F = Q` on the open core disc and `F = foldMap`
elsewhere. `Q` maps the core disc into the open upper half `foldPantsUpper` of the pants, since
every point outside it lies on an unbounded ray missing that half (`foldMap_outside_ray`), and
it misses the image of the rest of the triangle, since every such image point lies on the image
of a three-segment path ending high in the cusp `∞` followed by an outward ray
(`exists_unbounded_of_outside`). Hence `F` is smooth with nonzero Jacobian on the upper
half-plane, injective on the triangle and maps it into `pantsPlus`, its interior into
`foldPantsUpper`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Topology

namespace GC.Seifert

theorem sq_lt_of_norm_sub_foldCenter_gt {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : a < ‖z - foldCenter‖) :
    a ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2 := by
  rw [← norm_sub_foldCenter_sq]
  exact pow_lt_pow_left₀ h ha (by norm_num)

theorem sq_le_of_norm_sub_foldCenter_le {z : ℂ} {a : ℝ} (h : ‖z - foldCenter‖ ≤ a) :
    (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2 ≤ a ^ 2 := by
  rw [← norm_sub_foldCenter_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem mem_triangleInterior_of_norm_lt {z : ℂ} (h : ‖z - foldCenter‖ < 13 / 125) :
    z ∈ triangleInterior := by
  have h2 := sq_le_of_norm_sub_foldCenter_le h.le
  have hre : |z.re - 1 / 4| ≤ 13 / 125 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 13 / 125)]
    exact sq_le_sq.1 (by nlinarith [sq_nonneg (z.im - 37 / 100)])
  have him : |z.im - 37 / 100| ≤ 13 / 125 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 13 / 125)]
    exact sq_le_sq.1 (by nlinarith [sq_nonneg (z.re - 1 / 4)])
  obtain ⟨a1, a2⟩ := abs_le.1 hre
  obtain ⟨b1, b2⟩ := abs_le.1 him
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  unfold wallTwo
  nlinarith

theorem wallTwo_ge_of_norm_le {z : ℂ} (h : ‖z - foldCenter‖ ≤ 1 / 10) :
    1 / 100 ≤ wallTwo z.re z.im := by
  have h2 := sq_le_of_norm_sub_foldCenter_le h
  have him : |z.im - 37 / 100| ≤ 1 / 10 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
    exact sq_le_sq.1 (by nlinarith [sq_nonneg (z.re - 1 / 4)])
  obtain ⟨b1, b2⟩ := abs_le.1 him
  unfold wallTwo
  nlinarith [sq_nonneg (z.re - 1 / 4)]

theorem im_le_of_norm_le {z : ℂ} (h : ‖z - foldCenter‖ ≤ 1 / 10) : z.im ≤ 47 / 100 := by
  have h2 := sq_le_of_norm_sub_foldCenter_le h
  have him : |z.im - 37 / 100| ≤ 1 / 10 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
    exact sq_le_sq.1 (by nlinarith [sq_nonneg (z.re - 1 / 4)])
  linarith [(abs_le.1 him).2]

theorem norm_foldMap_le {z : ℂ} (hz : z ∈ triangleSet) (hy : z.im ≤ 47 / 100) :
    ‖foldMap z‖ ≤ foldRho (47 / 100) := by
  have hy0 := hz.1
  have hb : bridgeRho (11 / 25) ≤ foldRho (47 / 100) := by
    rw [foldRho_eq_bridgeRho (by norm_num)]
    exact (strictMonoOn_bridgeRho (show (11 / 25 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show (47 / 100 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)).le
  have hs := bridgeSigma_add_lt_bridgeRho
  have hσ := bridgeSigma_three_fifths_lt
  have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
  have h2 : 2 < foldRho (47 / 100) := two_lt_foldRho (by norm_num)
  by_cases h0 : 3 / 5 < heightOne z.re z.im
  · rw [foldMap_of_heightOne h0]
    have hn := norm_cornerZero_sub z
    have hlt : bridgeSigma (heightOne z.re z.im) < bridgeSigma (3 / 5) :=
      strictAntiOn_bridgeSigma (show (3 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
        (show heightOne z.re z.im ∈ Set.Ici 0 from (heightOne_pos hy0).le) h0
    have := norm_add_le (cornerZero z - 3 / 2) (3 / 2 : ℂ)
    simp only [sub_add_cancel] at this
    linarith
  by_cases hh : 3 / 5 < heightOne (1 / 2 - z.re) z.im
  · rw [foldMap_of_heightHalf h0 hh, cornerHalf, norm_neg, Complex.norm_conj]
    have hn := norm_cornerZero_sub (foldMirror z)
    rw [foldMirror_re, foldMirror_im] at hn
    have hlt : bridgeSigma (heightOne (1 / 2 - z.re) z.im) < bridgeSigma (3 / 5) :=
      strictAntiOn_bridgeSigma (show (3 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
        (show heightOne (1 / 2 - z.re) z.im ∈ Set.Ici 0 from (heightOne_pos hy0).le) hh
    have := norm_add_le (cornerZero (foldMirror z) - 3 / 2) (3 / 2 : ℂ)
    simp only [sub_add_cancel] at this
    linarith
  by_cases hl : foldLens z
  · rw [foldMap_of_lens h0 hh hl]
    linarith [norm_bridgeTwo_le hy0]
  · rw [foldMap_of_not_lens h0 hh hl, norm_cornerInf hy0]
    exact strictMonoOn_foldRho.monotoneOn hy0 (show (47 / 100 : ℝ) ∈ Set.Ioi 0 by norm_num) hy

theorem foldMap_quarter {Y : ℝ} (hY : 9 / 20 ≤ Y) :
    foldMap ((1 / 4 : ℝ) + (Y : ℂ) * Complex.I) =
      cornerInf ((1 / 4 : ℝ) + (Y : ℂ) * Complex.I) := by
  have hre : ((1 / 4 : ℝ) + (Y : ℂ) * Complex.I).re = 1 / 4 := by simp
  have him : ((1 / 4 : ℝ) + (Y : ℂ) * Complex.I).im = Y := by simp
  have hY0 : 0 < Y := by linarith
  have hh : ∀ a : ℝ, a = 1 / 4 → ¬ 3 / 5 < heightOne a Y := by
    intro a ha
    subst ha
    unfold heightOne
    rw [not_lt, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Y - 5 / 24)]
  refine foldMap_of_not_lens ?_ ?_ ?_
  · rw [hre, him]; exact hh _ rfl
  · rw [hre, him]; exact hh _ (by norm_num)
  · intro hl
    have := hl.1
    rw [hre, him] at this
    unfold wallTwo at this
    nlinarith

theorem norm_foldMap_quarter {Y : ℝ} (hY : 9 / 20 ≤ Y) :
    ‖foldMap ((1 / 4 : ℝ) + (Y : ℂ) * Complex.I)‖ = foldRho Y := by
  rw [foldMap_quarter hY, norm_cornerInf (by simp; linarith)]
  simp

theorem not_isBounded_ray {u : ℂ} (hu : u ≠ 0) :
    ¬ Bornology.IsBounded ((fun t : ℝ => (t : ℂ) * u) '' Set.Ici 1) := by
  rw [isBounded_iff_forall_norm_le]
  rintro ⟨C, hC⟩
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  set t : ℝ := max 1 ((|C| + 1) / ‖u‖)
  have ht := hC ((t : ℂ) * u) ⟨t, Set.mem_Ici.2 (le_max_left _ _), rfl⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at ht
  have h1 : (|C| + 1) / ‖u‖ ≤ t := le_max_right _ _
  rw [div_le_iff₀ hn] at h1
  linarith [le_abs_self C]

theorem isPreconnected_ray (u : ℂ) :
    IsPreconnected ((fun t : ℝ => (t : ℂ) * u) '' Set.Ici 1) :=
  isPreconnected_Ici.image _ (by fun_prop)

theorem norm_ray_ge {u v : ℂ} (hv : v ∈ (fun t : ℝ => (t : ℂ) * u) '' Set.Ici 1) : ‖u‖ ≤ ‖v‖ := by
  obtain ⟨t, ht, rfl⟩ := hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [Set.mem_Ici.1 ht])]
  nlinarith [norm_nonneg u, Set.mem_Ici.1 ht]

theorem sphere_subset_foldOuter : Metric.sphere foldCenter (1 / 10) ⊆ foldOuter := by
  intro w hw
  rw [mem_sphere_iff_norm] at hw
  refine ⟨triangleInterior_subset (mem_triangleInterior_of_norm_lt (by rw [hw]; norm_num)), ?_⟩
  have := norm_sub_foldCenter_sq w
  rw [hw] at this
  linarith

theorem norm_foldMap_sphere_le {w : ℂ} (hw : w ∈ Metric.sphere foldCenter (1 / 10)) :
    ‖foldMap w‖ ≤ foldRho (47 / 100) := by
  rw [mem_sphere_iff_norm] at hw
  exact norm_foldMap_le (sphere_subset_foldOuter (mem_sphere_iff_norm.2 hw)).1
    (im_le_of_norm_le hw.le)

theorem continuousAt_foldMap_of_norm {z : ℂ} (hz : 0 < z.im) (h : 1 / 10 < ‖z - foldCenter‖) :
    ContinuousAt foldMap z :=
  (contDiffAt_foldMap hz
    (by nlinarith [sq_lt_of_norm_sub_foldCenter_gt (by norm_num) h])).continuousAt

theorem mem_foldOuter_of_norm {z : ℂ} (hz : z ∈ triangleSet) (h : 1 / 10 ≤ ‖z - foldCenter‖) :
    z ∈ foldOuter := by
  refine ⟨hz, ?_⟩
  have := norm_sub_foldCenter_sq z
  nlinarith [norm_nonneg (z - foldCenter)]

theorem exists_unbounded_of_outside {z : ℂ} (hz : z ∈ triangleSet)
    (hout : 1 / 10 < ‖z - foldCenter‖) :
    ∃ S : Set ℂ, IsPreconnected S ∧ foldMap z ∈ S ∧
      Disjoint S (foldMap '' Metric.sphere foldCenter (1 / 10)) ∧ ¬ Bornology.IsBounded S := by
  set Y := max 1 z.im
  have hY1 : 1 ≤ Y := le_max_left _ _
  obtain ⟨P, hP, hzP, htop, hPΔ, hPout⟩ :=
    exists_isPreconnected_path_top hz hout hY1 (le_max_right _ _)
  set u₀ := foldMap ((1 / 4 : ℝ) + (Y : ℂ) * Complex.I)
  have hu₀ : ‖u₀‖ = foldRho Y := norm_foldMap_quarter (by linarith)
  have hgt : foldRho (47 / 100) < foldRho Y :=
    strictMonoOn_foldRho (show (47 / 100 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show Y ∈ Set.Ioi 0 from lt_of_lt_of_le one_pos hY1) (by linarith)
  have hu0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu₀
    linarith [two_lt_foldRho (show 0 < Y by linarith)]
  have hcont : ContinuousOn foldMap P := fun w hw =>
    (continuousAt_foldMap_of_norm (hPΔ hw).1 (hPout w hw)).continuousWithinAt
  refine ⟨foldMap '' P ∪ (fun t : ℝ => (t : ℂ) * u₀) '' Set.Ici 1,
    (hP.image _ hcont).union u₀ ⟨_, htop, rfl⟩ ⟨1, Set.mem_Ici.2 le_rfl, by simp⟩
      (isPreconnected_ray u₀), Or.inl ⟨z, hzP, rfl⟩, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro v (⟨p, hp, rfl⟩ | hv) ⟨q, hq, hpq⟩
    · have hq' := sphere_subset_foldOuter hq
      have hp' := mem_foldOuter_of_norm (hPΔ hp) (hPout p hp).le
      have := foldMap_injOn hq' hp' hpq
      rw [mem_sphere_iff_norm] at hq
      have h2 := hPout p hp
      rw [← this, hq] at h2
      exact lt_irrefl _ h2
    · have h1 := norm_ray_ge hv
      have h2 := norm_foldMap_sphere_le hq
      rw [hpq] at h2
      linarith
  · intro hb
    exact not_isBounded_ray hu0 (hb.subset Set.subset_union_right)

theorem foldMap_outside_ray {u : ℂ} (hu : u ∉ foldPantsUpper) :
    ∃ S : Set ℂ, IsPreconnected S ∧ u ∈ S ∧ Disjoint S foldPantsUpper ∧
      ¬ Bornology.IsBounded S := by
  have hdown : IsPreconnected ((fun t : ℝ => u - (t : ℂ) * Complex.I) '' Set.Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hdownb : ¬ Bornology.IsBounded ((fun t : ℝ => u - (t : ℂ) * Complex.I) '' Set.Ici 0) := by
    rw [isBounded_iff_forall_norm_le]
    rintro ⟨C, hC⟩
    set t : ℝ := |C| + ‖u‖ + 1
    have ht := hC (u - (t : ℂ) * Complex.I) ⟨t, Set.mem_Ici.2 (by positivity), rfl⟩
    have h1 := norm_sub_norm_le ((t : ℂ) * Complex.I) u
    rw [norm_sub_rev] at h1
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one] at h1
    linarith [le_abs_self C]
  have hu0 : u ∈ (fun t : ℝ => u - (t : ℂ) * Complex.I) '' Set.Ici 0 :=
    ⟨0, Set.mem_Ici.2 le_rfl, by simp⟩
  by_cases him : u.im ≤ 0
  · refine ⟨_, hdown, hu0, Set.disjoint_left.2 ?_, hdownb⟩
    rintro v ⟨t, ht, rfl⟩ hv
    have := hv.2
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] at this
    linarith [Set.mem_Ici.1 ht]
  push Not at him
  have hp : ¬ planarFunction 3 u < 0 := fun h => hu ⟨h, him⟩
  rw [planarFunction_three_neg_iff] at hp
  by_cases h3 : 3 ≤ ‖u‖
  · have hu00 : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h3
      linarith
    refine ⟨_, isPreconnected_ray u, ⟨1, Set.mem_Ici.2 le_rfl, by simp⟩,
      Set.disjoint_left.2 ?_, not_isBounded_ray hu00⟩
    intro v hv hvp
    have := norm_ray_ge hv
    have := ((planarFunction_three_neg_iff v).1 hvp.1).1
    linarith
  · push Not at h3
    have hhole : ‖u - 3 / 2‖ ≤ 1 / 2 ∨ ‖u + 3 / 2‖ ≤ 1 / 2 := by
      by_contra hc
      push Not at hc
      exact hp ⟨h3, hc.1, hc.2⟩
    refine ⟨_, hdown, hu0, Set.disjoint_left.2 ?_, hdownb⟩
    rintro v ⟨t, ht, rfl⟩ hv
    have ht0 := Set.mem_Ici.1 ht
    have hvim := hv.2
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] at hvim
    obtain ⟨-, hv1, hv2⟩ := (planarFunction_three_neg_iff _).1 hv.1
    have key : ∀ c : ℝ, ‖u - (t : ℂ) * Complex.I - c‖ ≤ ‖u - c‖ := by
      intro c
      have e1 : ‖u - (t : ℂ) * Complex.I - c‖ ^ 2 = (u.re - c) ^ 2 + (u.im - t) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      have e2 : ‖u - c‖ ^ 2 = (u.re - c) ^ 2 + u.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      have : ‖u - (t : ℂ) * Complex.I - c‖ ^ 2 ≤ ‖u - c‖ ^ 2 := by
        rw [e1, e2]
        nlinarith
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
    have k1 := key (3 / 2)
    have k2 := key (-(3 / 2))
    push_cast at k1 k2
    rw [sub_neg_eq_add, sub_neg_eq_add] at k2
    rcases hhole with hh | hh <;> linarith

theorem exists_foldCore :
    ∃ F : ℂ → ℂ, (∀ z, 1 / 10 ≤ ‖z - foldCenter‖ → F z = foldMap z) ∧
      (∀ z, 0 < z.im → ContDiffAt ℝ ∞ F z) ∧ (∀ z, 0 < z.im → (fderiv ℝ F z).det ≠ 0) ∧
      Set.InjOn F triangleSet ∧ Set.MapsTo F triangleSet pantsPlus ∧
      Set.MapsTo F triangleInterior foldPantsUpper := by
  have hann : ∀ z : ℂ, 1 / 10 - 1 / 250 < ‖z - foldCenter‖ → ‖z - foldCenter‖ < 1 / 10 + 1 / 250 →
      z ∈ triangleInterior ∧ z ∈ foldOuter ∧
        (12 / 125) ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2 := by
    intro z h1 h2
    have hI := mem_triangleInterior_of_norm_lt (by linarith : ‖z - foldCenter‖ < 13 / 125)
    have hsq := sq_lt_of_norm_sub_foldCenter_gt (by norm_num) h1
    exact ⟨hI, ⟨triangleInterior_subset hI, by nlinarith⟩, by nlinarith⟩
  have hE : ContDiffOn ℝ ∞ foldMap
      {z | 1 / 10 - 1 / 250 < ‖z - foldCenter‖ ∧ ‖z - foldCenter‖ < 1 / 10 + 1 / 250} := by
    rintro z ⟨h1, h2⟩
    obtain ⟨hI, -, hsq⟩ := hann z h1 h2
    exact (contDiffAt_foldMap hI.1 hsq).contDiffWithinAt
  have hdet : ∀ z, 1 / 10 - 1 / 250 < ‖z - foldCenter‖ → ‖z - foldCenter‖ < 1 / 10 + 1 / 250 →
      (fderiv ℝ foldMap z).det ≠ 0 := fun z h1 h2 => by
    obtain ⟨hI, -, hsq⟩ := hann z h1 h2
    exact det_fderiv_foldMap_ne_zero hI.1 hsq
  have hinj : Set.InjOn foldMap
      {z | 1 / 10 - 1 / 250 < ‖z - foldCenter‖ ∧ ‖z - foldCenter‖ < 1 / 10 + 1 / 250} :=
    foldMap_injOn.mono fun z hz => (hann z hz.1 hz.2).2.1
  set z₀ : ℂ := foldCenter + ((51 / 500 : ℝ) : ℂ) * Complex.I
  have hz₀n : ‖z₀ - foldCenter‖ = 51 / 500 := by
    simp only [z₀, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  have hz₀eq : z₀ = (1 / 4 : ℝ) + ((59 / 125 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [z₀, foldCenter]
    · simp [z₀, foldCenter]
      norm_num
  have hu₀ : ‖foldMap z₀‖ = foldRho (59 / 125) := by
    rw [hz₀eq]
    exact norm_foldMap_quarter (by norm_num)
  have hgt : foldRho (47 / 100) < foldRho (59 / 125) :=
    strictMonoOn_foldRho (show (47 / 100 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (59 / 125 : ℝ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
  have hu0 : foldMap z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu₀
    linarith [two_lt_foldRho (show (0 : ℝ) < 59 / 125 by norm_num)]
  have hout : ∃ z₁, 1 / 10 < ‖z₁ - foldCenter‖ ∧ ‖z₁ - foldCenter‖ < 1 / 10 + 1 / 250 ∧
      ∃ S : Set ℂ, IsPreconnected S ∧ foldMap z₁ ∈ S ∧
        Disjoint S (foldMap '' Metric.sphere foldCenter (1 / 10)) ∧ ¬ Bornology.IsBounded S := by
    refine ⟨z₀, by rw [hz₀n]; norm_num, by rw [hz₀n]; norm_num, _, isPreconnected_ray _,
      ⟨1, Set.mem_Ici.2 le_rfl, by simp⟩, Set.disjoint_left.2 ?_, not_isBounded_ray hu0⟩
    rintro v hv ⟨q, hq, rfl⟩
    have h1 := norm_ray_ge hv
    have h2 := norm_foldMap_sphere_le hq
    linarith
  obtain ⟨Q, hQs, hQi, hQd, ⟨V, hVo, hsV, hQV⟩, hQc⟩ :=
    exists_core_replacement (by norm_num : (0 : ℝ) < 1 / 250) (by norm_num) hE hdet hinj hout
  classical
  set F : ℂ → ℂ := fun z => if ‖z - foldCenter‖ < 1 / 10 then Q z else foldMap z with hFdef
  have hF1 : ∀ z, 1 / 10 ≤ ‖z - foldCenter‖ → F z = foldMap z := fun z hz => by
    simp only [hFdef, not_lt.2 hz, ↓reduceIte]
  have hFQ : ∀ z ∈ V ∪ Metric.ball foldCenter (1 / 10), F z = Q z := by
    rintro z (hz | hz)
    · by_cases h : ‖z - foldCenter‖ < 1 / 10
      · simp only [hFdef, h, ↓reduceIte]
      · rw [hF1 z (not_lt.1 h)]
        exact (hQV hz).symm
    · rw [mem_ball_iff_norm] at hz
      simp only [hFdef, hz, ↓reduceIte]
  have hopenQ : IsOpen (V ∪ Metric.ball foldCenter (1 / 10)) := hVo.union Metric.isOpen_ball
  have hopenE : IsOpen {z : ℂ | 1 / 10 < ‖z - foldCenter‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  have hcover : ∀ z, z ∈ V ∪ Metric.ball foldCenter (1 / 10) ∨ 1 / 10 < ‖z - foldCenter‖ := by
    intro z
    rcases lt_trichotomy ‖z - foldCenter‖ (1 / 10) with h | h | h
    · exact Or.inl (Or.inr (mem_ball_iff_norm.2 h))
    · exact Or.inl (Or.inl (hsV (mem_sphere_iff_norm.2 h)))
    · exact Or.inr h
  have hlocal : ∀ z, 0 < z.im → (F =ᶠ[𝓝 z] Q) ∨
      (F =ᶠ[𝓝 z] foldMap ∧ (12 / 125) ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2) := by
    intro z hz
    rcases hcover z with h | h
    · exact Or.inl (Filter.eventually_of_mem (hopenQ.mem_nhds h) hFQ)
    · refine Or.inr ⟨Filter.eventually_of_mem (hopenE.mem_nhds h) fun w hw => hF1 w hw.le, ?_⟩
      nlinarith [sq_lt_of_norm_sub_foldCenter_gt (by norm_num) h]
  have hQball : Q '' Metric.ball foldCenter (1 / 10) ⊆ foldPantsUpper := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hc
    obtain ⟨S, hS, huS, hSd, hSb⟩ := foldMap_outside_ray hc
    have hΓ : Disjoint S (foldMap '' Metric.sphere foldCenter (1 / 10)) := by
      refine Set.disjoint_left.2 fun v hv ⟨q, hq, hqv⟩ => Set.disjoint_left.1 hSd hv ?_
      rw [← hqv]
      have hqI := mem_triangleInterior_of_norm_lt
        (by rw [mem_sphere_iff_norm] at hq; rw [hq]; norm_num : ‖q - foldCenter‖ < 13 / 125)
      exact ⟨(foldMap_mem_pantsPlus (triangleInterior_subset hqI)).1, foldMap_im_pos hqI⟩
    exact Set.disjoint_left.1 (hQc S hS hSb hΓ) huS ⟨z, hz, rfl⟩
  refine ⟨F, hF1, fun z hz => ?_, fun z hz => ?_, ?_, ?_, ?_⟩
  · rcases hlocal z hz with h | ⟨h, hsq⟩
    · exact (hQs.contDiffAt).congr_of_eventuallyEq h
    · exact (contDiffAt_foldMap hz hsq).congr_of_eventuallyEq h
  · rcases hlocal z hz with h | ⟨h, hsq⟩
    · rw [h.fderiv_eq]; exact hQd z
    · rw [h.fderiv_eq]; exact det_fderiv_foldMap_ne_zero hz hsq
  · intro z hz z' hz' heq
    have key : ∀ a b : ℂ, a ∈ triangleSet → b ∈ triangleSet → ‖a - foldCenter‖ < 1 / 10 →
        1 / 10 ≤ ‖b - foldCenter‖ → F a = F b → False := by
      intro a b ha hb hna hnb hab
      have hFa : F a = Q a := hFQ a (Or.inr (mem_ball_iff_norm.2 hna))
      rcases lt_or_eq_of_le hnb with hlt | heqn
      · obtain ⟨S, hS, hbS, hSd, hSb⟩ := exists_unbounded_of_outside hb hlt
        rw [← hF1 b hnb, ← hab, hFa] at hbS
        exact Set.disjoint_left.1 (hQc S hS hSb hSd) hbS ⟨a, mem_ball_iff_norm.2 hna, rfl⟩
      · have hbV : b ∈ V := hsV (mem_sphere_iff_norm.2 heqn.symm)
        have hFb : F b = Q b := hFQ b (Or.inl hbV)
        rw [hFa, hFb] at hab
        have := hQi hab
        rw [this] at hna
        linarith
    by_cases h1 : ‖z - foldCenter‖ < 1 / 10 <;> by_cases h2 : ‖z' - foldCenter‖ < 1 / 10
    · rw [hFQ z (Or.inr (mem_ball_iff_norm.2 h1)), hFQ z' (Or.inr (mem_ball_iff_norm.2 h2))]
        at heq
      exact hQi heq
    · exact (key z z' hz hz' h1 (not_lt.1 h2) heq).elim
    · exact (key z' z hz' hz h2 (not_lt.1 h1) heq.symm).elim
    · rw [hF1 z (not_lt.1 h1), hF1 z' (not_lt.1 h2)] at heq
      exact foldMap_injOn (mem_foldOuter_of_norm hz (not_lt.1 h1))
        (mem_foldOuter_of_norm hz' (not_lt.1 h2)) heq
  · intro z hz
    by_cases h : ‖z - foldCenter‖ < 1 / 10
    · rw [hFQ z (Or.inr (mem_ball_iff_norm.2 h))]
      have := hQball ⟨z, mem_ball_iff_norm.2 h, rfl⟩
      exact ⟨this.1, this.2.le⟩
    · rw [hF1 z (not_lt.1 h)]
      exact foldMap_mem_pantsPlus hz
  · intro z hz
    by_cases h : ‖z - foldCenter‖ < 1 / 10
    · rw [hFQ z (Or.inr (mem_ball_iff_norm.2 h))]
      exact hQball ⟨z, mem_ball_iff_norm.2 h, rfl⟩
    · rw [hF1 z (not_lt.1 h)]
      exact ⟨(foldMap_mem_pantsPlus (triangleInterior_subset hz)).1, foldMap_im_pos hz⟩

end GC.Seifert
