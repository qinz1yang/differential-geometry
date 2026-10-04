import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldLocal

/-!
# Image and injectivity of the K16f fold outside the core disc

Packet K16f, tier 2. `foldMap` maps the closed ideal triangle `triangleSet` into the closed upper
half `pantsPlus` of the open pants (`foldMap_mem_pantsPlus`) and its interior into the open
upper half (`foldMap_im_pos`). On `foldOuter`, the triangle minus the open disc of radius
`12/125` about `foldCenter`, it is injective (`foldMap_injOn`): the four branches have images
separated by the moduli `‖u ∓ 3/2‖` and `‖u‖` (`foldOuter_cases`; for `cornerInf` this uses
`middle_box_inside`, in `cornerInf_bounds`), and each branch formula is injective
(`cornerZero_injOn`, `bridgeTwo_injOn`, `cornerInf_injOn`; `cornerHalf` by the mirror).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Topology

namespace GC.Seifert

theorem conj_three_halves : (starRingEnd ℂ) (3 / 2 : ℂ) = 3 / 2 := by
  rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]

theorem norm_bridgeZero_sub {z : ℂ} (hz : 0 < z.im) :
    ‖bridgeZero z - 3 / 2‖ = bridgeSigma (heightOne z.re z.im) := by
  have h := bridgeRe0_sub_sq_add_bridgeIm0_sq (x := z.re) hz
  have hs : 0 < bridgeSigma (heightOne z.re z.im) := by
    linarith [half_lt_bridgeSigma (heightOne z.re z.im)]
  have h2 : ‖bridgeZero z - 3 / 2‖ ^ 2 = bridgeSigma (heightOne z.re z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← h]
    simp [bridgeZero_re, bridgeZero_im]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) hs.le).1 h2

theorem norm_bridgeTwo_sub {z : ℂ} (hz : 0 < z.im) :
    ‖bridgeTwo z - 3 / 2‖ = bridgeSigma (heightOne z.re z.im) := by
  have h := bridgeRe2_sub_sq_add_bridgeIm2_sq (x := z.re) hz
  have hs : 0 < bridgeSigma (heightOne z.re z.im) := by
    linarith [half_lt_bridgeSigma (heightOne z.re z.im)]
  have h2 : ‖bridgeTwo z - 3 / 2‖ ^ 2 = bridgeSigma (heightOne z.re z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← h]
    simp [bridgeTwo_re, bridgeTwo_im]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) hs.le).1 h2

theorem norm_bridgeTwo_add {z : ℂ} (hz : 0 < z.im) :
    ‖bridgeTwo z + 3 / 2‖ = bridgeSigma (heightOne (1 / 2 - z.re) z.im) := by
  have h := bridgeRe2_add_sq_add_bridgeIm2_sq (x := z.re) hz
  have hs : 0 < bridgeSigma (heightOne (1 / 2 - z.re) z.im) := by
    linarith [half_lt_bridgeSigma (heightOne (1 / 2 - z.re) z.im)]
  have h2 : ‖bridgeTwo z + 3 / 2‖ ^ 2 = bridgeSigma (heightOne (1 / 2 - z.re) z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← h]
    simp [bridgeTwo_re, bridgeTwo_im]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) hs.le).1 h2

theorem norm_bridgeTwo_le {z : ℂ} (hz : 0 < z.im) : ‖bridgeTwo z‖ ≤ 2 := by
  have h1 := norm_bridgeTwo_sub hz
  have h2 := norm_bridgeTwo_add hz
  have hs1 := bridgeSigma_le (heightOne z.re z.im)
  have hs2 := bridgeSigma_le (heightOne (1 / 2 - z.re) z.im)
  have hpar : 2 * ‖bridgeTwo z‖ ^ 2 =
      ‖bridgeTwo z - 3 / 2‖ ^ 2 + ‖bridgeTwo z + 3 / 2‖ ^ 2 - 9 / 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.normSq_apply]
    simp
    ring
  have hn := norm_nonneg (bridgeTwo z)
  have hl1 := half_lt_bridgeSigma (heightOne z.re z.im)
  have hl2 := half_lt_bridgeSigma (heightOne (1 / 2 - z.re) z.im)
  rw [h1, h2] at hpar
  have hq : ‖bridgeTwo z‖ ^ 2 ≤ 4 := by nlinarith
  nlinarith

theorem norm_cornerHalf_add (z : ℂ) :
    ‖cornerHalf z + 3 / 2‖ = bridgeSigma (heightOne (1 / 2 - z.re) z.im) := by
  have h := norm_cornerZero_sub (foldMirror z)
  rw [foldMirror_re, foldMirror_im] at h
  rw [← h, cornerHalf, show -(starRingEnd ℂ) (cornerZero (foldMirror z)) + 3 / 2 =
    -(starRingEnd ℂ) (cornerZero (foldMirror z) - 3 / 2) by rw [map_sub, conj_three_halves]; ring,
    norm_neg, Complex.norm_conj]

def foldOuter : Set ℂ :=
  {z | z ∈ triangleSet ∧ (12 / 125) ^ 2 ≤ (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2}

theorem holeX_mem_of_mem_triangleSet {z : ℂ} (hz : z ∈ triangleSet) :
    -(1 / 2) ≤ holeX z.re z.im ∧ holeX z.re z.im ≤ 0 := by
  obtain ⟨hy, h0, h1, hw⟩ := hz
  have hs : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  unfold holeX
  unfold wallTwo at hw
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

def pantsPlus : Set ℂ := {u | planarFunction 3 u < 0 ∧ 0 ≤ u.im}

def triangleInterior : Set ℂ :=
  {w | 0 < w.im ∧ 0 < w.re ∧ w.re < 1 / 2 ∧ 0 < wallTwo w.re w.im}

theorem triangleInterior_subset : triangleInterior ⊆ triangleSet := by
  intro w h
  exact ⟨h.1, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem foldMirror_mem_triangleSet {z : ℂ} (hz : z ∈ triangleSet) : foldMirror z ∈ triangleSet := by
  obtain ⟨hy, h0, h1, hw⟩ := hz
  refine ⟨by rw [foldMirror_im]; exact hy, by rw [foldMirror_re]; linarith,
    by rw [foldMirror_re]; linarith, ?_⟩
  rw [foldMirror_re, foldMirror_im, wallTwo_mirror]
  exact hw

theorem foldMirror_mem_triangleInterior {z : ℂ} (hz : z ∈ triangleInterior) :
    foldMirror z ∈ triangleInterior := by
  obtain ⟨hy, h0, h1, hw⟩ := hz
  refine ⟨by rw [foldMirror_im]; exact hy, by rw [foldMirror_re]; linarith,
    by rw [foldMirror_re]; linarith, ?_⟩
  rw [foldMirror_re, foldMirror_im, wallTwo_mirror]
  exact hw

theorem holeX_mem_of_mem_triangleInterior {z : ℂ} (hz : z ∈ triangleInterior) :
    -(1 / 2) < holeX z.re z.im ∧ holeX z.re z.im < 0 := by
  obtain ⟨hy, h0, h1, hw⟩ := hz
  have hs : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  unfold holeX
  unfold wallTwo at hw
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem neg_conj_mem_pantsPlus_iff (u : ℂ) : -(starRingEnd ℂ) u ∈ pantsPlus ↔ u ∈ pantsPlus := by
  have e1 : ‖-(starRingEnd ℂ) u‖ = ‖u‖ := by rw [norm_neg, Complex.norm_conj]
  have e2 : ‖-(starRingEnd ℂ) u - 3 / 2‖ = ‖u + 3 / 2‖ := by
    rw [show -(starRingEnd ℂ) u - 3 / 2 = -(starRingEnd ℂ) (u + 3 / 2) by
      rw [map_add, conj_three_halves]; ring, norm_neg, Complex.norm_conj]
  have e3 : ‖-(starRingEnd ℂ) u + 3 / 2‖ = ‖u - 3 / 2‖ := by
    rw [show -(starRingEnd ℂ) u + 3 / 2 = -(starRingEnd ℂ) (u - 3 / 2) by
      rw [map_sub, conj_three_halves]; ring, norm_neg, Complex.norm_conj]
  unfold pantsPlus
  simp only [Set.mem_ofPred_eq, planarFunction_three_neg_iff, e1, e2, e3, Complex.neg_im,
    Complex.conj_im, neg_neg]
  tauto

theorem cornerZero_mem_pantsPlus {z : ℂ} (hz : z ∈ triangleSet) (h0 : 3 / 5 < heightOne z.re z.im) :
    cornerZero z ∈ pantsPlus := by
  have hy := hz.1
  obtain ⟨hX0, hX1⟩ := holeX_mem_of_mem_triangleSet hz
  have hσ := bridgeSigma_three_fifths_lt
  have hn := norm_cornerZero_sub z
  have hlt : bridgeSigma (heightOne z.re z.im) < bridgeSigma (3 / 5) :=
    strictAntiOn_bridgeSigma (by norm_num : (3 / 5 : ℝ) ∈ Set.Ici 0)
      (show heightOne z.re z.im ∈ Set.Ici 0 from (heightOne_pos hy).le) h0
  have hhalf := half_lt_bridgeSigma (heightOne z.re z.im)
  refine ⟨(planarFunction_three_neg_iff _).2 ⟨?_, by linarith, ?_⟩,
    cornerZero_im_nonneg hy (by linarith) hX0 hX1⟩
  · have := norm_add_le (cornerZero z - 3 / 2) (3 / 2 : ℂ)
    simp only [sub_add_cancel] at this
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    linarith
  · have := norm_sub_le (cornerZero z + 3 / 2) (cornerZero z - 3 / 2)
    have h3 : cornerZero z + 3 / 2 - (cornerZero z - 3 / 2) = 3 := by ring
    rw [h3] at this
    have h33 : ‖(3 : ℂ)‖ = 3 := by norm_num
    linarith

theorem bridgeTwo_mem_pantsPlus {z : ℂ} (hz : z ∈ triangleSet) : bridgeTwo z ∈ pantsPlus := by
  have hy := hz.1
  refine ⟨(planarFunction_three_neg_iff _).2 ⟨by linarith [norm_bridgeTwo_le hy], ?_, ?_⟩, ?_⟩
  · rw [norm_bridgeTwo_sub hy]; exact half_lt_bridgeSigma _
  · rw [norm_bridgeTwo_add hy]; exact half_lt_bridgeSigma _
  · rw [bridgeTwo_im, bridgeIm2]
    exact mul_nonneg hz.2.2.2 (Real.sqrt_nonneg _)

theorem cornerInf_mem_pantsPlus {z : ℂ} (hz : z ∈ triangleSet) : cornerInf z ∈ pantsPlus := by
  have hy := hz.1
  have hn := norm_cornerInf hy
  have h2 := two_lt_foldRho hy
  have h3 := foldRho_lt_three hy.le
  refine ⟨(planarFunction_three_neg_iff _).2 ⟨by linarith, ?_, ?_⟩,
    cornerInf_im_nonneg hy hz.2.1 hz.2.2.1⟩
  · have := norm_sub_norm_le (cornerInf z) (3 / 2 : ℂ)
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    linarith
  · have := norm_sub_norm_le (cornerInf z) (-(3 / 2) : ℂ)
    rw [sub_neg_eq_add] at this
    have h32 : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
    linarith

theorem foldMap_mem_pantsPlus {z : ℂ} (hz : z ∈ triangleSet) : foldMap z ∈ pantsPlus := by
  by_cases h0 : 3 / 5 < heightOne z.re z.im
  · rw [foldMap_of_heightOne h0]
    exact cornerZero_mem_pantsPlus hz h0
  by_cases hh : 3 / 5 < heightOne (1 / 2 - z.re) z.im
  · rw [foldMap_of_heightHalf h0 hh, cornerHalf, neg_conj_mem_pantsPlus_iff]
    exact cornerZero_mem_pantsPlus (foldMirror_mem_triangleSet hz)
      (by rw [heightOne_foldMirror]; exact hh)
  by_cases hl : foldLens z
  · rw [foldMap_of_lens h0 hh hl]
    exact bridgeTwo_mem_pantsPlus hz
  · rw [foldMap_of_not_lens h0 hh hl]
    exact cornerInf_mem_pantsPlus hz

theorem foldMap_im_pos {z : ℂ} (hz : z ∈ triangleInterior) : 0 < (foldMap z).im := by
  have hy := hz.1
  by_cases h0 : 3 / 5 < heightOne z.re z.im
  · rw [foldMap_of_heightOne h0]
    obtain ⟨hX0, hX1⟩ := holeX_mem_of_mem_triangleInterior hz
    exact cornerZero_im_pos hy (by linarith) hX0 hX1
  by_cases hh : 3 / 5 < heightOne (1 / 2 - z.re) z.im
  · rw [foldMap_of_heightHalf h0 hh, cornerHalf]
    have hM := foldMirror_mem_triangleInterior hz
    obtain ⟨hX0, hX1⟩ := holeX_mem_of_mem_triangleInterior hM
    have := cornerZero_im_pos hM.1 (by rw [heightOne_foldMirror]; linarith) hX0 hX1
    simpa using this
  by_cases hl : foldLens z
  · rw [foldMap_of_lens h0 hh hl, bridgeTwo_im, bridgeIm2]
    exact mul_pos hz.2.2.2 (Real.sqrt_pos.2 (bridgeQ2_pos hy))
  · rw [foldMap_of_not_lens h0 hh hl]
    exact cornerInf_im_pos hy hz.2.1 hz.2.2.1

theorem strictAnti_of_forall_exists_hasDerivAt_neg {g : ℝ → ℝ}
    (h : ∀ t, ∃ D : ℝ, D < 0 ∧ HasDerivAt g D t) : StrictAnti g := by
  have hd : ∀ t, HasDerivAt g (deriv g t) t := fun t => by
    obtain ⟨D, -, hD⟩ := h t
    exact hD.differentiableAt.hasDerivAt
  refine strictAnti_of_hasDerivAt_neg hd fun t => ?_
  obtain ⟨D, hD0, hD⟩ := h t
  rw [hD.deriv]
  exact hD0

theorem angleTwoHole_mem (x y : ℝ) :
    Real.pi / 2 < angleTwoHole x y ∧ angleTwoHole x y < 3 * Real.pi / 2 := by
  unfold angleTwoHole
  have h1 := Real.neg_pi_div_two_lt_arctan (bridgeIm2 x y / (3 / 2 - bridgeRe2 x y))
  have h2 := Real.arctan_lt_pi_div_two (bridgeIm2 x y / (3 / 2 - bridgeRe2 x y))
  constructor <;> linarith

theorem eq_of_exp_mul_I_eq {a b : ℝ} (h : Complex.exp (Complex.I * a) = Complex.exp (Complex.I * b))
    (hab : |a - b| < 2 * Real.pi) : a = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hre : a = b + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      exact_mod_cast this
    have : |a - b| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hre, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  rw [hre, hn0]
  simp

theorem bridgeTwo_injOn : Set.InjOn bridgeTwo {z : ℂ | 0 < z.im} := by
  intro z hz z' hz' heq
  have hz0 : 0 < z.im := hz
  have hz0' : 0 < z'.im := hz'
  have hY : heightOne z.re z.im = heightOne z'.re z'.im := by
    have h1 := norm_bridgeTwo_sub hz0
    have h2 := norm_bridgeTwo_sub hz0'
    rw [heq, h2] at h1
    exact strictAntiOn_bridgeSigma.injOn (show heightOne z'.re z'.im ∈ Set.Ici 0 from
      (heightOne_pos hz0').le) (show heightOne z.re z.im ∈ Set.Ici 0 from
      (heightOne_pos hz0).le) h1 |>.symm
  set Y := heightOne z.re z.im with hYdef
  have hYpos : 0 < Y := heightOne_pos hz0
  have hp := bridgeTwo_sub_eq_polar hz0
  have hp' := bridgeTwo_sub_eq_polar hz0'
  rw [heq, hp', ← hY] at hp
  have hσ : (bridgeSigma Y : ℂ) ≠ 0 := by
    have := half_lt_bridgeSigma Y
    exact_mod_cast (by linarith : bridgeSigma Y ≠ 0)
  have hexp := (mul_left_cancel₀ hσ hp).symm
  have hang : angleTwoHole z.re z.im = angleTwoHole z'.re z'.im := by
    refine eq_of_exp_mul_I_eq hexp ?_
    obtain ⟨a1, a2⟩ := angleTwoHole_mem z.re z.im
    obtain ⟨b1, b2⟩ := angleTwoHole_mem z'.re z'.im
    rw [abs_lt]
    constructor <;> linarith [Real.pi_pos]
  have hg := strictAnti_of_forall_exists_hasDerivAt_neg
    (fun t => exists_hasDerivAt_angleTwoHole (X := t) hYpos)
  obtain ⟨e1, e2⟩ := holeInv_holeX (x := z.re) hz0
  obtain ⟨f1, f2⟩ := holeInv_holeX (x := z'.re) hz0'
  rw [← hY] at f1 f2
  have hX : holeX z.re z.im = holeX z'.re z'.im := by
    apply hg.injective
    simp only
    rw [e1, e2, f1, f2]
    exact hang
  apply Complex.ext
  · rw [← e1, ← f1, hX]
  · rw [← e2, ← f2, hX]

theorem bridgeSigma_le_of_le {t : ℝ} (h0 : 0 < t) (h : t ≤ 3 / 5) :
    bridgeSigma (3 / 5) ≤ bridgeSigma t :=
  strictAntiOn_bridgeSigma.antitoneOn (show t ∈ Set.Ici 0 from h0.le)
    (show (3 / 5 : ℝ) ∈ Set.Ici 0 by norm_num) h

theorem three_halves_lt_norm_bridgeZero_add {z : ℂ} (hz : 0 < z.im) :
    3 / 2 < ‖bridgeZero z + 3 / 2‖ := by
  have h := Complex.re_le_norm (bridgeZero z + 3 / 2)
  have hr := bridgeRe0_pos (x := z.re) hz
  simp only [Complex.add_re, bridgeZero_re] at h
  norm_num at h
  linarith

theorem cornerInf_bounds {z : ℂ} (hz : z ∈ foldOuter) (h0 : ¬ 3 / 5 < heightOne z.re z.im)
    (hh : ¬ 3 / 5 < heightOne (1 / 2 - z.re) z.im) (hl : ¬ foldLens z) :
    bridgeSigma (3 / 5) ≤ ‖cornerInf z - 3 / 2‖ ∧ bridgeSigma (3 / 5) ≤ ‖cornerInf z + 3 / 2‖ := by
  obtain ⟨⟨hy, hx0, hx1, hw⟩, hR⟩ := hz
  push Not at h0 hh
  have hσ := bridgeSigma_three_fifths_lt
  have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
  rcases lt_or_ge (11 / 25) z.im with hyb | hyb
  · have hn := norm_cornerInf hy
    have hmono : foldRho (11 / 25) < foldRho z.im :=
      strictMonoOn_foldRho (show (11 / 25 : ℝ) ∈ Set.Ioi 0 by norm_num) hy hyb
    rw [foldRho_eq_bridgeRho (by norm_num)] at hmono
    have hb := bridgeSigma_add_lt_bridgeRho
    have e1 := norm_sub_norm_le (cornerInf z) (3 / 2 : ℂ)
    have e2 := norm_sub_norm_le (cornerInf z) (-(3 / 2) : ℂ)
    rw [sub_neg_eq_add] at e2
    have h32' : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
    constructor <;> linarith
  rcases le_or_gt z.re (23 / 100) with hxa | hxa
  · rw [cornerInf_eq_bridgeZero hy hxa (by linarith), norm_bridgeZero_sub hy]
    exact ⟨bridgeSigma_le_of_le (heightOne_pos hy) h0,
      le_of_lt (lt_trans hσ (three_halves_lt_norm_bridgeZero_add hy))⟩
  rcases le_or_gt (27 / 100) z.re with hxb | hxb
  · have hMy : 0 < (foldMirror z).im := by rw [foldMirror_im]; exact hy
    have hc : cornerInf z = -(starRingEnd ℂ) (cornerInf (foldMirror z)) := by
      have := cornerInf_foldMirror (foldMirror z)
      rw [foldMirror_foldMirror] at this
      exact this
    have hb : cornerInf (foldMirror z) = bridgeZero (foldMirror z) :=
      cornerInf_eq_bridgeZero hMy (by rw [foldMirror_re]; linarith)
        (by rw [foldMirror_im]; linarith)
    have e1 : ‖cornerInf z - 3 / 2‖ = ‖bridgeZero (foldMirror z) + 3 / 2‖ := by
      rw [hc, hb, show -(starRingEnd ℂ) (bridgeZero (foldMirror z)) - 3 / 2 =
        -(starRingEnd ℂ) (bridgeZero (foldMirror z) + 3 / 2) by
          rw [map_add, conj_three_halves]; ring, norm_neg, Complex.norm_conj]
    have e2 : ‖cornerInf z + 3 / 2‖ = ‖bridgeZero (foldMirror z) - 3 / 2‖ := by
      rw [hc, hb, show -(starRingEnd ℂ) (bridgeZero (foldMirror z)) + 3 / 2 =
        -(starRingEnd ℂ) (bridgeZero (foldMirror z) - 3 / 2) by
          rw [map_sub, conj_three_halves]; ring, norm_neg, Complex.norm_conj]
    rw [e1, e2, norm_bridgeZero_sub hMy, heightOne_foldMirror]
    exact ⟨le_of_lt (lt_trans hσ (three_halves_lt_norm_bridgeZero_add hMy)),
      bridgeSigma_le_of_le (heightOne_pos hy) hh⟩
  exfalso
  have hw' : 1 / 25 ≤ wallTwo z.re z.im := by
    by_contra hc
    push Not at hc
    unfold foldLens at hl
    simp only [not_and_or, not_lt] at hl
    rw [Complex.normSq_apply, Complex.normSq_apply] at hl
    simp only [Complex.sub_re, Complex.sub_im] at hl
    norm_num at hl
    unfold wallTwo at hc hl
    rcases hl with hl | hl | hl
    · linarith
    · nlinarith
    · nlinarith
  have := middle_box_inside hy hxa hxb hyb hw'
  linarith

theorem foldOuter_cases {z : ℂ} (hz : z ∈ foldOuter) :
    (3 / 5 < heightOne z.re z.im ∧ foldMap z = cornerZero z ∧
        ‖foldMap z - 3 / 2‖ < bridgeSigma (3 / 5)) ∨
      (3 / 5 < heightOne (1 / 2 - z.re) z.im ∧ foldMap z = cornerHalf z ∧
        ‖foldMap z + 3 / 2‖ < bridgeSigma (3 / 5)) ∨
      (foldMap z = bridgeTwo z ∧ bridgeSigma (3 / 5) ≤ ‖foldMap z - 3 / 2‖ ∧
        bridgeSigma (3 / 5) ≤ ‖foldMap z + 3 / 2‖ ∧ ‖foldMap z‖ ≤ 2) ∨
      (foldMap z = cornerInf z ∧ bridgeSigma (3 / 5) ≤ ‖foldMap z - 3 / 2‖ ∧
        bridgeSigma (3 / 5) ≤ ‖foldMap z + 3 / 2‖ ∧ 2 < ‖foldMap z‖) := by
  have hy := hz.1.1
  by_cases h0 : 3 / 5 < heightOne z.re z.im
  · refine Or.inl ⟨h0, foldMap_of_heightOne h0, ?_⟩
    rw [foldMap_of_heightOne h0, norm_cornerZero_sub]
    exact strictAntiOn_bridgeSigma (show (3 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show heightOne z.re z.im ∈ Set.Ici 0 from (heightOne_pos hy).le) h0
  by_cases hh : 3 / 5 < heightOne (1 / 2 - z.re) z.im
  · refine Or.inr (Or.inl ⟨hh, foldMap_of_heightHalf h0 hh, ?_⟩)
    rw [foldMap_of_heightHalf h0 hh, norm_cornerHalf_add]
    exact strictAntiOn_bridgeSigma (show (3 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show heightOne (1 / 2 - z.re) z.im ∈ Set.Ici 0 from (heightOne_pos hy).le) hh
  push Not at h0 hh
  by_cases hl : foldLens z
  · refine Or.inr (Or.inr (Or.inl ⟨foldMap_of_lens (not_lt.2 h0) (not_lt.2 hh) hl, ?_⟩))
    rw [foldMap_of_lens (not_lt.2 h0) (not_lt.2 hh) hl, norm_bridgeTwo_sub hy,
      norm_bridgeTwo_add hy]
    exact ⟨bridgeSigma_le_of_le (heightOne_pos hy) h0,
      bridgeSigma_le_of_le (heightOne_pos hy) hh, norm_bridgeTwo_le hy⟩
  · refine Or.inr (Or.inr (Or.inr ⟨foldMap_of_not_lens (not_lt.2 h0) (not_lt.2 hh) hl, ?_⟩))
    rw [foldMap_of_not_lens (not_lt.2 h0) (not_lt.2 hh) hl, norm_cornerInf hy]
    obtain ⟨b1, b2⟩ := cornerInf_bounds hz (not_lt.2 h0) (not_lt.2 hh) hl
    exact ⟨b1, b2, two_lt_foldRho hy⟩

theorem foldMap_injOn : Set.InjOn foldMap foldOuter := by
  intro z hz z' hz' heq
  have hσ := bridgeSigma_three_fifths_lt
  have hsep : ∀ u : ℂ, 3 ≤ ‖u - 3 / 2‖ + ‖u + 3 / 2‖ := fun u => by
    have := norm_sub_le (u + 3 / 2) (u - 3 / 2)
    have h3 : (u + 3 / 2) - (u - 3 / 2) = 3 := by ring
    rw [h3] at this
    have h33 : ‖(3 : ℂ)‖ = 3 := by norm_num
    linarith
  have hy := hz.1.1
  have hy' := hz'.1.1
  have hsep' := hsep (foldMap z)
  have hc' := foldOuter_cases hz'
  rw [← heq] at hc'
  rcases foldOuter_cases hz with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨c1, c2, c3, c4⟩ |
    ⟨d1, d2, d3, d4⟩ <;>
  rcases hc' with ⟨a1', a2', a3'⟩ | ⟨b1', b2', b3'⟩ | ⟨c1', c2', c3', c4'⟩ |
    ⟨d1', d2', d3', d4'⟩ <;> try linarith
  · have heq' : cornerZero z = cornerZero z' := a2.symm.trans a2'
    obtain ⟨hX0, hX1⟩ := holeX_mem_of_mem_triangleSet hz.1
    obtain ⟨hX0', hX1'⟩ := holeX_mem_of_mem_triangleSet hz'.1
    exact cornerZero_injOn ⟨hy, by linarith, hX0, hX1⟩ ⟨hy', by linarith, hX0', hX1'⟩ heq'
  · have heq' : cornerHalf z = cornerHalf z' := b2.symm.trans b2'
    rw [cornerHalf, cornerHalf, neg_inj] at heq'
    have heq'' := congrArg (starRingEnd ℂ) heq'
    simp only [Complex.conj_conj] at heq''
    have hM := foldMirror_mem_triangleSet hz.1
    have hM' := foldMirror_mem_triangleSet hz'.1
    obtain ⟨hX0, hX1⟩ := holeX_mem_of_mem_triangleSet hM
    obtain ⟨hX0', hX1'⟩ := holeX_mem_of_mem_triangleSet hM'
    have := cornerZero_injOn ⟨hM.1, by rw [heightOne_foldMirror]; linarith, hX0, hX1⟩
      ⟨hM'.1, by rw [heightOne_foldMirror]; linarith, hX0', hX1'⟩ heq''
    rw [← foldMirror_foldMirror z, this, foldMirror_foldMirror]
  · exact bridgeTwo_injOn hy hy' (c1.symm.trans c1')
  · exact cornerInf_injOn ⟨hy, hz.1.2.1, hz.1.2.2.1⟩ ⟨hy', hz'.1.2.1, hz'.1.2.2.1⟩
      (d1.symm.trans d1')

end GC.Seifert
