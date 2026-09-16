import DifferentialGeometry.Analysis.ODE.SaddleBandCurve
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.LeftInverse
import DifferentialGeometry.Topology.Morse.Attachment.ModelCell
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

theorem fderiv_saddle_band_apply_vertical (c s : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)
      z (0, 1) = (1 - z.1 ^ 2) * z.2 := by
  have hd := ((((((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).const_sub 1).mul
    ((((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add_const (2 * s))).mul_const
      (2 : ℝ)⁻¹).const_add c
  simp only [Pi.mul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd'] at hd
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring


noncomputable def saddleBandChart {s : ℝ} (hs : 0 < s) :
    (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Diffeomorph.fiberwiseSmul (E := ℝ)
    (show ContDiff ℝ ∞ (fun u : ℝ => Real.sqrt (u ^ 2 + 2 * s)) from
      (show ContDiff ℝ ∞ (fun u : ℝ => u ^ 2 + 2 * s) by fun_prop).sqrt (fun u => ne_of_gt (by positivity)))
    (fun u => ne_of_gt (Real.sqrt_pos.2 (by positivity)))).trans
    (((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).symm.toDiffeomorph)

theorem saddleBandChart_apply_zero {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    saddleBandChart hs z 0 = Real.sqrt (z.2 ^ 2 + 2 * s) * z.1 := rfl

theorem saddleBandChart_apply_one {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    saddleBandChart hs z 1 = z.2 := rfl

theorem norm_saddleBandChart_sq {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    ‖saddleBandChart hs z‖ ^ 2 = z.1 ^ 2 * (z.2 ^ 2 + 2 * s) + z.2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, saddleBandChart_apply_zero, saddleBandChart_apply_one,
    mul_pow, Real.sq_sqrt (show 0 ≤ z.2 ^ 2 + 2 * s by positivity)]
  ring

theorem morseNormalForm_saddleBandChart {s : ℝ} (hs : 0 < s) (c : ℝ) (z : ℝ × ℝ) :
    CellAttachment.morseNormalForm (n := 2) (k := 1) (by omega) c
      (EuclideanSpace.equiv (Fin 2) ℝ (saddleBandChart hs z)) + s - c =
        (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 := by
  simp only [CellAttachment.morseNormalForm, Nat.reduceSub, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, CellAttachment.negIdx, CellAttachment.posIdx]
  change c + 1 / 2 * (-(saddleBandChart hs z 0) ^ 2 +
    (saddleBandChart hs z 1) ^ 2) + s - c = _
  rw [saddleBandChart_apply_zero, saddleBandChart_apply_one]
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ z.2 ^ 2 + 2 * s by positivity)]
  ring

theorem morseNormalForm_saddleBandChart_eq_iff {s : ℝ} (hs : 0 < s)
    (c : ℝ) (z : ℝ × ℝ) :
    CellAttachment.morseNormalForm (n := 2) (k := 1) (by omega) c
      (EuclideanSpace.equiv (Fin 2) ℝ (saddleBandChart hs z)) + s = c ↔
      z.1 = -1 ∨ z.1 = 1 := by
  have heq := morseNormalForm_saddleBandChart hs c z
  have hpos : 0 < z.2 ^ 2 + 2 * s := by positivity
  constructor
  · intro h
    have hz : z.1 ^ 2 = 1 := by nlinarith
    exact (sq_eq_one_iff.mp hz).symm
  · rintro (h | h) <;> rw [h] at heq <;> nlinarith

theorem morseNormalForm_saddleBandChart_gt {s : ℝ} (hs : 0 < s)
    (c : ℝ) (z : ℝ × ℝ) (hz : z.1 ∈ Ioo (-1 : ℝ) 1) :
    c < CellAttachment.morseNormalForm (n := 2) (k := 1) (by omega) c
      (EuclideanSpace.equiv (Fin 2) ℝ (saddleBandChart hs z)) + s := by
  have heq := morseNormalForm_saddleBandChart hs c z
  have ht : 0 < 1 - z.1 ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hz.2) (by linarith [hz.1] : 0 < z.1 + 1)]
  have hpos : 0 < z.2 ^ 2 + 2 * s := by positivity
  nlinarith [mul_pos ht hpos]

theorem mapsTo_saddleBandChart_ball {s R h : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hsmall : 2 * h ^ 2 + 2 * s < R ^ 2) :
    MapsTo (saddleBandChart hs) (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) (ball 0 R) := by
  rintro ⟨t, u⟩ ⟨ht, hu⟩
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 0 ≤ t + 1)]
  have hu2 : u ^ 2 ≤ h ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (by linarith [hu.1] : 0 ≤ u + h)]
  have hn := norm_saddleBandChart_sq hs (t, u)
  simp only [mem_ball, dist_zero_right]
  dsimp only at hn
  have hterm := mul_nonneg (sub_nonneg.mpr ht2) (show 0 ≤ u ^ 2 + 2 * s by positivity)
  nlinarith [norm_nonneg (saddleBandChart hs (t, u))]

theorem exists_saddle_band_of_eqOn {s R c : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hsmall : 2 * s < R ^ 2) {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hg : EqOn g (fun y => CellAttachment.morseNormalForm (n := 2) (k := 1)
      (by omega) c (EuclideanSpace.equiv (Fin 2) ℝ y) + s) (ball 0 R)) :
    ∃ h > 0,
      MapsTo (saddleBandChart hs) (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) (ball 0 R) ∧
      (saddleBandChart hs ⁻¹' {y | g y = c}) ∩ (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) =
        {-1, 1} ×ˢ Icc (-h) h ∧
      ∀ z ∈ Ioo (-1 : ℝ) 1 ×ˢ Icc (-h) h, c < g (saddleBandChart hs z) := by
  let h := Real.sqrt ((R ^ 2 - 2 * s) / 4)
  have hh : 0 < h := Real.sqrt_pos.2 (by linarith)
  have hh2 : h ^ 2 = (R ^ 2 - 2 * s) / 4 := Real.sq_sqrt (by linarith)
  have hmap := mapsTo_saddleBandChart_ball hs hR (by nlinarith : 2 * h ^ 2 + 2 * s < R ^ 2)
  refine ⟨h, hh, hmap, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨hz, hzrect⟩
      have heq := hg (hmap hzrect)
      have hedge := (morseNormalForm_saddleBandChart_eq_iff hs c z).mp (heq.symm.trans hz)
      exact ⟨by simpa only [mem_insert_iff, mem_singleton_iff] using hedge, hzrect.2⟩
    · rintro ⟨hz, hu⟩
      have hedge : z.1 = -1 ∨ z.1 = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hz
      have ht : z.1 ∈ Icc (-1 : ℝ) 1 := by rcases hedge with h | h <;> rw [h] <;> norm_num
      refine ⟨?_, ht, hu⟩
      change g (saddleBandChart hs z) = c
      rw [hg (hmap ⟨ht, hu⟩)]
      exact (morseNormalForm_saddleBandChart_eq_iff hs c z).mpr hedge
  · intro z hz
    rw [hg (hmap ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)]
    exact morseNormalForm_saddleBandChart_gt hs c z hz.1

noncomputable def saddleBandLevelCurve (s t σ u : ℝ) : ℝ × ℝ :=
  (u, σ * Real.sqrt (2 * (t + s * u ^ 2) / (1 - u ^ 2)))

theorem saddleBandLevelCurve_height_of_nonneg {s t σ u : ℝ}
    (ht : 0 ≤ t + s * u ^ 2) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) (c : ℝ) :
    c + (1 - (saddleBandLevelCurve s t σ u).1 ^ 2) *
      ((saddleBandLevelCurve s t σ u).2 ^ 2 + 2 * s) / 2 = c + s + t := by
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  have hrad : 0 ≤ 2 * (t + s * u ^ 2) / (1 - u ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) ht) hden.le
  simp only [saddleBandLevelCurve, mul_pow, hσ, one_mul, Real.sq_sqrt hrad]
  field_simp
  ring

theorem saddleBandLevelCurve_height {s t σ u : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) (c : ℝ) :
    c + (1 - (saddleBandLevelCurve s t σ u).1 ^ 2) *
      ((saddleBandLevelCurve s t σ u).2 ^ 2 + 2 * s) / 2 = c + s + t :=
  saddleBandLevelCurve_height_of_nonneg (add_nonneg ht.le (mul_nonneg hs (sq_nonneg u)))
    hσ hu c

theorem saddleBandLevelCurve_regular_of_pos {s t σ u : ℝ}
    (ht : 0 < t + s * u ^ 2) (hσ : σ ≠ 0) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    (1 - (saddleBandLevelCurve s t σ u).1 ^ 2) * (saddleBandLevelCurve s t σ u).2 ≠ 0 := by
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  exact mul_ne_zero hden.ne' (mul_ne_zero hσ (Real.sqrt_pos.mpr
    (div_pos (mul_pos (by norm_num) ht) hden)).ne')

theorem saddleBandLevelCurve_regular {s t σ u : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) (hσ : σ ≠ 0) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    (1 - (saddleBandLevelCurve s t σ u).1 ^ 2) * (saddleBandLevelCurve s t σ u).2 ≠ 0 :=
  saddleBandLevelCurve_regular_of_pos (add_pos_of_pos_of_nonneg ht (mul_nonneg hs (sq_nonneg u)))
    hσ hu

theorem contDiffOn_saddleBandLevelCurve_family (s σ : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => saddleBandLevelCurve s z.1 σ z.2)
      {z | z.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < z.1 + s * z.2 ^ 2} := by
  apply contDiffOn_snd.prodMk
  apply contDiffOn_const.mul
  apply ContDiffOn.sqrt
  · exact (contDiffOn_const.mul (contDiffOn_fst.add
      (contDiffOn_const.mul (contDiffOn_snd.pow 2)))).div
        (contDiffOn_const.sub (contDiffOn_snd.pow 2)) (fun z hz => by
          change 1 - z.2 ^ 2 ≠ 0
          nlinarith [hz.1.1, hz.1.2])
  · intro z hz
    have hden : 0 < 1 - z.2 ^ 2 := by nlinarith [hz.1.1, hz.1.2]
    exact (div_pos (mul_pos (by norm_num) hz.2) hden).ne'

theorem contDiffOn_saddleBandLevelCurve {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) (σ : ℝ) :
    ContDiffOn ℝ ∞ (saddleBandLevelCurve s t σ) (Ioo (-1 : ℝ) 1) :=
  (contDiffOn_saddleBandLevelCurve_family s σ).comp
    (contDiffOn_const.prodMk contDiffOn_id)
    (fun u hu => ⟨hu, add_pos_of_pos_of_nonneg ht (mul_nonneg hs (sq_nonneg u))⟩)

theorem exists_saddleBandLevelCurve_subset_open (s : ℝ) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hzero : (0, 0) ∈ U) :
    ∃ δ k : ℝ, 0 < δ ∧ 0 < k ∧ k < 1 ∧
      ∀ t ∈ Icc (0 : ℝ) δ, ∀ σ ∈ ({-1, 1} : Set ℝ),
        saddleBandLevelCurve s t σ '' Icc (-k) k ⊆ U := by
  let V : Set (ℝ × ℝ) := U ∩ (fun z : ℝ × ℝ => (z.1, -z.2)) ⁻¹' U
  have hV : IsOpen V := hU.inter (hU.preimage (continuous_fst.prodMk continuous_snd.neg))
  have hVzero : (0, 0) ∈ V := ⟨hzero, by simpa using hzero⟩
  let f : ℝ × ℝ → ℝ × ℝ := fun z => saddleBandLevelCurve s z.1 1 z.2
  have hf : ContinuousAt f (0, 0) := by
    have hden : ContinuousAt (fun z : ℝ × ℝ => 1 - z.2 ^ 2) (0, 0) := by fun_prop
    have hnum : ContinuousAt (fun z : ℝ × ℝ => 2 * (z.1 + s * z.2 ^ 2)) (0, 0) := by fun_prop
    exact continuousAt_snd.prodMk
      (continuousAt_const.mul ((hnum.div hden (by norm_num)).sqrt))
  have hfzero : f (0, 0) = (0, 0) := by simp [f, saddleBandLevelCurve]
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff.mp (hf (hfzero ▸ hV.mem_nhds hVzero))
  let k := min r 1 / 2
  have hk : 0 < k := half_pos (lt_min hr zero_lt_one)
  have hkr : k < r := by dsimp [k]; have := min_le_left r 1; linarith
  have hkone : k < 1 := by dsimp [k]; have := min_le_right r 1; linarith
  refine ⟨k, k, hk, hk, hkone, ?_⟩
  intro t ht σ hσ
  rintro z ⟨u, hu, rfl⟩
  have hd : dist (t, u) (0, 0) < r := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; exact ht.2.trans_lt hkr,
      by rw [Real.dist_eq, sub_zero]; exact (abs_le.mpr hu).trans_lt hkr⟩
  have hm := hfr hd
  rcases hσ with rfl | rfl
  · have hneg := hm.2
    simpa only [V, f, saddleBandLevelCurve, mem_preimage, one_mul, neg_mul, neg_one_mul] using hneg
  · exact hm.1


theorem exists_isCompact_saddleBandLevelCurve_subset_open {s : ℝ} (hs : 0 ≤ s)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U) :
    ∃ δ k : ℝ, 0 < δ ∧ 0 < k ∧ k < 1 ∧
      ∀ t ∈ Ioo (0 : ℝ) δ, ∀ σ ∈ ({-1, 1} : Set ℝ),
        let K := saddleBandLevelCurve s t σ '' Icc (-k) k
        IsCompact K ∧ IsConnected K ∧ K ⊆ U ∧
          (∀ z ∈ K, (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + t) ∧
          ∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0 := by
  obtain ⟨δ, k, hδ, hk, hkone, hsub⟩ := exists_saddleBandLevelCurve_subset_open s hU hzero
  refine ⟨δ, k, hδ, hk, hkone, ?_⟩
  intro t ht σ hσ
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσne : σ ≠ 0 := by intro h; rw [h] at hσsq; norm_num at hσsq
  have hinterval : Icc (-k) k ⊆ Ioo (-1 : ℝ) 1 := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans_lt hkone⟩
  have hc := (contDiffOn_saddleBandLevelCurve hs ht.1 σ).continuousOn.mono hinterval
  refine ⟨isCompact_Icc.image_of_continuousOn hc,
    (isConnected_Icc (by linarith : -k ≤ k)).image _ hc,
    hsub t ⟨ht.1.le, ht.2.le⟩ σ hσ, ?_, ?_⟩
  · rintro z ⟨u, hu, rfl⟩
    simpa only [zero_add] using saddleBandLevelCurve_height hs ht.1 hσsq (hinterval hu) 0
  · rintro z ⟨u, hu, rfl⟩
    exact saddleBandLevelCurve_regular hs ht.1 hσne (hinterval hu)

theorem exists_partialDiffeomorph_saddleBandLevelCurve {s σ : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      χ.source = Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (χ : (ℝ × ℝ) → ℝ × ℝ) = (fun z => saddleBandLevelCurve s z.1 σ z.2) ∧
      (χ.symm : (ℝ × ℝ) → ℝ × ℝ) =
        (fun z => ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)) := by
  let U := Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1
  let f : ℝ × ℝ → ℝ × ℝ := fun z => saddleBandLevelCurve s z.1 σ z.2
  let g : ℝ × ℝ → ℝ × ℝ := fun z =>
    ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)
  have hgf : LeftInvOn g f U := by
    intro z hz
    apply Prod.ext
    · have h := saddleBandLevelCurve_height hs hz.1 hσ hz.2 (0 : ℝ)
      change (1 - (f z).1 ^ 2) * ((f z).2 ^ 2 + 2 * s) / 2 - s = z.1
      dsimp only [f]
      linarith
    · rfl
  have hf : ContDiffOn ℝ ∞ f U :=
    (contDiffOn_saddleBandLevelCurve_family s σ).mono
      (fun z hz => ⟨hz.2, add_pos_of_pos_of_nonneg hz.1 (mul_nonneg hs (sq_nonneg z.2))⟩)
  have hg : ContDiff ℝ ∞ g := by fun_prop
  obtain ⟨χ, hsource, _, hfun, hinv⟩ := hgf.exists_partialDiffeomorph
    (isOpen_Ioi.prod isOpen_Ioo) hf.contMDiffOn (fun _ _ => hg.contMDiff.contMDiffAt) rfl
  exact ⟨χ, hsource, hfun, hinv⟩

open DifferentialGeometry.Analysis.ODE in
theorem hasDerivAt_saddleBandLevelCurve_time_of_pos {s τ σ u : ℝ}
    (hτ : 0 < τ + s * u ^ 2) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => saddleBandLevelCurve s t σ u)
      (saddleBandVectorField (saddleBandLevelCurve s τ σ u)) τ := by
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  have hrad : 0 < 2 * (τ + s * u ^ 2) / (1 - u ^ 2) :=
    div_pos (mul_pos (by norm_num) hτ) hden
  have hσne : σ ≠ 0 := by rintro rfl; norm_num at hσ
  have hsqrt := Real.sqrt_pos.mpr hrad
  have hd := (((((hasDerivAt_id τ).add_const (s * u ^ 2)).const_mul 2).div_const
    (1 - u ^ 2)).sqrt hrad.ne').const_mul σ
  apply ((hasDerivAt_const τ u).prodMk hd).congr_deriv
  apply Prod.ext
  · rfl
  change σ * (2 * 1 / (1 - u ^ 2) / (2 * Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2)))) =
    ((1 - u ^ 2) * (σ * Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2))))⁻¹
  field_simp
  simp only [hσ]

open DifferentialGeometry.Analysis.ODE in
theorem hasDerivAt_saddleBandLevelCurve_time {s τ σ u : ℝ}
    (hs : 0 ≤ s) (hτ : 0 < τ) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => saddleBandLevelCurve s t σ u)
      (saddleBandVectorField (saddleBandLevelCurve s τ σ u)) τ :=
  hasDerivAt_saddleBandLevelCurve_time_of_pos
    (add_pos_of_pos_of_nonneg hτ (mul_nonneg hs (sq_nonneg u))) hσ hu

end DifferentialGeometry.Topology.Morse
