import DifferentialGeometry.Analysis.ODE.SaddleBandCurve
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.LeftInverse
import DifferentialGeometry.Topology.Morse.Attachment.ModelCell
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

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
      (show ContDiff ℝ ∞ (fun u : ℝ => u ^ 2 + 2 * s) by fun_prop).sqrt
        (fun u => ne_of_gt (by positivity)))
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
  have ht : 0 < 1 - z.1 ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hz.2) (by linarith [hz.1] : 0 < z.1 + 1)]
  have hpos : 0 < z.2 ^ 2 + 2 * s := by positivity
  nlinarith [mul_pos ht hpos]

theorem mapsTo_saddleBandChart_ball {s R h : ℝ} (hs : 0 < s) (hR : 0 < R)
    (hsmall : 2 * h ^ 2 + 2 * s < R ^ 2) :
    MapsTo (saddleBandChart hs) (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) (ball 0 R) := by
  rintro ⟨t, u⟩ ⟨ht, hu⟩
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 0 ≤ t + 1)]
  have hu2 : u ^ 2 ≤ h ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (by linarith [hu.1] : 0 ≤ u + h)]
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

theorem exists_partialDiffeomorph_saddleBandLevelCurve_on {s σ : ℝ}
    (hσ : σ ^ 2 = 1) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUdom : U ⊆ {z | z.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < z.1 + s * z.2 ^ 2}) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      χ.source = U ∧
      (χ : (ℝ × ℝ) → ℝ × ℝ) = (fun z => saddleBandLevelCurve s z.1 σ z.2) ∧
      (χ.symm : (ℝ × ℝ) → ℝ × ℝ) =
        (fun z => ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun z => saddleBandLevelCurve s z.1 σ z.2
  let g : ℝ × ℝ → ℝ × ℝ := fun z =>
    ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)
  have hgf : LeftInvOn g f U := by
    intro z hz
    have hdom := hUdom hz
    apply Prod.ext
    · have h := saddleBandLevelCurve_height_of_nonneg hdom.2.le hσ hdom.1 (0 : ℝ)
      change (1 - (f z).1 ^ 2) * ((f z).2 ^ 2 + 2 * s) / 2 - s = z.1
      dsimp only [f]
      linarith
    · rfl
  have hf : ContDiffOn ℝ ∞ f U := (contDiffOn_saddleBandLevelCurve_family s σ).mono hUdom
  have hg : ContDiff ℝ ∞ g := by fun_prop
  obtain ⟨χ, hsource, _, hfun, hinv⟩ := hgf.exists_partialDiffeomorph
    hU hf.contMDiffOn (fun _ _ => hg.contMDiff.contMDiffAt) rfl
  exact ⟨χ, hsource, hfun, hinv⟩

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

open DifferentialGeometry.Analysis.ODE in
theorem eq_saddleBandLevelCurve_of_isIntegralCurveOn
    {γ : ℝ → ℝ × ℝ} {δ s τ σ u : ℝ} (hδ : 0 < δ)
    (hγ : IsIntegralCurveOn γ (fun _ => saddleBandVectorField) (Icc (-δ) δ))
    (hreg : ∀ t ∈ Icc (-δ) δ, (1 - (γ t).1 ^ 2) * (γ t).2 ≠ 0)
    (hinit : γ 0 = saddleBandLevelCurve s τ σ u)
    (hτ : δ < τ + s * u ^ 2) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    EqOn γ (fun t => saddleBandLevelCurve s (τ + t) σ u) (Icc (-δ) δ) := by
  let η : ℝ → ℝ × ℝ := fun t => saddleBandLevelCurve s (τ + t) σ u
  have hpos (t : ℝ) (ht : t ∈ Icc (-δ) δ) : 0 < τ + t + s * u ^ 2 := by
    linarith [ht.1]
  have hηd (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      HasDerivAt η (saddleBandVectorField (η t)) t := by
    have htadd : HasDerivAt (fun r : ℝ => τ + r) 1 t := by
      simpa using (hasDerivAt_id t).const_add τ
    convert (hasDerivAt_saddleBandLevelCurve_time_of_pos (hpos t ht) hσ hu).scomp t htadd
      using 1 <;>
      first | rfl | simp [η]
  have hη : ContinuousOn η (Icc (-δ) δ) :=
    fun t ht => (hηd t ht).continuousAt.continuousWithinAt
  let S := γ '' Icc (-δ) δ ∪ η '' Icc (-δ) δ
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hγ.continuousOn).union
      (isCompact_Icc.image_of_continuousOn hη)
  have hSreg : S ⊆ {z : ℝ × ℝ | (1 - z.1 ^ 2) * z.2 ≠ 0} := by
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact hreg t ht
    · exact saddleBandLevelCurve_regular_of_pos (hpos t ht)
        (by rintro rfl; norm_num at hσ) hu
  obtain ⟨L, hL⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS (f := saddleBandVectorField) (by
      intro z hz
      have ho : IsOpen {z : ℝ × ℝ | (1 - z.1 ^ 2) * z.2 ≠ 0} :=
        isOpen_ne.preimage (by fun_prop)
      have hd := (contDiffOn_saddleBandVectorField.contDiffAt (ho.mem_nhds (hSreg hz))).of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
      obtain ⟨L, T, hT, hLT⟩ := hd.exists_lipschitzOnWith
      exact ⟨L, T, mem_nhdsWithin_of_mem_nhds hT, hLT⟩)
  exact ODE_solution_unique_of_mem_Icc (s := fun _ => S) (fun _ _ => hL)
    (show 0 ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)
    hγ.continuousOn
    (fun t ht => (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => Or.inl ⟨t, Ioo_subset_Icc_self ht, rfl⟩) hη
    (fun t ht => hηd t (Ioo_subset_Icc_self ht))
    (fun t ht => Or.inr ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
    (by simpa [η] using hinit)

open DifferentialGeometry.Analysis.ODE (saddleBandCurve) in
theorem saddleBandCurve_eq_saddleBandLevelCurve
    {z : ℝ × ℝ} {s σ t : ℝ} (hσ : σ ^ 2 = 1)
    (hu : 1 - z.1 ^ 2 ≠ 0) (hv : 0 < σ * z.2)
    (ht : 0 ≤ 1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) :
    saddleBandCurve z t = saddleBandLevelCurve s
      ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s + t) σ z.1 := by
  have hvne : z.2 ≠ 0 := by intro hz; rw [hz, mul_zero] at hv; exact lt_irrefl _ hv
  have habs : σ * |z.2| = z.2 := by
    rcases (sq_eq_one_iff.mp hσ) with hσ | hσ
    · subst σ
      rw [one_mul] at hv
      rw [abs_of_pos hv, one_mul]
    · subst σ
      have hz : z.2 < 0 := by linarith
      rw [abs_of_neg hz]
      ring
  apply Prod.ext
  · rfl
  change Real.sqrt (1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / ‖z.2‖ ^ 2) * z.2 =
    σ * Real.sqrt (2 * (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s + t) + s * z.1 ^ 2) /
      (1 - z.1 ^ 2))
  rw [Real.norm_eq_abs, sq_abs]
  have hrad : 2 * (((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s + t) + s * z.1 ^ 2) / (1 - z.1 ^ 2) =
      (1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) * z.2 ^ 2 := by
    field_simp
    ring
  rw [hrad, Real.sqrt_mul ht, Real.sqrt_sq_eq_abs]
  calc
    _ = Real.sqrt (1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) * (σ * |z.2|) :=
      congrArg (fun x => Real.sqrt (1 + 2 * (1 - z.1 ^ 2)⁻¹ * t / z.2 ^ 2) * x) habs.symm
    _ = _ := by ring

open DifferentialGeometry.Analysis.ODE (saddleBandCurve_zero) in
theorem eq_saddleBandLevelCurve_of_height_eq_of_lower_bound
    {s τ σ v₀ : ℝ} (hs : 0 ≤ s) (hσ : σ ^ 2 = 1)
    (hv₀ : 0 ≤ v₀) (hv₀τ : v₀ ^ 2 < 2 * τ)
    {z : ℝ × ℝ} (hbottom : -v₀ ≤ σ * z.2)
    (hlevel : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = s + τ) :
    z = saddleBandLevelCurve s τ σ z.1 := by
  have hzpos : 0 < σ * z.2 := by
    by_contra hn
    have hzle : σ * z.2 ≤ 0 := le_of_not_gt hn
    have hsq : (σ * z.2) ^ 2 = z.2 ^ 2 := by rw [mul_pow, hσ, one_mul]
    have hzsq : z.2 ^ 2 ≤ v₀ ^ 2 := by nlinarith
    have hprod := mul_nonneg (sq_nonneg z.1)
      (add_nonneg (sq_nonneg z.2) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs))
    nlinarith
  have hden : 1 - z.1 ^ 2 ≠ 0 := by
    intro hd
    rw [hd, zero_mul, zero_div] at hlevel
    nlinarith only [hlevel, hs, hv₀τ, sq_nonneg v₀]
  have hzcurve := saddleBandCurve_eq_saddleBandLevelCurve (s := s) (t := 0)
    hσ hden hzpos (by simp)
  rwa [saddleBandCurve_zero, hlevel, show s + τ - s + 0 = τ by ring] at hzcurve

theorem exists_compact_saddleBandLevelCurve_parameter_neighborhood
    {E : Type*} [TopologicalSpace E] (B : (ℝ × ℝ) → E) (hB : Continuous B)
    {s σ : ℝ} {T : Set ℝ} {K : Set (ℝ × ℝ)} (hT : IsCompact T) (hK : IsCompact K)
    (hreg : ∀ t ∈ T, ∀ z ∈ K, z.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < t + z.1 + s * z.2 ^ 2)
    {U : Set (ℝ × E)} (hU : IsOpen U)
    (htrace : ∀ t ∈ T, ∀ z ∈ K, (t, B (saddleBandLevelCurve s (t + z.1) σ z.2)) ∈ U)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ W ∧
      ∀ t ∈ T, ∀ z ∈ K',
        z.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < t + z.1 + s * z.2 ^ 2 ∧
          (t, B (saddleBandLevelCurve s (t + z.1) σ z.2)) ∈ U := by
  let D := {p : ℝ × (ℝ × ℝ) |
    p.2.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < p.1 + p.2.1 + s * p.2.2 ^ 2}
  let f := fun p : ℝ × (ℝ × ℝ) => (p.1, B (saddleBandLevelCurve s (p.1 + p.2.1) σ p.2.2))
  have hD : IsOpen D := (isOpen_Ioo.preimage (continuous_snd.snd)).inter
    (isOpen_lt continuous_const
      ((continuous_fst.add continuous_snd.fst).add
        (continuous_const.mul (continuous_snd.snd.pow 2))))
  have hf : ContinuousOn f D := by
    apply continuousOn_fst.prodMk
    apply hB.comp_continuousOn
    apply (contDiffOn_saddleBandLevelCurve_family s σ).continuousOn.comp
      ((continuousOn_fst.add continuousOn_snd.fst).prodMk continuousOn_snd.snd)
    exact fun _ hp => hp
  have hsub : T ×ˢ K ⊆ D ∩ f ⁻¹' U := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact ⟨hreg t ht z hz, htrace t ht z hz⟩
  obtain ⟨T', V, _, hV, hTT', hKV, hTV⟩ := generalized_tube_lemma hT hK
    (hf.isOpen_inter_preimage hD hU) hsub
  obtain ⟨K', hK'compact, hK'int, hK'V⟩ := exists_compact_between hK (hV.inter hW)
    (subset_inter hKV hKW)
  refine ⟨K', hK'compact, hK'int, hK'V.trans inter_subset_right, ?_⟩
  intro t ht z hz
  have hp := hTV (a := (t, z)) ⟨hTT' ht, (hK'V hz).1⟩
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem saddleBandLevelCurve_mem_rectangle_of_le
    {s t τ σ u h ρ : ℝ} (ht : t ≤ τ) (hu : u ∈ Ioo (-1 : ℝ) 1)
    (hupper : saddleBandLevelCurve s τ σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) :
    saddleBandLevelCurve s t σ u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ := by
  refine ⟨hupper.1, ?_⟩
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  have hrad : 2 * (t + s * u ^ 2) / (1 - u ^ 2) ≤
      2 * (τ + s * u ^ 2) / (1 - u ^ 2) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have hmul := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) (abs_nonneg σ)
  have htop : |σ| * Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2)) ≤ ρ := by
    have hh := abs_le.mpr hupper.2
    simpa only [saddleBandLevelCurve, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hh
  apply abs_le.mp
  change |σ * Real.sqrt (2 * (t + s * u ^ 2) / (1 - u ^ 2))| ≤ ρ
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hmul.trans htop

theorem saddleBandLevelCurve_flow_radicand {s τ t σ u : ℝ}
    (hτ : 0 < τ + s * u ^ 2) (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    1 + 2 * (1 - u ^ 2)⁻¹ * (t - τ) / (saddleBandLevelCurve s τ σ u).2 ^ 2 =
      (t + s * u ^ 2) / (τ + s * u ^ 2) := by
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  have hrad : 0 ≤ 2 * (τ + s * u ^ 2) / (1 - u ^ 2) := by positivity
  have hsnd : (saddleBandLevelCurve s τ σ u).2 ^ 2 =
      2 * (τ + s * u ^ 2) / (1 - u ^ 2) := by
    simp only [saddleBandLevelCurve, mul_pow, hσ, one_mul, Real.sq_sqrt hrad]
  rw [hsnd]
  have hτne : τ + u ^ 2 * s ≠ 0 := by nlinarith
  field_simp [hτ.ne', hτne, hden.ne']
  ring

open DifferentialGeometry.Analysis.ODE (saddleBandCurve) in
theorem saddleBandCurve_saddleBandLevelCurve {s τ t σ u : ℝ}
    (hτ : 0 < τ + s * u ^ 2) (ht : 0 ≤ t + s * u ^ 2)
    (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    saddleBandCurve (saddleBandLevelCurve s τ σ u) (t - τ) =
      saddleBandLevelCurve s t σ u := by
  have hden : 0 < 1 - u ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < u + 1)]
  have hsign : 0 < σ * (saddleBandLevelCurve s τ σ u).2 := by
    change 0 < σ * (σ * Real.sqrt (2 * (τ + s * u ^ 2) / (1 - u ^ 2)))
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
    exact Real.sqrt_pos.mpr (by positivity)
  have hrad : 0 ≤ 1 + 2 * (1 - (saddleBandLevelCurve s τ σ u).1 ^ 2)⁻¹ * (t - τ) /
      (saddleBandLevelCurve s τ σ u).2 ^ 2 := by
    change 0 ≤ 1 + 2 * (1 - u ^ 2)⁻¹ * (t - τ) / (saddleBandLevelCurve s τ σ u).2 ^ 2
    rw [saddleBandLevelCurve_flow_radicand hτ hσ hu]
    exact div_nonneg ht hτ.le
  rw [saddleBandCurve_eq_saddleBandLevelCurve hσ hden.ne' hsign hrad (s := s)]
  have hh := saddleBandLevelCurve_height_of_nonneg hτ.le hσ hu (0 : ℝ)
  congr 1
  linarith

theorem mem_rectangle_of_saddle_band_height_le {s τ h ρ : ℝ} {z : ℝ × ℝ}
    (hu : z.1 ∈ Ioo (-1 : ℝ) 1)
    (hheight : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ≤ s + τ)
    (hupper : saddleBandLevelCurve s τ 1 z.1 ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) :
    z ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ := by
  have hden : 0 < 1 - z.1 ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < z.1 + 1)]
  have hsq : z.2 ^ 2 ≤ 2 * (τ + s * z.1 ^ 2) / (1 - z.1 ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have htop : Real.sqrt (2 * (τ + s * z.1 ^ 2) / (1 - z.1 ^ 2)) ≤ ρ := by
    simpa only [saddleBandLevelCurve, one_mul] using hupper.2.2
  exact ⟨hupper.1, abs_le.mp ((Real.abs_le_sqrt hsq).trans htop)⟩


theorem isCompact_saddle_band_graph_strip {s h a b : ℝ}
    (hh1 : h < 1) :
    IsCompact {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc a b ∧ |p.2.1| ≤ h ∧
      (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1} := by
  by_cases hh : 0 ≤ h
  · let R := 2 * (|s| + max b 0) / (1 - h ^ 2) + 1
    have hden : 0 < 1 - h ^ 2 := by nlinarith
    have hR : 0 ≤ 2 * (|s| + max b 0) / (1 - h ^ 2) := by positivity
    have hc : IsClosed {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc a b ∧ |p.2.1| ≤ h ∧
        (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1} :=
      (isClosed_Icc.preimage continuous_fst).inter
        ((isClosed_le (continuous_snd.fst.abs) continuous_const).inter
          (isClosed_eq (by fun_prop) (by fun_prop)))
    apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hc
      (show _ ⊆ Icc a b ×ˢ (Icc (-h) h ×ˢ Icc (-R) R) from ?_)
    intro p hp
    have hu : p.2.1 ^ 2 ≤ h ^ 2 := by nlinarith [sq_abs p.2.1, abs_nonneg p.2.1, hp.2.1]
    have hu1 : 0 ≤ 1 - p.2.1 ^ 2 := by linarith
    have hmul := mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg p.2.2)
    have hsprod : s * p.2.1 ^ 2 ≤ |s| := by
      calc
        s * p.2.1 ^ 2 ≤ |s| * p.2.1 ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self s) (sq_nonneg p.2.1)
        _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
        _ = |s| := mul_one _
    have hv : p.2.2 ^ 2 ≤ 2 * (|s| + max b 0) / (1 - h ^ 2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [hp.2.2, hp.1.2, le_max_left b 0]
    have hvabs : |p.2.2| ≤ R := by
      dsimp only [R]
      nlinarith [sq_abs p.2.2, sq_nonneg (|p.2.2| - 1)]
    exact ⟨hp.1, abs_le.mp hp.2.1, abs_le.mp hvabs⟩
  · have hempty : {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc a b ∧ |p.2.1| ≤ h ∧
        (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + p.1} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hh ((abs_nonneg p.2.1).trans hp.2.1)
    rw [hempty]
    exact isCompact_empty

open DifferentialGeometry.Analysis.ODE
  (saddleBandCurve saddleBandCurve_zero saddleBandCurve_height) in
theorem image_saddleBand_graph_time_change
    {A : Type*} {τ : A → ℝ} {ψ : A × ℝ → ℝ} {U : Set (A × (ℝ × ℝ))}
    (hU : ∀ p ∈ U, ψ (p.1, p.2.1) = 0 ∨
      (1 - p.2.1 ^ 2 ≠ 0 ∧ p.2.2 ≠ 0 ∧
        0 ≤ 1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * ψ (p.1, p.2.1) / p.2.2 ^ 2)) (s : ℝ) :
    (fun p : A × (ℝ × ℝ) => (p.1, saddleBandCurve p.2 (ψ (p.1, p.2.1)))) ''
        (U ∩ {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 = s + τ p.1}) =
      ((fun p : A × (ℝ × ℝ) => (p.1, saddleBandCurve p.2 (ψ (p.1, p.2.1)))) '' U) ∩
        {p | (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 =
          s + τ p.1 + ψ (p.1, p.2.1)} := by
  have hheight (p : A × (ℝ × ℝ)) (hp : p ∈ U) :
      (1 - (saddleBandCurve p.2 (ψ (p.1, p.2.1))).1 ^ 2) *
          ((saddleBandCurve p.2 (ψ (p.1, p.2.1))).2 ^ 2 + 2 * s) / 2 =
        (1 - p.2.1 ^ 2) * (p.2.2 ^ 2 + 2 * s) / 2 + ψ (p.1, p.2.1) := by
    rcases hU p hp with hz | hr
    · rw [hz, saddleBandCurve_zero, add_zero]
    · simpa only [zero_add] using saddleBandCurve_height hr.1 hr.2.1 hr.2.2 0 s
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hq⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    change (1 - (saddleBandCurve p.2 (ψ (p.1, p.2.1))).1 ^ 2) *
        ((saddleBandCurve p.2 (ψ (p.1, p.2.1))).2 ^ 2 + 2 * s) / 2 = _
    rw [hheight p hp, hq]
    rfl
  · rintro ⟨⟨p, hp, rfl⟩, hq⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    change (1 - (saddleBandCurve p.2 (ψ (p.1, p.2.1))).1 ^ 2) *
        ((saddleBandCurve p.2 (ψ (p.1, p.2.1))).2 ^ 2 + 2 * s) / 2 = _ at hq
    rw [hheight p hp] at hq
    exact add_right_cancel hq

theorem saddle_band_negative_side_iff_height_le
    {s σ u v v₀ : ℝ} (hσ : σ ^ 2 = 1) (hu : u ∈ Ioo (-1 : ℝ) 1)
    (hv : σ * v < 0) (hv₀ : 0 ≤ v₀) :
    -v₀ ≤ σ * v ↔
      (1 - u ^ 2) * (v ^ 2 + 2 * s) / 2 - s ≤
        v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * u ^ 2 := by
  have hup : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hsquare : (σ * v) ^ 2 = v ^ 2 := by rw [mul_pow, hσ, one_mul]
  have hside : -v₀ ≤ σ * v ↔ v ^ 2 ≤ v₀ ^ 2 := by
    constructor
    · intro h
      nlinarith [sq_nonneg (v₀ + σ * v)]
    · intro h
      nlinarith [sq_nonneg (v₀ - σ * v)]
  rw [hside]
  have heq : (1 - u ^ 2) * (v ^ 2 + 2 * s) / 2 - s -
      (v₀ ^ 2 / 2 - (s + v₀ ^ 2 / 2) * u ^ 2) =
      (1 - u ^ 2) * (v ^ 2 - v₀ ^ 2) / 2 := by ring
  constructor
  · intro h
    have := mul_nonpos_of_nonneg_of_nonpos hup.le (sub_nonpos.mpr h)
    linarith
  · intro h
    have : (1 - u ^ 2) * (v ^ 2 - v₀ ^ 2) ≤ 0 := by linarith
    by_contra hnot
    have hp : 0 < v ^ 2 - v₀ ^ 2 := sub_pos.mpr (lt_of_not_ge hnot)
    exact (not_lt_of_ge this) (mul_pos hup hp)

theorem exists_partialDiffeomorph_saddle_band_negative_half_strip
    {s σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      χ.source = {z | z.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < z.1 + s * z.2 ^ 2} ∧
      χ.target = {z | z.1 ∈ Ioo (-1 : ℝ) 1 ∧ σ * z.2 < 0} ∧
      (χ : (ℝ × ℝ) → ℝ × ℝ) = (fun z => saddleBandLevelCurve s z.1 (-σ) z.2) ∧
      (χ.symm : (ℝ × ℝ) → ℝ × ℝ) =
        (fun z => ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)) := by
  have hnegσ : (-σ) ^ 2 = 1 := by simpa only [neg_sq] using hσ
  have hU : IsOpen {z : ℝ × ℝ | z.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < z.1 + s * z.2 ^ 2} :=
    (isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_lt continuous_const
        (show Continuous (fun z : ℝ × ℝ => z.1 + s * z.2 ^ 2) by fun_prop))
  obtain ⟨χ, hsource, hfun, hinv⟩ := exists_partialDiffeomorph_saddleBandLevelCurve_on
    (s := s) hnegσ hU Subset.rfl
  refine ⟨χ, hsource, ?_, hfun, hinv⟩
  ext z
  constructor
  · intro hz
    let p : ℝ × ℝ := χ.symm z
    have hp := χ.map_target hz
    rw [hsource] at hp
    change p.2 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < p.1 + s * p.2 ^ 2 at hp
    have hright := χ.right_inv hz
    rw [hfun] at hright
    change saddleBandLevelCurve s p.1 (-σ) p.2 = z at hright
    have hupos : 0 < 1 - p.2 ^ 2 := by nlinarith [hp.1.1, hp.1.2]
    have hrad : 0 < 2 * (p.1 + s * p.2 ^ 2) / (1 - p.2 ^ 2) :=
      div_pos (mul_pos (by norm_num) hp.2) hupos
    rw [← hright]
    refine ⟨hp.1, ?_⟩
    change σ * (-σ * Real.sqrt _) < 0
    rw [← mul_assoc, mul_neg, ← pow_two, hσ, neg_one_mul]
    exact neg_neg_of_pos (Real.sqrt_pos.2 hrad)
  · intro hz
    have hupos : 0 < 1 - z.1 ^ 2 := by nlinarith [hz.1.1, hz.1.2]
    have hv : z.2 ≠ 0 := by
      intro hv
      have hn := hz.2
      rw [hv, mul_zero] at hn
      exact lt_irrefl _ hn
    let p : ℝ × ℝ := ((1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s, z.1)
    have hp : p ∈ χ.source := by
      rw [hsource]
      refine ⟨hz.1, ?_⟩
      change 0 < (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s + s * z.1 ^ 2
      have heq : (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s + s * z.1 ^ 2 =
          (1 - z.1 ^ 2) * z.2 ^ 2 / 2 := by ring
      rw [heq]
      exact div_pos (mul_pos hupos (sq_pos_of_ne_zero hv)) (by norm_num)
    have heq := saddleBandCurve_eq_saddleBandLevelCurve (s := s) (t := 0)
      hnegσ hupos.ne' (by nlinarith [hz.2]) (by simp)
    simp only [DifferentialGeometry.Analysis.ODE.saddleBandCurve_zero, add_zero] at heq
    have hmap := χ.map_source hp
    rw [hfun] at hmap
    exact heq.symm ▸ hmap

end DifferentialGeometry.Topology.Morse
