import DifferentialGeometry.Topology.Manifold.RelativeSquareIsotopy
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section
open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem exists_compactly_supported_planar_isotopy
    (f : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hf : HasCompactSupport (fun z ↦ f z - z)) :
    ∃ H : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (H q.1).symm q.2) ∧
      H 0 = f ∧ H 1 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      ∃ K : Set ℂ, IsCompact K ∧ ∀ p z, z ∉ K → H p z = z ∧ (H p).symm z = z := by
  obtain ⟨R, hR, hsupp⟩ := hf.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hRn : 8 * R ≠ 0 := by positivity
  let c : ℂ := (1 / 2 : ℝ) + (1 / 2 : ℝ) • Complex.I
  have hLf : ContDiff ℝ ∞ (fun z : ℂ ↦ (8 * R)⁻¹ • z + c) := by
    have hs : ContDiff ℝ ∞ (fun z : ℂ ↦ (8 * R)⁻¹ • z) :=
      (contDiff_id : ContDiff ℝ ∞ (id : ℂ → ℂ)).const_smul ((8 * R)⁻¹)
    exact hs.add contDiff_const
  have hLi : ContDiff ℝ ∞ (fun z : ℂ ↦ (8 * R) • (z - c)) :=
    (contDiff_id.sub contDiff_const : ContDiff ℝ ∞ (fun z : ℂ ↦ z - c)).const_smul (8 * R)
  let L : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    { toEquiv :=
        { toFun := fun z ↦ (8 * R)⁻¹ • z + c
          invFun := fun z ↦ (8 * R) • (z - c)
          left_inv := fun z ↦ by
            change (8 * R) • (((8 * R)⁻¹ • z + c) - c) = z
            rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hRn, one_smul]
          right_inv := fun z ↦ by
            change (8 * R)⁻¹ • ((8 * R) • (z - c)) + c = z
            rw [smul_smul, inv_mul_cancel₀ hRn, one_smul, sub_add_cancel] }
      contMDiff_toFun := hLf.contMDiff
      contMDiff_invFun := hLi.contMDiff }
  have hL (z : ℂ) : L z = (8 * R)⁻¹ • z + c := rfl
  have hscale : 0 < (8 * R)⁻¹ := inv_pos.mpr (by positivity)
  have hscaleR : (8 * R)⁻¹ * R = 1 / 8 := by field_simp
  have hinside (z : ℂ) (hz : z ∈ tsupport (fun z ↦ f z - z)) :
      1 / 4 < (L z).re ∧ (L z).re < 3 / 4 ∧ 1 / 4 < (L z).im ∧ (L z).im < 3 / 4 := by
    have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hsupp hz
    have hre := abs_lt.mp (Complex.abs_re_le_norm z |>.trans_lt hzR)
    have him := abs_lt.mp (Complex.abs_im_le_norm z |>.trans_lt hzR)
    have hrlo := mul_lt_mul_of_pos_left hre.1 hscale
    have hrhi := mul_lt_mul_of_pos_left hre.2 hscale
    have hilo := mul_lt_mul_of_pos_left him.1 hscale
    have hihi := mul_lt_mul_of_pos_left him.2 hscale
    rw [hL]
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, c, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hfout (z : ℂ) (hz : z ∉ tsupport (fun z ↦ f z - z)) : f z = z :=
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun z ↦ f z - z) hz)
  let g := (L.symm.trans f).trans L
  have hg (z : ℂ) : g z = L (f (L.symm z)) := rfl
  have hgfix (z : ℂ)
      (hz : z.re ≤ 1 / 4 ∨ 1 - 1 / 4 ≤ z.re ∨ z.im ≤ 1 / 4 ∨ 1 - 1 / 4 ≤ z.im) : g z = z := by
    have hout : L.symm z ∉ tsupport (fun z ↦ f z - z) := by
      intro h
      have hi := hinside _ h
      rw [L.apply_symm_apply] at hi
      rcases hz with hz | hz | hz | hz <;> linarith [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
    rw [hg, hfout _ hout, L.apply_symm_apply]
  obtain ⟨J, hJ, hJi, hJzero, hJone, _, ε, hε, _, hJfix⟩ :=
    exists_relative_square_isotopy g (δ := 1 / 4) (by norm_num) hgfix
  let H (p : ℝ) := (L.trans (J p)).trans L.symm
  have hH : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ H q.1 q.2) :=
    L.symm.contMDiff.contDiff.comp
      (hJ.comp (contDiff_fst.prodMk (L.contMDiff.contDiff.comp contDiff_snd)))
  have hHi : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (H q.1).symm q.2) :=
    L.symm.contMDiff.contDiff.comp
      (hJi.comp (contDiff_fst.prodMk (L.contMDiff.contDiff.comp contDiff_snd)))
  let Q : Set ℂ := Complex.reProdIm (Icc 0 1) (Icc 0 1)
  let K : Set ℂ := L.symm '' Q
  have hK : IsCompact K := (isCompact_Icc.reProdIm isCompact_Icc).image L.symm.contMDiff.continuous
  have hHout (p : ℝ) (z : ℂ) (hz : z ∉ K) : H p z = z := by
    have hzQ : L z ∉ Q := by
      intro hi
      exact hz ⟨L z, hi, L.symm_apply_apply z⟩
    have hj : J p (L z) = L z := by
      apply hJfix p (L z)
      by_contra h
      push Not at h
      exact hzQ ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩,
        by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
    change L.symm (J p (L z)) = z
    rw [hj, L.symm_apply_apply]
  refine ⟨H, hH, hHi, ?_, ?_, K, hK, fun p z hz ↦ ⟨hHout p z hz, ?_⟩⟩
  · apply Diffeomorph.ext
    intro z
    change L.symm (J 0 (L z)) = f z
    rw [hJzero, hg, L.symm_apply_apply, L.symm_apply_apply]
  · apply Diffeomorph.ext
    intro z
    change L.symm (J 1 (L z)) = z
    rw [hJone]
    exact L.symm_apply_apply z
  · apply (H p).injective
    exact ((H p).apply_symm_apply z).trans (hHout p z hz).symm

end DifferentialGeometry.Topology.Manifold
