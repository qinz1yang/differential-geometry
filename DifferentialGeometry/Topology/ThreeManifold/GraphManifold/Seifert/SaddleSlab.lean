import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels
import DifferentialGeometry.Topology.Morse.CriticalPoints
import DifferentialGeometry.Topology.Morse.ModelTransport

/-!
# The pants as a one-saddle slab

Packet SP of the P1 elementarization survey (the crux of RG03). The part of a surface between two
regular levels of a Morse function that contains one two-sided critical point of index one, with
two boundary circles below and one above, is modelled by `planarModel 3` itself, so no planar
diffeomorphism is needed. Put `pantsLower z = q₊ z * q₋ z`, where `q± z = ‖z ∓ 3/2‖² - 1/4` cut
out the holes, `pantsUpper z = 9 - ‖z‖²` and `pantsHeight = pantsLower / (pantsLower + pantsUpper)`.
The denominator is `‖z‖⁴ + 3 ‖z‖² + 13 - 9 x² ≥ (x² - 3)² + 4`, `x = re z`, so `pantsHeight` is
smooth on `ℂ` and `pantsHeight ⁻¹' Icc 0 1 = planarModel 3` (`pantsHeight_preimage_Icc`). Level
`0` is the pair of hole circles and level `1` the outer circle; on `pantsSurface` the boundary
points are exactly the points of level `0` or `1`, and collar `j` lies on level `1` for `j = 0`
and on level `0` otherwise.

The differential is `(Q dP - P dQ) / D²` with `P = pantsLower`, `Q = pantsUpper`, `D = P + Q`.
On the model its `im`-component is `im z` times a positive factor, and on the real axis its
`re`-component is `x` times `-2 (s² - 18 s + 41) / D²`, `s = x²`, whose roots `9 ± 2 √10` avoid
`[0, 1] ∪ [4, 9]`. So `0` is the only critical point in the slab, with value `4/13` and Hessian
`diag (-82, 80) / 169`: it is nondegenerate of index one, also for the model `saddleModel` on
`MorseModel 2`. For one circle below and two above use `1 - pantsHeight`.

The naive model `{z | |x² - y²| ≤ 1 ∧ ‖z‖ ≤ 2}` of the saddle is star-shaped
(`starConvex_saddleCross`): it is the handle neighbourhood, a disc bounded by four level arcs and
four arcs of the circle, not the slab.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def pantsLower (z : ℂ) : ℝ := (z.re ^ 2 + z.im ^ 2 + 2) ^ 2 - 9 * z.re ^ 2

def pantsUpper (z : ℂ) : ℝ := 9 - z.re ^ 2 - z.im ^ 2

def pantsHeight (z : ℂ) : ℝ := pantsLower z / (pantsLower z + pantsUpper z)

theorem sq_norm_sub_real (z : ℂ) (c : ℝ) : ‖z - c‖ ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  ring

theorem pantsLower_eq (z : ℂ) : pantsLower z =
    (‖z - ((3 / 2 : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2) *
      (‖z - ((-(3 / 2) : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2) := by
  rw [sq_norm_sub_real, sq_norm_sub_real, pantsLower]
  ring

theorem pantsUpper_eq (z : ℂ) : pantsUpper z = 3 ^ 2 - ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, pantsUpper]
  ring

theorem four_le_pantsLower_add_pantsUpper (z : ℂ) : 4 ≤ pantsLower z + pantsUpper z := by
  unfold pantsLower pantsUpper
  nlinarith [sq_nonneg (z.re ^ 2 - 3), sq_nonneg z.im, sq_nonneg z.re,
    mul_nonneg (sq_nonneg z.im) (sq_nonneg z.re), sq_nonneg (z.im ^ 2)]

theorem pantsLower_add_pantsUpper_pos (z : ℂ) : 0 < pantsLower z + pantsUpper z :=
  lt_of_lt_of_le (by norm_num) (four_le_pantsLower_add_pantsUpper z)

theorem pantsUpper_nonneg_iff (z : ℂ) : 0 ≤ pantsUpper z ↔ ‖z‖ ≤ 3 := by
  rw [pantsUpper_eq, sub_nonneg]
  exact pow_le_pow_iff_left₀ (norm_nonneg z) (by norm_num) two_ne_zero

theorem pantsLower_nonneg_iff (z : ℂ) : 0 ≤ pantsLower z ↔
    1 / 2 ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 / 2 ≤ ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  have h3 := three_le_norm_sub_add_norm_sub z
  have h1 := norm_nonneg (z - ((3 / 2 : ℝ) : ℂ))
  have h2 := norm_nonneg (z - ((-(3 / 2) : ℝ) : ℂ))
  rw [pantsLower_eq]
  constructor
  · intro h
    by_contra hc
    rw [not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · have ha : ‖z - ((3 / 2 : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2 < 0 := by nlinarith
      have hb : 0 < ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
      nlinarith
    · have ha : 0 < ‖z - ((3 / 2 : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
      have hb : ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2 < 0 := by nlinarith
      nlinarith
  · rintro ⟨ha, hb⟩
    exact mul_nonneg (by nlinarith) (by nlinarith)

theorem pantsHeight_mem_Icc_iff (z : ℂ) : pantsHeight z ∈ Icc 0 1 ↔ z ∈ planarModel 3 := by
  have hD := pantsLower_add_pantsUpper_pos z
  rw [mem_planarModel_three, ← pantsUpper_nonneg_iff, ← pantsLower_nonneg_iff, mem_Icc,
    pantsHeight, div_nonneg_iff, div_le_one hD]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact ⟨by linarith, h.1⟩
    · exact absurd h.2 (not_le.mpr hD)
  · rintro ⟨hU, hL⟩
    exact ⟨Or.inl ⟨hL, hD.le⟩, by linarith⟩

theorem pantsHeight_preimage_Icc : pantsHeight ⁻¹' Icc 0 1 = planarModel 3 :=
  Set.ext pantsHeight_mem_Icc_iff

theorem isCompact_pantsHeight_preimage_Icc : IsCompact (pantsHeight ⁻¹' Icc 0 1) := by
  rw [pantsHeight_preimage_Icc]
  exact isCompact_planarModel (Or.inr rfl)

theorem isConnected_pantsHeight_preimage_Icc : IsConnected (pantsHeight ⁻¹' Icc 0 1) := by
  rw [pantsHeight_preimage_Icc]
  exact isConnected_planarModel 3

theorem pantsHeight_eq_zero_iff_pantsLower (z : ℂ) : pantsHeight z = 0 ↔ pantsLower z = 0 := by
  rw [pantsHeight, div_eq_zero_iff, or_iff_left (pantsLower_add_pantsUpper_pos z).ne']

theorem pantsHeight_eq_one_iff_pantsUpper (z : ℂ) : pantsHeight z = 1 ↔ pantsUpper z = 0 := by
  rw [pantsHeight, div_eq_one_iff_eq (pantsLower_add_pantsUpper_pos z).ne']
  constructor <;> intro h <;> linarith

theorem pantsHeight_eq_zero_iff (z : ℂ) : pantsHeight z = 0 ↔
    ‖z - ((3 / 2 : ℝ) : ℂ)‖ = 1 / 2 ∨ ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ = 1 / 2 := by
  rw [pantsHeight_eq_zero_iff_pantsLower, pantsLower_eq, mul_eq_zero, sub_eq_zero, sub_eq_zero,
    pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero,
    pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero]

theorem pantsHeight_eq_one_iff (z : ℂ) : pantsHeight z = 1 ↔ ‖z‖ = 3 := by
  rw [pantsHeight_eq_one_iff_pantsUpper, pantsUpper_eq, sub_eq_zero, eq_comm,
    pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero]

theorem pantsHeight_planarCircleMap (j : Fin 3) (t : Circle) :
    pantsHeight (planarCircleMap 3 j t) = if j.val = 0 then 1 else 0 := by
  have h := norm_planarCircleMap_sub 3 j t
  fin_cases j
  · simp only [planarCenter, planarRadius] at h
    norm_num at h
    simpa using (pantsHeight_eq_one_iff _).mpr h
  · simp only [planarCenter, planarRadius] at h
    norm_num at h
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    exact (pantsHeight_eq_zero_iff _).mpr (Or.inl (by simpa using h))
  · simp only [planarCenter, planarRadius] at h
    norm_num at h
    simp only [Fin.reduceFinMk, Fin.isValue, OfNat.ofNat_ne_zero, ↓reduceIte]
    exact (pantsHeight_eq_zero_iff _).mpr (Or.inr (by simpa using h))

theorem planarFunction_three_eq (z : ℂ) :
    planarFunction 3 z = -(pantsUpper z * pantsLower z) := by
  rw [planarFunction_three, pantsLower_eq, pantsUpper_eq]
  ring

theorem planarSet_three_isBoundaryPoint_iff (x : planarSet.{u} 3) :
    (𝓡∂ 2).IsBoundaryPoint x ↔ pantsHeight x.val.down = 0 ∨ pantsHeight x.val.down = 1 := by
  rw [planarSet_isBoundaryPoint_iff, planarFunction_three_eq, neg_eq_zero, mul_eq_zero,
    pantsHeight_eq_zero_iff_pantsLower, pantsHeight_eq_one_iff_pantsUpper, or_comm]

theorem pantsHeight_pantsPlanarBase_collar (j : Fin 3) (t : Circle) :
    pantsHeight (pantsPlanarBase.{u}.embedding (pantsPlanarBase.{u}.collar j (t, halfZero))) =
      if j.val = 0 then 1 else 0 := by
  rw [pantsPlanarBase.{u}.embedding_collar]
  exact pantsHeight_planarCircleMap j t

def pantsGradRe (z : ℂ) : ℝ := pantsUpper z * (4 * (z.re ^ 2 + z.im ^ 2) - 10) + 2 * pantsLower z

def pantsGradIm (z : ℂ) : ℝ := 4 * pantsUpper z * (z.re ^ 2 + z.im ^ 2 + 2) + 2 * pantsLower z

def pantsCoeffRe (z : ℂ) : ℝ := pantsGradRe z / (pantsLower z + pantsUpper z) ^ 2

def pantsCoeffIm (z : ℂ) : ℝ := pantsGradIm z / (pantsLower z + pantsUpper z) ^ 2

theorem contDiff_pantsLower : ContDiff ℝ ∞ pantsLower := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  unfold pantsLower
  fun_prop

theorem contDiff_pantsUpper : ContDiff ℝ ∞ pantsUpper := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  unfold pantsUpper
  fun_prop

theorem contDiff_pantsHeight : ContDiff ℝ ∞ pantsHeight :=
  contDiff_pantsLower.div (contDiff_pantsLower.add contDiff_pantsUpper)
    fun z => (pantsLower_add_pantsUpper_pos z).ne'

theorem contMDiff_pantsHeight_planarSet :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (fun x : planarSet.{u} 3 => pantsHeight x.val.down) :=
  contDiff_pantsHeight.contMDiff.comp (contMDiff_planarSet_down 3)

theorem contDiff_pantsCoeffRe : ContDiff ℝ ∞ pantsCoeffRe := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hL := contDiff_pantsLower
  have hU := contDiff_pantsUpper
  refine ContDiff.div ?_ ((hL.add hU).pow 2) fun z =>
    pow_ne_zero 2 (pantsLower_add_pantsUpper_pos z).ne'
  unfold pantsGradRe
  fun_prop

theorem contDiff_pantsCoeffIm : ContDiff ℝ ∞ pantsCoeffIm := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hL := contDiff_pantsLower
  have hU := contDiff_pantsUpper
  refine ContDiff.div ?_ ((hL.add hU).pow 2) fun z =>
    pow_ne_zero 2 (pantsLower_add_pantsUpper_pos z).ne'
  unfold pantsGradIm
  fun_prop

theorem hasFDerivAt_pantsHeight (z : ℂ) : HasFDerivAt pantsHeight
    ((z.re * pantsCoeffRe z) • Complex.reCLM + (z.im * pantsCoeffIm z) • Complex.imCLM) z := by
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hL := (((hre.pow 2).add (him.pow 2)).add_const 2).pow 2 |>.sub ((hre.pow 2).const_mul 9)
  have hU := ((hre.pow 2).const_sub 9).sub (him.pow 2)
  have hD := hL.add hU
  have hpos := pantsLower_add_pantsUpper_pos z
  have hinv := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt z hD
  have hH := hL.mul hinv
  convert hH using 1
  · funext w
    simp only [pantsHeight, pantsLower, pantsUpper, div_eq_mul_inv, comp_apply, Pi.mul_apply,
      Pi.add_apply, Pi.sub_apply]
  · unfold pantsCoeffRe pantsCoeffIm pantsGradRe pantsGradIm
    unfold pantsLower pantsUpper at hpos ⊢
    ext v
    simp only [add_apply, smul_apply, Complex.reCLM_apply, smul_eq_mul, Complex.imCLM_apply,
      Pi.add_apply, Pi.sub_apply, Nat.add_one_sub_one, pow_one, smul_add, nsmul_eq_mul,
      Nat.cast_ofNat, neg_smul, smul_neg, comp_apply, neg_apply, sub_apply]
    field_simp
    ring


theorem fderiv_pantsHeight (z : ℂ) : fderiv ℝ pantsHeight z =
    (z.re * pantsCoeffRe z) • Complex.reCLM + (z.im * pantsCoeffIm z) • Complex.imCLM :=
  (hasFDerivAt_pantsHeight z).fderiv

theorem pantsGradIm_pos {z : ℂ} (hz : z ∈ planarModel 3) : 0 < pantsGradIm z := by
  rw [mem_planarModel_three] at hz
  have hL := (pantsLower_nonneg_iff z).mpr hz.2
  have hU := (pantsUpper_nonneg_iff z).mpr hz.1
  have hD := four_le_pantsLower_add_pantsUpper z
  unfold pantsGradIm
  nlinarith [mul_nonneg hU (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))]

theorem pantsGradRe_ne_zero {z : ℂ} (hz : z ∈ planarModel 3) (him : z.im = 0) :
    pantsGradRe z ≠ 0 := by
  rw [mem_planarModel_three] at hz
  have hL := (pantsLower_nonneg_iff z).mpr hz.2
  have hU := (pantsUpper_nonneg_iff z).mpr hz.1
  unfold pantsGradRe
  unfold pantsLower at hL ⊢
  unfold pantsUpper at hU ⊢
  rw [him] at hL hU ⊢
  intro h
  have h1 : 0 ≤ 13 * z.re ^ 2 - 37 := by nlinarith
  nlinarith [mul_nonneg h1 hU]

theorem zero_mem_planarModel_three : (0 : ℂ) ∈ planarModel 3 := by
  rw [← pantsHeight_mem_Icc_iff]
  norm_num [pantsHeight, pantsLower, pantsUpper]

theorem pantsHeight_zero : pantsHeight 0 = 4 / 13 := by
  norm_num [pantsHeight, pantsLower, pantsUpper]

theorem fderiv_pantsHeight_eq_zero_iff {z : ℂ} (hz : z ∈ planarModel 3) :
    fderiv ℝ pantsHeight z = 0 ↔ z = 0 := by
  rw [fderiv_pantsHeight]
  constructor
  · intro h
    have hD := pantsLower_add_pantsUpper_pos z
    have h1 : z.re * pantsCoeffRe z = 0 := by
      simpa using congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) h
    have hI : z.im * pantsCoeffIm z = 0 := by
      simpa using congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) h
    have hcIm : pantsCoeffIm z ≠ 0 :=
      div_ne_zero (pantsGradIm_pos hz).ne' (pow_ne_zero 2 hD.ne')
    have him : z.im = 0 := (mul_eq_zero.mp hI).resolve_right hcIm
    have hcRe : pantsCoeffRe z ≠ 0 :=
      div_ne_zero (pantsGradRe_ne_zero hz him) (pow_ne_zero 2 hD.ne')
    exact Complex.ext ((mul_eq_zero.mp h1).resolve_right hcRe) him
  · rintro rfl
    simp

theorem isCriticalPointAt_pantsHeight_iff {z : ℂ} (hz : pantsHeight z ∈ Icc 0 1) :
    IsCriticalPointAt 𝓘(ℝ, ℂ) pantsHeight z ↔ z = 0 := by
  rw [IsCriticalPointAt, mfderiv_eq_fderiv]
  exact fderiv_pantsHeight_eq_zero_iff ((pantsHeight_mem_Icc_iff z).mp hz)

theorem hasFDerivAt_fderiv_pantsHeight_zero : HasFDerivAt (fderiv ℝ pantsHeight)
    ((pantsCoeffRe 0 • Complex.reCLM).smulRight Complex.reCLM +
      (pantsCoeffIm 0 • Complex.imCLM).smulRight Complex.imCLM) 0 := by
  have hfun : fderiv ℝ pantsHeight = fun z =>
      (z.re * pantsCoeffRe z) • Complex.reCLM + (z.im * pantsCoeffIm z) • Complex.imCLM :=
    funext fderiv_pantsHeight
  rw [hfun]
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM 0 := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM 0 := Complex.imCLM.hasFDerivAt
  have hcr := ((contDiff_pantsCoeffRe.differentiable (by simp)) 0).hasFDerivAt
  have hci := ((contDiff_pantsCoeffIm.differentiable (by simp)) 0).hasFDerivAt
  have h := ((hre.mul hcr).smul_const Complex.reCLM).add ((him.mul hci).smul_const Complex.imCLM)
  refine h.congr_fderiv ?_
  simp

theorem pantsCoeffRe_zero : pantsCoeffRe 0 = -(82 / 169) := by
  norm_num [pantsCoeffRe, pantsGradRe, pantsLower, pantsUpper]

theorem pantsCoeffIm_zero : pantsCoeffIm 0 = 80 / 169 := by
  norm_num [pantsCoeffIm, pantsGradIm, pantsLower, pantsUpper]

theorem fderiv_fderiv_pantsHeight_zero_apply (v w : ℂ) :
    fderiv ℝ (fderiv ℝ pantsHeight) 0 v w =
      -(82 / 169) * v.re * w.re + 80 / 169 * v.im * w.im := by
  rw [hasFDerivAt_fderiv_pantsHeight_zero.fderiv]
  simp [pantsCoeffRe_zero, pantsCoeffIm_zero]

theorem isNondegenerateCriticalPointAt_pantsHeight_zero :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, ℂ) pantsHeight 0 := by
  rw [isNondegenerateCriticalPointAt_model_iff
    (contDiff_pantsHeight.contDiffAt.of_le (by simp))]
  refine ⟨(fderiv_pantsHeight_eq_zero_iff zero_mem_planarModel_three).mpr rfl, ?_⟩
  intro u v huv
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) huv
  have hI := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) huv
  simp only [fderiv_fderiv_pantsHeight_zero_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im] at h1 hI
  apply Complex.ext <;> linarith

theorem sigNeg_chartHessianAt_pantsHeight_zero :
    sigNeg (chartHessianAt (fun y => pantsHeight ((extChartAt 𝓘(ℝ, ℂ) (0 : ℂ)).symm y))
      (extChartAt 𝓘(ℝ, ℂ) (0 : ℂ) 0)) = 1 := by
  classical
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  let w : Fin 2 → ℝ := ![-(82 / 169), 80 / 169]
  have he : QuadraticMap.Equivalent (chartHessianAt pantsHeight 0)
      (QuadraticMap.weightedSumSquares ℝ w) := by
    refine ⟨{ Complex.equivRealProdLm.trans (LinearEquiv.finTwoArrow ℝ ℝ).symm with
      map_app' := ?_ }⟩
    intro v
    change _ = fderiv ℝ (fderiv ℝ pantsHeight) 0 v v
    rw [fderiv_fderiv_pantsHeight_zero_apply]
    simp only [LinearEquiv.finTwoArrow, Equiv.toFun_as_coe, finTwoArrowEquiv_apply,
      piFinTwoEquiv_apply, Fin.isValue, Equiv.invFun_as_coe, finTwoArrowEquiv_symm_apply,
      LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Complex.equivRealProdLm_apply, LinearEquiv.coe_mk, QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, w]
    ring
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares he]
  have hw : {i | w i < 0} = ({0} : Set (Fin 2)) := by
    ext i
    fin_cases i <;> norm_num [w]
  rw [hw, Set.ncard_singleton]

def saddleModelEquiv : ℂ ≃L[ℝ] MorseModel 2 :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

abbrev saddleModel : ModelWithCorners ℝ (MorseModel 2) ℂ :=
  𝓘(ℝ, ℂ).transContinuousLinearEquiv saddleModelEquiv

theorem isCriticalPointAt_saddleModel_pantsHeight_iff {z : ℂ} (hz : pantsHeight z ∈ Icc 0 1) :
    IsCriticalPointAt saddleModel pantsHeight z ↔ z = 0 := by
  rw [isCriticalPointAt_transContinuousLinearEquiv_iff]
  exact isCriticalPointAt_pantsHeight_iff hz

theorem isNondegenerateCriticalPointAt_saddleModel_pantsHeight_zero :
    IsNondegenerateCriticalPointAt saddleModel pantsHeight 0 :=
  (Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff 𝓘(ℝ, ℂ) saddleModelEquiv
    contDiff_pantsHeight.contMDiff BoundarylessManifold.isInteriorPoint).mpr
    isNondegenerateCriticalPointAt_pantsHeight_zero

theorem sigNeg_chartHessianAt_saddleModel_pantsHeight_zero :
    sigNeg (chartHessianAt (fun y => pantsHeight ((extChartAt saddleModel (0 : ℂ)).symm y))
      (extChartAt saddleModel (0 : ℂ) 0)) = 1 := by
  rw [Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv 𝓘(ℝ, ℂ) saddleModelEquiv
    contDiff_pantsHeight.contMDiff BoundarylessManifold.isInteriorPoint
    isNondegenerateCriticalPointAt_pantsHeight_zero.1]
  exact sigNeg_chartHessianAt_pantsHeight_zero

theorem starConvex_saddleCross :
    StarConvex ℝ 0 {z : ℂ | |z.re ^ 2 - z.im ^ 2| ≤ 1 ∧ ‖z‖ ≤ 2} := by
  intro z hz a b ha hb hab
  simp only [smul_zero, zero_add, mem_ofPred_eq]
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · have he : (b • z).re ^ 2 - (b • z).im ^ 2 = b ^ 2 * (z.re ^ 2 - z.im ^ 2) := by
      simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg b)]
    nlinarith [hz.1, abs_nonneg (z.re ^ 2 - z.im ^ 2)]
  · rw [norm_smul, Real.norm_of_nonneg hb]
    nlinarith [hz.2, norm_nonneg z]

end GC.Seifert
