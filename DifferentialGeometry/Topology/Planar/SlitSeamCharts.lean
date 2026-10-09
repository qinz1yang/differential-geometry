import DifferentialGeometry.Topology.Planar.SlitRegluing
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
The three explicit affine charts for a slit and its two branches. Their global
smooth inverses, actual derivative determinants, and strict radial margins are
paired with the accepted closed-cell slit-map identities. The common seam is
handled after composition with the supplied paired-value map.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Planar.SlitSeamCharts

/-- The affine chart transverse to the model slit. -/
def T (lam η : ℝ) (w : ℂ) : ℂ :=
  Complex.I * (lam / 4 : ℝ) - Complex.I * (η : ℂ) * w

/-- The affine chart on the positive branch. -/
def Bplus (lam η : ℝ) (w : ℂ) : ℂ :=
  Complex.mk (lam / 4 + η * w.re + (3 * η / 2) * w.im) (η * w.im)

/-- The affine chart on the negative branch. -/
def Bminus (lam η : ℝ) (w : ℂ) : ℂ :=
  Complex.mk (-lam / 4 - η * w.re - (3 * η / 2) * w.im) (η * w.im)

/-- The literal inverse of the transverse affine chart. -/
def TInv (lam η : ℝ) (z : ℂ) : ℂ :=
  (Complex.I * (lam / 4 : ℝ) - z) / (Complex.I * (η : ℂ))

/-- The literal inverse of the positive affine chart. -/
def BplusInv (lam η : ℝ) (z : ℂ) : ℂ :=
  Complex.mk ((z.re - lam / 4 - (3 / 2 : ℝ) * z.im) / η) (z.im / η)

/-- The literal inverse of the negative affine chart. -/
def BminusInv (lam η : ℝ) (z : ℂ) : ℂ :=
  Complex.mk ((-z.re - lam / 4 - (3 / 2 : ℝ) * z.im) / η) (z.im / η)

private theorem contDiff_complex_mk {f g : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z => Complex.mk (f z) (g z)) := by
  simpa only [Complex.mk_eq_add_mul_I, Function.comp_apply, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.comp hf).add
      ((Complex.ofRealCLM.contDiff.comp hg).mul contDiff_const)

private theorem contDiff_T (lam η : ℝ) : ContDiff ℝ ∞ (T lam η) := by
  unfold T
  exact contDiff_const.sub (contDiff_const.mul contDiff_id)

private theorem contDiff_TInv (lam η : ℝ) : ContDiff ℝ ∞ (TInv lam η) := by
  unfold TInv
  exact (contDiff_const.sub contDiff_id).div_const _

private theorem contDiff_Bplus (lam η : ℝ) : ContDiff ℝ ∞ (Bplus lam η) := by
  apply contDiff_complex_mk
  · exact (contDiff_const.add (contDiff_const.mul Complex.reCLM.contDiff)).add
      (contDiff_const.mul Complex.imCLM.contDiff)
  · exact contDiff_const.mul Complex.imCLM.contDiff

private theorem contDiff_Bminus (lam η : ℝ) : ContDiff ℝ ∞ (Bminus lam η) := by
  apply contDiff_complex_mk
  · exact (contDiff_const.sub (contDiff_const.mul Complex.reCLM.contDiff)).sub
      (contDiff_const.mul Complex.imCLM.contDiff)
  · exact contDiff_const.mul Complex.imCLM.contDiff

private theorem contDiff_BplusInv (lam η : ℝ) : ContDiff ℝ ∞ (BplusInv lam η) := by
  apply contDiff_complex_mk
  · exact ((Complex.reCLM.contDiff.sub contDiff_const).sub
      (contDiff_const.mul Complex.imCLM.contDiff)).div_const η
  · exact Complex.imCLM.contDiff.div_const η

private theorem contDiff_BminusInv (lam η : ℝ) : ContDiff ℝ ∞ (BminusInv lam η) := by
  apply contDiff_complex_mk
  · exact ((Complex.reCLM.contDiff.neg.sub contDiff_const).sub
      (contDiff_const.mul Complex.imCLM.contDiff)).div_const η
  · exact Complex.imCLM.contDiff.div_const η

private theorem T_inverse (lam η : ℝ) (hη : η ≠ 0) :
    (∀ w, TInv lam η (T lam η w) = w) ∧ (∀ w, T lam η (TInv lam η w) = w) := by
  have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  constructor <;> intro w <;> unfold T TInv <;> field_simp [hηc] <;> ring

private theorem Bplus_inverse (lam η : ℝ) (hη : η ≠ 0) :
    (∀ w, BplusInv lam η (Bplus lam η w) = w) ∧
      (∀ w, Bplus lam η (BplusInv lam η w) = w) := by
  constructor <;> intro w <;> apply Complex.ext <;>
    dsimp only [Bplus, BplusInv] <;>
    field_simp [hη] <;> ring

private theorem Bminus_inverse (lam η : ℝ) (hη : η ≠ 0) :
    (∀ w, BminusInv lam η (Bminus lam η w) = w) ∧
      (∀ w, Bminus lam η (BminusInv lam η w) = w) := by
  constructor <;> intro w <;> apply Complex.ext <;>
    dsimp only [Bminus, BminusInv] <;>
    field_simp [hη] <;> ring

/-- The global transverse affine chart with its literal inverse. -/
def TChart (lam η : ℝ) (hη : η ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun := T lam η
  invFun := TInv lam η
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' w _ := (T_inverse lam η hη).1 w
  right_inv' w _ := (T_inverse lam η hη).2 w
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_T lam η).contDiffOn.contMDiffOn
  contMDiffOn_invFun := (contDiff_TInv lam η).contDiffOn.contMDiffOn

/-- The global positive-branch affine chart with its literal inverse. -/
def BplusChart (lam η : ℝ) (hη : η ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun := Bplus lam η
  invFun := BplusInv lam η
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' w _ := (Bplus_inverse lam η hη).1 w
  right_inv' w _ := (Bplus_inverse lam η hη).2 w
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_Bplus lam η).contDiffOn.contMDiffOn
  contMDiffOn_invFun := (contDiff_BplusInv lam η).contDiffOn.contMDiffOn

/-- The global negative-branch affine chart with its literal inverse. -/
def BminusChart (lam η : ℝ) (hη : η ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun := Bminus lam η
  invFun := BminusInv lam η
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' w _ := (Bminus_inverse lam η hη).1 w
  right_inv' w _ := (Bminus_inverse lam η hη).2 w
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_Bminus lam η).contDiffOn.contMDiffOn
  contMDiffOn_invFun := (contDiff_BminusInv lam η).contDiffOn.contMDiffOn

theorem charts_source_target (lam η : ℝ) (hη : η ≠ 0) :
    (TChart lam η hη).source = Set.univ ∧ (TChart lam η hη).target = Set.univ ∧
    (BplusChart lam η hη).source = Set.univ ∧ (BplusChart lam η hη).target = Set.univ ∧
    (BminusChart lam η hη).source = Set.univ ∧ (BminusChart lam η hη).target = Set.univ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem charts_apply (lam η : ℝ) (hη : η ≠ 0) (w : ℂ) :
    TChart lam η hη w = T lam η w ∧ (TChart lam η hη).symm w = TInv lam η w ∧
    BplusChart lam η hη w = Bplus lam η w ∧ (BplusChart lam η hη).symm w = BplusInv lam η w ∧
    BminusChart lam η hη w = Bminus lam η w ∧
      (BminusChart lam η hη).symm w = BminusInv lam η w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem centers (lam η : ℝ) :
    T lam η 0 = Complex.I * (lam / 4 : ℝ) ∧
    Bplus lam η 0 = (lam / 4 : ℝ) ∧ Bminus lam η 0 = (-lam / 4 : ℝ) := by
  simp [T, Bplus, Bminus, Complex.ext_iff]

theorem hasDerivAt_T (lam η : ℝ) (w : ℂ) :
    HasDerivAt (T lam η) (-(Complex.I * (η : ℂ))) w := by
  unfold T
  apply HasDerivAt.const_sub
  simpa only [mul_one] using! (hasDerivAt_id w).const_mul (Complex.I * (η : ℂ))

theorem deriv_T_ne_zero (lam η : ℝ) (hη : η ≠ 0) (w : ℂ) :
    deriv (T lam η) w ≠ 0 := by
  rw [(hasDerivAt_T lam η w).deriv]
  exact neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hη))

private def triangularLinear (a b c : ℝ) : ℂ →L[ℝ] ℂ :=
  (a • Complex.reCLM + b • Complex.imCLM).smulRight (1 : ℂ) +
    (c • Complex.imCLM).smulRight Complex.I

private theorem triangularLinear_apply (a b c : ℝ) (z : ℂ) :
    triangularLinear a b c z = Complex.mk (a * z.re + b * z.im) (c * z.im) := by
  apply Complex.ext <;> simp [triangularLinear]

private theorem Bplus_eq_affine (lam η : ℝ) :
    Bplus lam η = fun z => (lam / 4 : ℝ) + triangularLinear η (3 * η / 2) η z := by
  funext z
  apply Complex.ext <;> simp [Bplus, triangularLinear_apply]
  ring

private theorem Bminus_eq_affine (lam η : ℝ) :
    Bminus lam η = fun z => (-lam / 4 : ℝ) + triangularLinear (-η) (-(3 * η / 2)) η z := by
  funext z
  apply Complex.ext <;> simp [Bminus, triangularLinear_apply]
  ring

private theorem triangularLinear_det (a b c : ℝ) :
    (triangularLinear a b c).toLinearMap.det = a * c := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, triangularLinear_apply]

theorem det_fderiv_Bplus (lam η : ℝ) (w : ℂ) :
    (fderiv ℝ (Bplus lam η) w).toLinearMap.det = η ^ 2 := by
  rw [Bplus_eq_affine]
  have hd : HasFDerivAt
      (fun z : ℂ => (lam / 4 : ℝ) + triangularLinear η (3 * η / 2) η z)
      (triangularLinear η (3 * η / 2) η) w :=
    (triangularLinear η (3 * η / 2) η).hasFDerivAt.const_add ((lam / 4 : ℝ) : ℂ)
  rw [hd.fderiv, triangularLinear_det]
  ring

theorem det_fderiv_Bminus (lam η : ℝ) (w : ℂ) :
    (fderiv ℝ (Bminus lam η) w).toLinearMap.det = -(η ^ 2) := by
  rw [Bminus_eq_affine]
  have hd : HasFDerivAt
      (fun z : ℂ => (-lam / 4 : ℝ) + triangularLinear (-η) (-(3 * η / 2)) η z)
      (triangularLinear (-η) (-(3 * η / 2)) η) w :=
    (triangularLinear (-η) (-(3 * η / 2)) η).hasFDerivAt.const_add ((-lam / 4 : ℝ) : ℂ)
  rw [hd.fderiv, triangularLinear_det]
  ring

private theorem slit_scaled_coordinates_le
    {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
    |η * w.re| ≤ η ∧ |η * w.im| ≤ η := by
  have hn : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  constructor
  · rw [abs_mul, abs_of_pos hη]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm w).trans hn) hη.le).trans_eq
      (mul_one η)
  · rw [abs_mul, abs_of_pos hη]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm w).trans hn) hη.le).trans_eq
      (mul_one η)

/-- The transverse chart stays uniformly away from zero and within half the model radius. -/
theorem T_norm_bounds {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η) (hηlam : η < lam / 16)
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
    lam / 16 < ‖T lam η w‖ ∧ ‖T lam η w‖ < lam / 2 := by
  obtain ⟨hr, hi⟩ := slit_scaled_coordinates_le hη hw
  have hre : (T lam η w).re = η * w.im := by
    simp [T, Complex.mul_re, Complex.mul_im]
  have him : (T lam η w).im = lam / 4 - η * w.re := by
    simp [T, Complex.mul_re, Complex.mul_im]
  have hquarter : |lam / 4| = lam / 4 := abs_of_pos (by positivity)
  constructor
  · have hn := Complex.im_le_norm (T lam η w)
    rw [him] at hn
    have hupper := (abs_le.mp hr).2
    linarith
  · have ha : |lam / 4 - η * w.re| ≤ lam / 4 + η := by
      calc
        _ ≤ |lam / 4| + |η * w.re| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (lam / 4) (-(η * w.re))
        _ ≤ lam / 4 + η := by rw [hquarter]; exact add_le_add le_rfl hr
    calc
      ‖T lam η w‖ ≤ |η * w.im| + |lam / 4 - η * w.re| := by
        simpa only [hre, him] using Complex.norm_le_abs_re_add_abs_im (T lam η w)
      _ ≤ η + (lam / 4 + η) := add_le_add hi ha
      _ < lam / 2 := by linarith

/-- The positive affine branch lies in a fixed punctured subball. -/
theorem Bplus_norm_bounds {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η) (hηlam : η < lam / 16)
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
    lam / 16 < ‖Bplus lam η w‖ ∧ ‖Bplus lam η w‖ < lam / 2 := by
  obtain ⟨hr, hi⟩ := slit_scaled_coordinates_le hη hw
  have hthree : |(3 * η / 2) * w.im| ≤ 3 * η / 2 := by
    rw [show (3 * η / 2) * w.im = (3 / 2 : ℝ) * (η * w.im) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  have hdelta : |η * w.re + (3 * η / 2) * w.im| ≤ 5 * η / 2 := by
    calc
      _ ≤ |η * w.re| + |(3 * η / 2) * w.im| := abs_add_le _ _
      _ ≤ η + 3 * η / 2 := add_le_add hr hthree
      _ = _ := by ring
  constructor
  · have hn := Complex.re_le_norm (Bplus lam η w)
    change lam / 4 + η * w.re + (3 * η / 2) * w.im ≤ ‖Bplus lam η w‖ at hn
    have hlower := (abs_le.mp hdelta).1
    linarith
  · have ha : |lam / 4 + η * w.re + (3 * η / 2) * w.im| ≤ lam / 4 + 5 * η / 2 := by
      calc
        _ = |lam / 4 + (η * w.re + (3 * η / 2) * w.im)| := by rw [add_assoc]
        _ ≤ |lam / 4| + |η * w.re + (3 * η / 2) * w.im| := abs_add_le _ _
        _ ≤ lam / 4 + 5 * η / 2 := by
          rw [abs_of_pos (by positivity : (0 : ℝ) < lam / 4)]
          exact add_le_add le_rfl hdelta
    calc
      ‖Bplus lam η w‖ ≤ |lam / 4 + η * w.re + (3 * η / 2) * w.im| + |η * w.im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (lam / 4 + 5 * η / 2) + η := add_le_add ha hi
      _ < lam / 2 := by linarith

/-- The negative affine branch has the same quantitative image bounds. -/
theorem Bminus_norm_bounds {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η) (hηlam : η < lam / 16)
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
    lam / 16 < ‖Bminus lam η w‖ ∧ ‖Bminus lam η w‖ < lam / 2 := by
  have heq : Bminus lam η w = -starRingEnd ℂ (Bplus lam η w) := by
    apply Complex.ext
    · simp only [Bminus, Bplus, Complex.neg_re, Complex.conj_re]
      ring
    · simp only [Bminus, Bplus, Complex.neg_im, Complex.conj_im, neg_neg]
  rw [heq, norm_neg, Complex.norm_conj]
  exact Bplus_norm_bounds hlam hη hηlam hw

private theorem normalized_T_cell_inequalities {lam η : ℝ} (hlam : 0 < lam)
    (hη : 0 < η) (hsmall : η < lam / 16) {w : ℂ}
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1) (him : 0 ≤ w.im) :
    0 ≤ η * w.im / lam ∧
      η * w.im / lam ≤ (lam / 4 - η * w.re) / lam ∧
      2 * ((lam / 4 - η * w.re) / lam) ≤ 1 + η * w.im / lam := by
  have hn : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hre := abs_le.mp ((Complex.abs_re_le_norm w).trans hn)
  have himle := (le_abs_self w.im).trans ((Complex.abs_im_le_norm w).trans hn)
  have hreal_lower := mul_le_mul_of_nonneg_left hre.1 hη.le
  have hreal_upper := mul_le_mul_of_nonneg_left hre.2 hη.le
  have himag_upper := mul_le_mul_of_nonneg_left himle hη.le
  have himag_lower : 0 ≤ η * w.im := mul_nonneg hη.le him
  have hxy : η * w.im ≤ lam / 4 - η * w.re := by linarith
  have hlast : 2 * (lam / 4 - η * w.re) ≤ lam + η * w.im := by linarith
  refine ⟨div_nonneg himag_lower hlam.le,
    (div_le_div_iff_of_pos_right hlam).mpr hxy, ?_⟩
  calc
    2 * ((lam / 4 - η * w.re) / lam) = (2 * (lam / 4 - η * w.re)) / lam := by ring
    _ ≤ (lam + η * w.im) / lam := (div_le_div_iff_of_pos_right hlam).mpr hlast
    _ = 1 + η * w.im / lam := by rw [add_div, div_self hlam.ne']

/-- The transverse affine chart lies in the actual positive closed slit cell. -/
theorem T_mem_sourceClosedCell {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hsmall : η < lam / 16) {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1)
    (him : 0 ≤ w.im) :
    T lam η w / (lam : ℂ) ∈ SlitRegluing.sourceClosedCell (false, false) 1 := by
  simpa [SlitRegluing.sourceClosedCell, SlitRegluing.reflect,
    SlitRegluing.baseClosedCell, T, Complex.mul_re, Complex.mul_im]
    using normalized_T_cell_inequalities hlam hη hsmall hw him

/-- Reflection of the parameter lies in the actual negative closed slit cell. -/
theorem T_conj_mem_sourceClosedCell {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hsmall : η < lam / 16) {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1)
    (him : 0 ≤ w.im) :
    T lam η (star w) / (lam : ℂ) ∈ SlitRegluing.sourceClosedCell (true, false) 1 := by
  rcases normalized_T_cell_inequalities hlam hη hsmall hw him with ⟨hzero, hfirst, hlast⟩
  suffices hreflected :
      -(η * w.im / lam) ≤ 0 ∧
        η * w.im / lam ≤ (lam / 4 - η * w.re) / lam ∧
        2 * ((lam / 4 - η * w.re) / lam) + -(η * w.im / lam) ≤ 1 by
    simpa [SlitRegluing.sourceClosedCell, SlitRegluing.reflect,
      SlitRegluing.baseClosedCell, T, Complex.mul_re, Complex.mul_im, neg_div]
      using hreflected
  exact ⟨by linarith, hfirst, by linarith⟩

/-- The literal positive affine branch after the transverse affine chart. -/
theorem scaledBranch_T {lam η : ℝ} (hlam : lam ≠ 0) (w : ℂ) :
    SlitRegluing.scaledBranch lam (false, false) 1 (T lam η w) = Bplus lam η w := by
  apply Complex.ext <;>
    simp [SlitRegluing.scaledBranch, SlitRegluing.branch, SlitRegluing.reflect,
      SlitRegluing.baseBranch, T, Bplus, Complex.mul_re, Complex.mul_im]
  all_goals field_simp [hlam]
  all_goals ring

/-- The literal negative affine branch after reflection of the parameter. -/
theorem scaledBranch_T_conj {lam η : ℝ} (hlam : lam ≠ 0) (w : ℂ) :
    SlitRegluing.scaledBranch lam (true, false) 1 (T lam η (star w)) = Bminus lam η w := by
  apply Complex.ext <;>
    simp [SlitRegluing.scaledBranch, SlitRegluing.branch, SlitRegluing.reflect,
      SlitRegluing.baseBranch, T, Bminus, Complex.mul_re, Complex.mul_im]
  all_goals field_simp [hlam]
  all_goals ring

/-- The positive seam identity after composing with the supplied paired-value map. -/
theorem comp_scaledSlitMap_T {Y : Type*} {f : ℂ → Y} {lam η : ℝ}
    (hlam : 0 < lam) (hη : 0 < η) (hsmall : η < lam / 16)
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) (lam / 2), f (t : ℂ) = f (-t : ℂ))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) (him : 0 ≤ w.im) :
    f (SlitRegluing.scaledSlitMap lam (T lam η w)) = f (Bplus lam η w) := by
  rw [SlitRegluing.comp_scaledSlitMap_eq_scaledBranch hlam hpair (false, false) 1
    (T_mem_sourceClosedCell hlam hη hsmall hw him), scaledBranch_T hlam.ne']

/-- The negative seam identity, including the common slit, after composition. -/
theorem comp_scaledSlitMap_T_conj {Y : Type*} {f : ℂ → Y} {lam η : ℝ}
    (hlam : 0 < lam) (hη : 0 < η) (hsmall : η < lam / 16)
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) (lam / 2), f (t : ℂ) = f (-t : ℂ))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) (him : 0 ≤ w.im) :
    f (SlitRegluing.scaledSlitMap lam (T lam η (star w))) = f (Bminus lam η w) := by
  rw [SlitRegluing.comp_scaledSlitMap_eq_scaledBranch hlam hpair (true, false) 1
    (T_conj_mem_sourceClosedCell hlam hη hsmall hw him), scaledBranch_T_conj hlam.ne']

end DifferentialGeometry.Topology.Planar.SlitSeamCharts
