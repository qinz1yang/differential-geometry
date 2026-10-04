import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabUniquenessProof
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
# The pants piece of the one-sided slab

Lane MD3, T5. In the blow-down picture of the one-sided model slab (`OneSidedSlab.lean`) the pants
piece is the round annulus `1 ≤ |z| ≤ √3` minus the open disc `|z - 7i/5| < 1/5`, `ospSlab`. It is
the slab `[0, 1]` of `ospHeight = U F / G` on `ospDom = {Im z < 123/70}`, with
`U = |z|² - 1`, `F = |z - 7i/5|² - 1/25`, `G = 246/25 - 28/5 Im z = 2 (F + 2 - U)`
(`ospHeight_mem_Icc_iff`). Its `x`-derivative is `x · 2 (F + U) / G` (`hasFDerivAt_ospHeight`),
so critical points in the slab lie on the imaginary axis, where the derivative is
`N (Im z) / G²` for the quartic `ospN`; `ospN` has no zero on `[-2, -1] ∪ [8/5, 7/4]` and is
strictly decreasing on `[1, 6/5]` (derivative `P'' G < 0`), with one zero `ospT`. So `ospSaddle =
i ospT` is the only critical point (`fderiv_ospHeight_eq_zero_iff`); its Hessian is
`diag (2 (F + U) / G, P'' / G)` (`fderiv_fderiv_ospHeight_saddle_apply`), nondegenerate of index
one. The slab is compact and connected (radial segments to the two circles of the annulus,
`isConnected_ospSlab`) and its lower level is the two circles, so lane MD2's uniqueness gives a
diffeomorphism from the pants model onto the slab, outer circle to level `1` (`exists_ospPants`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def ospU (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2 - 1

def ospF (z : ℂ) : ℝ := z.re ^ 2 + (z.im - 7 / 5) ^ 2 - 1 / 25

def ospG (z : ℂ) : ℝ := 246 / 25 - 28 / 5 * z.im

def ospHeight (z : ℂ) : ℝ := ospU z * ospF z / ospG z

theorem ospG_eq (z : ℂ) : ospG z = 2 * (ospF z + 2 - ospU z) := by
  unfold ospG ospF ospU
  ring

theorem ospG_pos {z : ℂ} (hz : z.im < 123 / 70) : 0 < ospG z := by
  unfold ospG
  linarith

theorem ospU_pos_of_ospF_nonpos {z : ℂ} (h : ospF z ≤ 0) : 0 < ospU z := by
  unfold ospF at h
  unfold ospU
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 7 / 5)]

theorem ospF_pos_of_ospU_nonpos {z : ℂ} (h : ospU z ≤ 0) : 0 < ospF z := by
  unfold ospU at h
  unfold ospF
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem ospF_ge (z : ℂ) : -(1 / 25) ≤ ospF z := by
  unfold ospF
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 7 / 5)]

theorem ospHeight_mem_Icc_iff {z : ℂ} (hz : z.im < 123 / 70) :
    ospHeight z ∈ Icc 0 1 ↔ 0 ≤ ospU z ∧ ospU z ≤ 2 ∧ 0 ≤ ospF z := by
  have hG := ospG_pos hz
  have hF := ospF_ge z
  unfold ospHeight
  rw [mem_Icc, div_nonneg_iff, div_le_one hG]
  have hle : ospU z * ospF z ≤ ospG z ↔ ospU z ≤ 2 := by
    rw [ospG_eq]
    constructor
    · intro h
      by_contra hc
      have hc' := lt_of_not_ge hc
      nlinarith
    · intro h
      nlinarith
  rw [hle]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · have hUF := h1.1
      by_cases hU : 0 ≤ ospU z
      · refine ⟨hU, h2, ?_⟩
        by_contra hFn
        have hFn' := lt_of_not_ge hFn
        have := ospU_pos_of_ospF_nonpos hFn'.le
        nlinarith
      · have hU' := lt_of_not_ge hU
        have := ospF_pos_of_ospU_nonpos hU'.le
        nlinarith
    · linarith [h1.2]
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Or.inl ⟨mul_nonneg h1 h3, hG.le⟩, h2⟩

theorem ospHeight_eq_zero_iff {z : ℂ} (hz : z.im < 123 / 70) :
    ospHeight z = 0 ↔ ospU z = 0 ∨ ospF z = 0 := by
  unfold ospHeight
  rw [div_eq_zero_iff, mul_eq_zero]
  have hG := ospG_pos hz
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hG.ne'
  · intro h
    exact Or.inl h

theorem ospHeight_eq_one_iff {z : ℂ} (hz : z.im < 123 / 70) :
    ospHeight z = 1 ↔ ospU z = 2 := by
  have hG := ospG_pos hz
  have hF := ospF_ge z
  unfold ospHeight
  rw [div_eq_one_iff_eq hG.ne', ospG_eq]
  constructor
  · intro h
    have h' : (2 - ospU z) * (ospF z + 2) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · linarith
    · linarith
  · intro h
    rw [h]
    ring

def ospSlab : Set ℂ := {z | 0 ≤ ospU z ∧ ospU z ≤ 2 ∧ 0 ≤ ospF z}

theorem im_lt_of_mem_ospSlab {z : ℂ} (hz : z ∈ ospSlab) : z.im < 123 / 70 := by
  obtain ⟨-, h2, -⟩ := hz
  unfold ospU at h2
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 123 / 70)]

theorem isCompact_ospSlab : IsCompact ospSlab := by
  have hU : Continuous ospU := by unfold ospU; fun_prop
  have hF : Continuous ospF := by unfold ospF; fun_prop
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const hU).inter ((isClosed_le hU continuous_const).inter
      (isClosed_le continuous_const hF))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_
    rw [mem_closedBall_zero_iff]
    have h2 := hz.2.1
    unfold ospU at h2
    have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg z]

def ospDom : TopologicalSpace.Opens ℂ :=
  ⟨{z | z.im < 123 / 70}, isOpen_lt Complex.continuous_im continuous_const⟩

theorem ospSlab_subset_ospDom : ospSlab ⊆ (ospDom : Set ℂ) := fun _ hz =>
  im_lt_of_mem_ospSlab hz

def ospFun (z : ospDom) : ℝ := ospHeight z.val

theorem ospFun_preimage_Icc : ospFun ⁻¹' Icc 0 1 = Subtype.val ⁻¹' ospSlab := by
  ext z
  exact ospHeight_mem_Icc_iff z.2

theorem isCompact_ospFun_preimage_Icc : IsCompact (ospFun ⁻¹' Icc 0 1) := by
  rw [ospFun_preimage_Icc]
  exact (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
    (by rw [Subtype.range_coe]; exact ospSlab_subset_ospDom)).mpr isCompact_ospSlab

theorem not_isPreconnected_ospFun_zero : ¬ IsPreconnected (ospFun ⁻¹' {0}) := by
  intro h
  have hF : Continuous fun z : ospDom => ospF z.val := by
    unfold ospF
    fun_prop
  have him := h.image _ hF.continuousOn
  have hdom1 : (-Complex.I : ℂ) ∈ (ospDom : Set ℂ) := by
    change (-Complex.I).im < 123 / 70
    norm_num
  have hdom2 : ((6 / 5 : ℝ) * Complex.I : ℂ) ∈ (ospDom : Set ℂ) := by
    change ((6 / 5 : ℝ) * Complex.I).im < 123 / 70
    norm_num
  have h1 : (0 : ℝ) ∈ (fun z : ospDom => ospF z.val) '' (ospFun ⁻¹' {0}) := by
    refine ⟨⟨_, hdom2⟩, ?_, ?_⟩
    · change ospHeight _ = 0
      rw [ospHeight_eq_zero_iff hdom2]
      right
      norm_num [ospF]
    · norm_num [ospF]
  have h2 : (143 / 25 : ℝ) ∈ (fun z : ospDom => ospF z.val) '' (ospFun ⁻¹' {0}) := by
    refine ⟨⟨_, hdom1⟩, ?_, ?_⟩
    · change ospHeight _ = 0
      rw [ospHeight_eq_zero_iff hdom1]
      left
      norm_num [ospU]
    · norm_num [ospF]
  have hmid := him.Icc_subset h1 h2
    (show (1 / 20 : ℝ) ∈ Icc 0 (143 / 25) from ⟨by norm_num, by norm_num⟩)
  obtain ⟨z, hz0, hz⟩ := hmid
  have hz0' : ospHeight z.val = 0 := hz0
  rw [ospHeight_eq_zero_iff z.2] at hz0'
  simp only at hz
  rcases hz0' with hU | hFz
  · have := ospF_pos_of_ospU_nonpos hU.le
    unfold ospU at hU
    unfold ospF at hz
    nlinarith [sq_nonneg z.val.re, sq_nonneg z.val.im]
  · rw [hFz] at hz
    norm_num at hz

section Derivative

def ospCx (z : ℂ) : ℝ := 2 * (ospF z + ospU z) / ospG z

def ospNy (z : ℂ) : ℝ :=
  (2 * z.im * ospF z + 2 * (z.im - 7 / 5) * ospU z) * ospG z + 28 / 5 * ospU z * ospF z

def ospDy (z : ℂ) : ℝ := ospNy z / ospG z ^ 2

theorem hasFDerivAt_ospHeight {z : ℂ} (hz : ospG z ≠ 0) :
    HasFDerivAt ospHeight ((z.re * ospCx z) • Complex.reCLM + ospDy z • Complex.imCLM) z := by
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hU := ((hre.pow 2).add (him.pow 2)).sub_const 1
  have hF := ((hre.pow 2).add ((him.sub_const (7 / 5)).pow 2)).sub_const (1 / 25)
  have hG := (him.const_mul (28 / 5)).const_sub (246 / 25)
  have hinv := (hasDerivAt_inv hz).comp_hasFDerivAt z hG
  have hH := (hU.mul hF).mul hinv
  convert hH using 1
  · funext w
    simp only [ospHeight, ospU, ospF, ospG, div_eq_mul_inv, comp_apply, Pi.mul_apply,
      Pi.add_apply]
  · unfold ospCx ospDy ospNy
    unfold ospG at hz ⊢
    unfold ospU ospF
    ext v
    simp
    field_simp
    ring

theorem ospCx_pos {z : ℂ} (hz : z ∈ ospSlab) : 0 < ospCx z := by
  have hG := ospG_pos (im_lt_of_mem_ospSlab hz)
  obtain ⟨h1, -, h3⟩ := hz
  unfold ospCx
  refine div_pos ?_ hG
  rcases h1.lt_or_eq with h | h
  · linarith
  · have := ospF_pos_of_ospU_nonpos h.symm.le
    linarith

def ospN (t : ℝ) : ℝ :=
  -(84 / 5) * t ^ 4 + 1768 / 25 * t ^ 3 - 10976 / 125 * t ^ 2 + 11316 / 625 * t + 84 / 5

def ospN' (t : ℝ) : ℝ := (12 * t ^ 2 - 84 / 5 * t + 46 / 25) * (246 / 25 - 28 / 5 * t)

theorem ospNy_of_re_eq_zero {z : ℂ} (h : z.re = 0) : ospNy z = ospN z.im := by
  unfold ospNy ospN ospF ospU ospG
  rw [h]
  ring

theorem hasDerivAt_ospN (t : ℝ) : HasDerivAt ospN (ospN' t) t := by
  have h := ((((hasDerivAt_pow 4 t).const_mul (-(84 / 5))).add
    ((hasDerivAt_pow 3 t).const_mul (1768 / 25))).sub
    ((hasDerivAt_pow 2 t).const_mul (10976 / 125))).add
    (((hasDerivAt_id t).const_mul (11316 / 625)).add_const (84 / 5))
  convert h using 1
  · funext x
    simp only [ospN, Pi.add_apply, Pi.sub_apply, id]
    ring
  · simp only [ospN']
    norm_num
    ring

theorem ospN_neg {t : ℝ} (h2 : t ≤ -1) : ospN t < 0 := by
  unfold ospN
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ -t)]

theorem ospN_pos {t : ℝ} (h1 : 8 / 5 ≤ t) (h2 : t ≤ 7 / 4) : 0 < ospN t := by
  have hU : 0 < t ^ 2 - 1 := by nlinarith
  have hF : 0 ≤ (t - 7 / 5) ^ 2 - 1 / 25 := by nlinarith
  have hP : 0 < 2 * t * ((t - 7 / 5) ^ 2 - 1 / 25) + 2 * (t - 7 / 5) * (t ^ 2 - 1) := by
    have : 0 < 2 * (t - 7 / 5) * (t ^ 2 - 1) := by
      apply mul_pos _ hU
      linarith
    nlinarith
  have hG : 0 < 246 / 25 - 28 / 5 * t := by linarith
  have he : ospN t = (2 * t * ((t - 7 / 5) ^ 2 - 1 / 25) + 2 * (t - 7 / 5) * (t ^ 2 - 1)) *
      (246 / 25 - 28 / 5 * t) + 28 / 5 * (t ^ 2 - 1) * ((t - 7 / 5) ^ 2 - 1 / 25) := by
    unfold ospN
    ring
  rw [he]
  have := mul_nonneg hU.le hF
  positivity

theorem ospN'_neg {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 6 / 5) : ospN' t < 0 := by
  unfold ospN'
  have hP : 12 * t ^ 2 - 84 / 5 * t + 46 / 25 < 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) (by linarith : (0 : ℝ) ≤ 6 / 5 - t)]
  have hG : 0 < 246 / 25 - 28 / 5 * t := by linarith
  exact mul_neg_of_neg_of_pos hP hG

theorem continuous_ospN : Continuous ospN := by
  unfold ospN
  fun_prop

theorem strictAntiOn_ospN : StrictAntiOn ospN (Icc 1 (6 / 5)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_ospN.continuousOn fun t ht => ?_
  rw [interior_Icc] at ht
  rw [(hasDerivAt_ospN t).deriv]
  exact ospN'_neg ht.1.le ht.2.le

theorem exists_ospN_root : ∃ t ∈ Ioo (1 : ℝ) (6 / 5), ospN t = 0 := by
  have h := intermediate_value_Ioo' (show (1 : ℝ) ≤ 6 / 5 by norm_num)
    continuous_ospN.continuousOn
  have h0 : (0 : ℝ) ∈ Ioo (ospN (6 / 5)) (ospN 1) := by
    constructor <;> norm_num [ospN]
  obtain ⟨t, ht, hzero⟩ := h h0
  exact ⟨t, ht, hzero⟩

def ospT : ℝ := Classical.choose exists_ospN_root

theorem ospT_mem : ospT ∈ Ioo (1 : ℝ) (6 / 5) := (Classical.choose_spec exists_ospN_root).1

theorem ospN_ospT : ospN ospT = 0 := (Classical.choose_spec exists_ospN_root).2

def ospSaddle : ℂ := ⟨0, ospT⟩

theorem ospSaddle_mem_ospSlab : ospSaddle ∈ ospSlab := by
  have h := ospT_mem
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ospU, ospF, ospSaddle] <;> nlinarith [h.1, h.2]

theorem ospG_ospSaddle_pos : 0 < ospG ospSaddle :=
  ospG_pos (im_lt_of_mem_ospSlab ospSaddle_mem_ospSlab)

theorem ospHeight_ospSaddle_mem : ospHeight ospSaddle ∈ Ioo 0 1 := by
  have h := ospT_mem
  have hdom : ospSaddle.im < 123 / 70 := im_lt_of_mem_ospSlab ospSaddle_mem_ospSlab
  have hI := (ospHeight_mem_Icc_iff hdom).mpr ospSaddle_mem_ospSlab
  refine ⟨lt_of_le_of_ne hI.1 fun h0 => ?_, lt_of_le_of_ne hI.2 fun h1 => ?_⟩
  · rcases (ospHeight_eq_zero_iff hdom).mp h0.symm with h' | h' <;>
      simp only [ospU, ospF, ospSaddle] at h' <;> nlinarith [h.1, h.2]
  · have hU := (ospHeight_eq_one_iff hdom).mp h1
    simp only [ospU, ospSaddle] at hU
    nlinarith [h.1, h.2]

theorem im_cases_of_mem_ospSlab {z : ℂ} (hz : z ∈ ospSlab) (hre : z.re = 0) :
    (-2 ≤ z.im ∧ z.im ≤ -1) ∨ (1 ≤ z.im ∧ z.im ≤ 6 / 5) ∨ (8 / 5 ≤ z.im ∧ z.im ≤ 7 / 4) := by
  obtain ⟨h1, h2, h3⟩ := hz
  simp only [ospU, ospF, hre] at h1 h2 h3
  by_cases hneg : z.im < 0
  · left
    constructor <;> nlinarith
  · have hy : 0 ≤ z.im := le_of_not_gt hneg
    by_cases hlow : z.im ≤ 6 / 5
    · right; left
      constructor <;> nlinarith
    · right; right
      have hy' : 6 / 5 < z.im := lt_of_not_ge hlow
      constructor <;> nlinarith

theorem fderiv_ospHeight_eq_zero_iff {z : ℂ} (hz : z ∈ ospSlab) :
    fderiv ℝ ospHeight z = 0 ↔ z = ospSaddle := by
  have hG := ospG_pos (im_lt_of_mem_ospSlab hz)
  rw [(hasFDerivAt_ospHeight hG.ne').fderiv]
  constructor
  · intro h
    have h1 : z.re * ospCx z = 0 := by
      simpa using congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) h
    have hI : ospDy z = 0 := by
      simpa using congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) h
    have hre : z.re = 0 := (mul_eq_zero.mp h1).resolve_right (ospCx_pos hz).ne'
    have hN : ospN z.im = 0 := by
      rw [← ospNy_of_re_eq_zero hre]
      unfold ospDy at hI
      rcases div_eq_zero_iff.mp hI with h' | h'
      · exact h'
      · exact absurd h' (pow_ne_zero 2 hG.ne')
    rcases im_cases_of_mem_ospSlab hz hre with hc | hc | hc
    · exact absurd hN (ospN_neg hc.2).ne
    · have hT := ospT_mem
      have heq : z.im = ospT := strictAntiOn_ospN.injOn ⟨hc.1, hc.2⟩ ⟨hT.1.le, hT.2.le⟩
        (hN.trans ospN_ospT.symm)
      exact Complex.ext hre heq
    · exact absurd hN (ospN_pos hc.1 hc.2).ne'
  · rintro rfl
    have hre : ospSaddle.re = 0 := rfl
    have hDy : ospDy ospSaddle = 0 := by
      unfold ospDy
      rw [ospNy_of_re_eq_zero hre]
      change ospN ospT / _ = 0
      rw [ospN_ospT, zero_div]
    rw [hre, hDy, zero_mul, zero_smul, zero_smul, add_zero]

end Derivative

section Hessian

def ospAx (z : ℂ) : ℝ := (2 * z.im + 2 * (z.im - 7 / 5)) * ospG z + 28 / 5 * (ospF z + ospU z)

def ospBz (z : ℂ) : ℝ := 2 * ospF z + 2 * ospU z + 8 * z.im * (z.im - 7 / 5)

theorem contDiff_ospU : ContDiff ℝ ∞ ospU := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  unfold ospU
  fun_prop

theorem contDiff_ospF : ContDiff ℝ ∞ ospF := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  unfold ospF
  fun_prop

theorem contDiff_ospG : ContDiff ℝ ∞ ospG := by
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  unfold ospG
  fun_prop

theorem contDiffAt_ospHeight {z : ℂ} (hz : ospG z ≠ 0) : ContDiffAt ℝ ∞ ospHeight z :=
  (contDiff_ospU.mul contDiff_ospF).contDiffAt.div contDiff_ospG.contDiffAt hz

theorem contDiffAt_ospCx {z : ℂ} (hz : ospG z ≠ 0) : ContDiffAt ℝ ∞ ospCx z :=
  ((contDiff_const.mul (contDiff_ospF.add contDiff_ospU)).contDiffAt).div
    contDiff_ospG.contDiffAt hz

theorem hasFDerivAt_ospNy (z : ℂ) :
    HasFDerivAt ospNy
      ((2 * z.re * ospAx z) • Complex.reCLM + (ospG z * ospBz z) • Complex.imCLM) z := by
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hU := ((hre.pow 2).add (him.pow 2)).sub_const 1
  have hF := ((hre.pow 2).add ((him.sub_const (7 / 5)).pow 2)).sub_const (1 / 25)
  have hG := (him.const_mul (28 / 5)).const_sub (246 / 25)
  have hNy := ((((him.const_mul 2).mul hF).add
    (((him.sub_const (7 / 5)).const_mul 2).mul hU)).mul hG).add ((hU.const_mul (28 / 5)).mul hF)
  convert hNy using 1
  · funext w
    simp only [ospNy, ospU, ospF, ospG, Pi.mul_apply, Pi.add_apply]
  · unfold ospAx ospBz ospU ospF ospG
    ext v
    simp
    ring

theorem ospSaddle_re : ospSaddle.re = 0 := rfl

theorem ospNy_ospSaddle : ospNy ospSaddle = 0 := by
  rw [ospNy_of_re_eq_zero ospSaddle_re]
  exact ospN_ospT

theorem ospBz_ospSaddle_neg : ospBz ospSaddle < 0 := by
  have h := ospT_mem
  simp only [ospBz, ospF, ospU, ospSaddle]
  nlinarith [mul_nonneg (by linarith [h.1] : (0 : ℝ) ≤ ospT - 1)
    (by linarith [h.2] : (0 : ℝ) ≤ 6 / 5 - ospT)]

theorem hasFDerivAt_ospDy_saddle :
    HasFDerivAt ospDy ((ospG ospSaddle ^ 2)⁻¹ •
      ((ospG ospSaddle * ospBz ospSaddle) • Complex.imCLM)) ospSaddle := by
  have hG0 := ospG_ospSaddle_pos
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM ospSaddle :=
    Complex.imCLM.hasFDerivAt
  have hG := ((him.const_mul (28 / 5)).const_sub (246 / 25)).pow 2
  have hGi := (hasDerivAt_inv (pow_ne_zero 2 hG0.ne')).comp_hasFDerivAt ospSaddle hG
  have h := (hasFDerivAt_ospNy ospSaddle).mul hGi
  convert h using 1
  · funext w
    simp only [ospDy, ospG, div_eq_mul_inv, Pi.mul_apply, comp_apply]
  · rw [ospNy_ospSaddle, ospSaddle_re]
    ext v
    simp [ospG]

theorem fderiv_ospHeight_eventuallyEq : fderiv ℝ ospHeight =ᶠ[𝓝 ospSaddle]
    fun z => (z.re * ospCx z) • Complex.reCLM + ospDy z • Complex.imCLM := by
  have hopen : IsOpen {z : ℂ | ospG z ≠ 0} :=
    isOpen_ne_fun contDiff_ospG.continuous continuous_const
  filter_upwards [hopen.mem_nhds ospG_ospSaddle_pos.ne'] with z hz
  exact (hasFDerivAt_ospHeight hz).fderiv

theorem hasFDerivAt_fderiv_ospHeight_saddle : HasFDerivAt (fderiv ℝ ospHeight)
    ((ospCx ospSaddle • Complex.reCLM).smulRight Complex.reCLM +
      ((ospG ospSaddle ^ 2)⁻¹ • ((ospG ospSaddle * ospBz ospSaddle) • Complex.imCLM)).smulRight
        Complex.imCLM) ospSaddle := by
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM ospSaddle :=
    Complex.reCLM.hasFDerivAt
  have hCx := ((contDiffAt_ospCx ospG_ospSaddle_pos.ne').differentiableAt
    (by simp)).hasFDerivAt
  have h := ((hre.mul hCx).smul_const Complex.reCLM).add
    (hasFDerivAt_ospDy_saddle.smul_const Complex.imCLM)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq fderiv_ospHeight_eventuallyEq
  rw [ospSaddle_re]
  simp

theorem fderiv_fderiv_ospHeight_saddle_apply (v w : ℂ) :
    fderiv ℝ (fderiv ℝ ospHeight) ospSaddle v w =
      ospCx ospSaddle * v.re * w.re +
        (ospG ospSaddle ^ 2)⁻¹ * (ospG ospSaddle * ospBz ospSaddle) * v.im * w.im := by
  rw [hasFDerivAt_fderiv_ospHeight_saddle.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  ring

theorem ospHessian_im_coeff_neg :
    (ospG ospSaddle ^ 2)⁻¹ * (ospG ospSaddle * ospBz ospSaddle) < 0 :=
  mul_neg_of_pos_of_neg (inv_pos.mpr (pow_pos ospG_ospSaddle_pos 2))
    (mul_neg_of_pos_of_neg ospG_ospSaddle_pos ospBz_ospSaddle_neg)

theorem isNondegenerateCriticalPointAt_ospHeight_saddle :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, ℂ) ospHeight ospSaddle := by
  rw [isNondegenerateCriticalPointAt_model_iff
    ((contDiffAt_ospHeight ospG_ospSaddle_pos.ne').of_le (by simp))]
  refine ⟨(fderiv_ospHeight_eq_zero_iff ospSaddle_mem_ospSlab).mpr rfl, ?_⟩
  intro u v huv
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) huv
  have hI := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) huv
  simp only [fderiv_fderiv_ospHeight_saddle_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at h1 hI
  have hc := ospCx_pos ospSaddle_mem_ospSlab
  have hd := ospHessian_im_coeff_neg
  apply Complex.ext
  · exact mul_left_cancel₀ hc.ne' h1
  · exact mul_left_cancel₀ hd.ne hI

theorem sigNeg_chartHessianAt_ospHeight_saddle :
    sigNeg (chartHessianAt (fun y => ospHeight ((extChartAt 𝓘(ℝ, ℂ) ospSaddle).symm y))
      (extChartAt 𝓘(ℝ, ℂ) ospSaddle ospSaddle)) = 1 := by
  classical
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  let w : Fin 2 → ℝ := ![ospCx ospSaddle,
    (ospG ospSaddle ^ 2)⁻¹ * (ospG ospSaddle * ospBz ospSaddle)]
  have he : QuadraticMap.Equivalent (chartHessianAt ospHeight ospSaddle)
      (QuadraticMap.weightedSumSquares ℝ w) := by
    refine ⟨{ Complex.equivRealProdLm.trans (LinearEquiv.finTwoArrow ℝ ℝ).symm with
      map_app' := ?_ }⟩
    intro v
    change _ = fderiv ℝ (fderiv ℝ ospHeight) ospSaddle v v
    rw [fderiv_fderiv_ospHeight_saddle_apply]
    simp only [LinearEquiv.finTwoArrow, Equiv.toFun_as_coe, finTwoArrowEquiv_apply,
      piFinTwoEquiv_apply, Fin.isValue, Equiv.invFun_as_coe, finTwoArrowEquiv_symm_apply,
      LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Complex.equivRealProdLm_apply, LinearEquiv.coe_mk, QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, w]
    ring
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares he]
  have hc := ospCx_pos ospSaddle_mem_ospSlab
  have hd := ospHessian_im_coeff_neg
  have hw : {i | w i < 0} = ({1} : Set (Fin 2)) := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, mem_ofPred_eq, Matrix.cons_val_zero, w,
        mem_singleton_iff, zero_ne_one, iff_false, not_lt]
      exact hc.le
    · simp only [Fin.mk_one, Fin.isValue, mem_ofPred_eq, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, w, mem_singleton_iff, iff_true]
      exact hd
  rw [hw, Set.ncard_singleton]

end Hessian

section Connected

theorem norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem ospU_eq (z : ℂ) : ospU z = ‖z‖ ^ 2 - 1 := by
  rw [norm_sq_eq_re_im]
  rfl

theorem ospF_smul (c : ℝ) (y : ℂ) :
    ospF (c • y) = ‖y‖ ^ 2 * c ^ 2 - 14 / 5 * y.im * c + 48 / 25 := by
  unfold ospF
  rw [norm_sq_eq_re_im]
  simp only [Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  ring

def ospSkeleton : Set ℂ :=
  Metric.sphere 0 1 ∪ Metric.sphere 0 (Real.sqrt 3) ∪
    (fun t : ℝ => (t : ℂ) * (-Complex.I)) '' Icc 1 (Real.sqrt 3)

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem one_le_sqrt_three : 1 ≤ Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem isPreconnected_ospSkeleton : IsPreconnected ospSkeleton := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have h1 := isPreconnected_sphere hrank (0 : ℂ) 1
  have h2 := isPreconnected_sphere hrank (0 : ℂ) (Real.sqrt 3)
  have h3 : IsPreconnected ((fun t : ℝ => (t : ℂ) * (-Complex.I)) '' Icc 1 (Real.sqrt 3)) :=
    isPreconnected_Icc.image _ (by fun_prop)
  have hmem1 : -Complex.I ∈ Metric.sphere (0 : ℂ) 1 := by simp
  have hmem1' : -Complex.I ∈ (fun t : ℝ => (t : ℂ) * (-Complex.I)) '' Icc 1 (Real.sqrt 3) :=
    ⟨1, ⟨le_rfl, one_le_sqrt_three⟩, by simp⟩
  have h13 := h1.union (-Complex.I) hmem1 hmem1' h3
  have hmem2 : ((Real.sqrt 3 : ℝ) : ℂ) * (-Complex.I) ∈ Metric.sphere (0 : ℂ) (Real.sqrt 3) := by
    simp [abs_of_nonneg (Real.sqrt_nonneg 3)]
  have hmem2' : ((Real.sqrt 3 : ℝ) : ℂ) * (-Complex.I) ∈ Metric.sphere 0 1 ∪
      (fun t : ℝ => (t : ℂ) * (-Complex.I)) '' Icc 1 (Real.sqrt 3) :=
    Or.inr ⟨Real.sqrt 3, ⟨one_le_sqrt_three, le_rfl⟩, rfl⟩
  have h := h13.union _ hmem2' hmem2 h2
  have he : Metric.sphere 0 1 ∪ (fun t : ℝ => (t : ℂ) * (-Complex.I)) '' Icc 1 (Real.sqrt 3) ∪
      Metric.sphere 0 (Real.sqrt 3) = ospSkeleton := by
    unfold ospSkeleton
    rw [union_assoc, union_assoc, union_comm ((fun t : ℝ => (t : ℂ) * (-Complex.I)) '' _)]
  rw [← he]
  exact h

theorem ospSkeleton_subset : ospSkeleton ⊆ ospSlab := by
  rintro z ((hz | hz) | ⟨t, ht, rfl⟩)
  · rw [mem_sphere_zero_iff_norm] at hz
    have hU : ospU z = 0 := by rw [ospU_eq, hz]; norm_num
    refine ⟨hU.ge, by rw [hU]; norm_num, (ospF_pos_of_ospU_nonpos hU.le).le⟩
  · rw [mem_sphere_zero_iff_norm] at hz
    have hU : ospU z = 2 := by rw [ospU_eq, hz, sqrt_three_sq]; norm_num
    refine ⟨by rw [hU]; norm_num, hU.le, ?_⟩
    have h2 : z.re ^ 2 + z.im ^ 2 = 3 := by rw [← norm_sq_eq_re_im, hz, sqrt_three_sq]
    unfold ospF
    nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 123 / 70)]
  · obtain ⟨h1, h2⟩ := ht
    have h3 : t ^ 2 ≤ 3 := by
      have := mul_le_mul h2 h2 (by linarith) (Real.sqrt_nonneg 3)
      nlinarith [sqrt_three_sq]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [ospU, ospF, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] <;>
      nlinarith

theorem exists_radial_subset {y : ℂ} (hy : y ∈ ospSlab) :
    ∃ t ⊆ ospSlab, y ∈ t ∧ (t ∩ ospSkeleton).Nonempty ∧ IsPreconnected t := by
  have hU0 := hy.1
  have hU2 := hy.2.1
  have hF := hy.2.2
  rw [ospU_eq] at hU0 hU2
  have hr1 : 1 ≤ ‖y‖ := by nlinarith [norm_nonneg y]
  have hr0 : 0 < ‖y‖ := by linarith
  have hr3 : ‖y‖ ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (norm_nonneg y)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hF1 : ospF ((1 : ℝ) • y) = ospF y := by rw [one_smul]
  have hq : ∀ c : ℝ, ospF (c • y) = ospF y + (2 * ‖y‖ ^ 2 - 14 / 5 * y.im) * (c - 1) +
      ‖y‖ ^ 2 * (c - 1) ^ 2 := by
    intro c
    rw [ospF_smul, ← hF1, ospF_smul]
    ring
  have hseg : ∀ a b : ℝ, 0 < a → (∀ c ∈ Icc a b, 1 ≤ c * ‖y‖ ∧ c * ‖y‖ ≤ Real.sqrt 3) →
      (∀ c ∈ Icc a b, 0 ≤ ospF (c • y)) → (fun c : ℝ => c • y) '' Icc a b ⊆ ospSlab := by
    rintro a b - hab hFc w ⟨c, hc, rfl⟩
    obtain ⟨h1, h2⟩ := hab c hc
    have hn : ‖c • y‖ = c * ‖y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by nlinarith [hr0])]
    refine ⟨?_, ?_, hFc c hc⟩ <;> rw [ospU_eq, hn]
    · nlinarith
    · have := mul_le_mul h2 h2 (by linarith) (Real.sqrt_nonneg 3)
      nlinarith [sqrt_three_sq]
  by_cases hd : 0 ≤ 2 * ‖y‖ ^ 2 - 14 / 5 * y.im
  · refine ⟨(fun c : ℝ => c • y) '' Icc 1 (Real.sqrt 3 / ‖y‖), ?_, ⟨1, ⟨le_rfl, ?_⟩, one_smul _ _⟩,
      ⟨(Real.sqrt 3 / ‖y‖) • y, ⟨_, ⟨?_, le_rfl⟩, rfl⟩, Or.inl (Or.inr ?_)⟩,
      isPreconnected_Icc.image _ (by fun_prop)⟩
    · refine hseg _ _ one_pos (fun c hc => ⟨?_, ?_⟩) (fun c hc => ?_)
      · nlinarith [hc.1]
      · have := (le_div_iff₀ hr0).mp hc.2
        linarith
      · rw [hq]
        have := hc.1
        nlinarith [sq_nonneg (c - 1)]
    · rw [le_div_iff₀ hr0, one_mul]
      exact hr3
    · rw [le_div_iff₀ hr0, one_mul]
      exact hr3
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg
        (div_nonneg (Real.sqrt_nonneg 3) hr0.le), div_mul_cancel₀ _ hr0.ne']
  · have hd' : 2 * ‖y‖ ^ 2 - 14 / 5 * y.im < 0 := lt_of_not_ge hd
    refine ⟨(fun c : ℝ => c • y) '' Icc (1 / ‖y‖) 1, ?_, ⟨1, ⟨?_, le_rfl⟩, one_smul _ _⟩,
      ⟨(1 / ‖y‖) • y, ⟨_, ⟨le_rfl, ?_⟩, rfl⟩, Or.inl (Or.inl ?_)⟩,
      isPreconnected_Icc.image _ (by fun_prop)⟩
    · refine hseg _ _ (by positivity) (fun c hc => ⟨?_, ?_⟩) (fun c hc => ?_)
      · have := (div_le_iff₀ hr0).mp hc.1
        linarith
      · nlinarith [hc.2]
      · rw [hq]
        have := hc.2
        nlinarith [sq_nonneg (c - 1)]
    · rw [div_le_iff₀ hr0, one_mul]
      exact hr1
    · rw [div_le_iff₀ hr0, one_mul]
      exact hr1
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (by positivity),
        div_mul_cancel₀ _ hr0.ne']

theorem isConnected_ospSlab : IsConnected ospSlab := by
  have hbase : -Complex.I ∈ ospSkeleton := Or.inl (Or.inl (by simp))
  refine ⟨⟨_, ospSkeleton_subset hbase⟩, isPreconnected_of_forall (-Complex.I) fun y hy => ?_⟩
  obtain ⟨t, hts, hyt, ⟨z, hzt, hzS⟩, htc⟩ := exists_radial_subset hy
  refine ⟨ospSkeleton ∪ t, union_subset ospSkeleton_subset hts, Or.inl hbase, Or.inr hyt, ?_⟩
  exact isPreconnected_ospSkeleton.union z hzS hzt htc

end Connected

section Pants

theorem contMDiff_ospFun : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ ospFun := fun z =>
  (contDiffAt_ospHeight (ospG_pos z.2).ne').contMDiffAt.comp z
    (contMDiff_subtype_val (U := ospDom)).contMDiffAt

theorem isCriticalPointAt_ospFun_iff (z : ospDom) :
    IsCriticalPointAt 𝓘(ℝ, ℂ) ospFun z ↔ IsCriticalPointAt 𝓘(ℝ, ℂ) ospHeight z.val :=
  isCriticalPointAt_comp_localDiffeomorph_iff (isLocalDiffeomorph_subtype_val ospDom z)
    ((contDiffAt_ospHeight (ospG_pos z.2).ne').contMDiffAt.mdifferentiableAt (by simp))

theorem eq_saddle_of_isCriticalPointAt {z : ospDom} (hz : ospFun z ∈ Icc 0 1)
    (hc : IsCriticalPointAt 𝓘(ℝ, ℂ) ospFun z) : z.val = ospSaddle := by
  rw [isCriticalPointAt_ospFun_iff, IsCriticalPointAt, mfderiv_eq_fderiv] at hc
  have hslab : z.val ∈ ospSlab := (ospHeight_mem_Icc_iff z.2).mp hz
  exact (fderiv_ospHeight_eq_zero_iff hslab).mp hc

theorem ospFun_regular (z : ospDom) (hz : ospFun z = 0 ∨ ospFun z = 1) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ospFun z ≠ 0 := by
  intro h
  have hI : ospFun z ∈ Icc 0 1 := by
    rcases hz with h' | h' <;> rw [h'] <;> norm_num
  have he := eq_saddle_of_isCriticalPointAt hI h
  have hm := ospHeight_ospSaddle_mem
  change ospHeight z.val = 0 ∨ ospHeight z.val = 1 at hz
  rw [he] at hz
  rcases hz with h' | h' <;> rw [h'] at hm <;> norm_num at hm

def ospSaddlePt : ospDom := ⟨ospSaddle, ospSlab_subset_ospDom ospSaddle_mem_ospSlab⟩

theorem ospFun_saddle_mem : ospFun ospSaddlePt ∈ Ioo 0 1 := ospHeight_ospSaddle_mem

theorem isCriticalPointAt_ospHeight_saddle : IsCriticalPointAt 𝓘(ℝ, ℂ) ospHeight ospSaddle := by
  rw [IsCriticalPointAt, mfderiv_eq_fderiv]
  exact (fderiv_ospHeight_eq_zero_iff ospSaddle_mem_ospSlab).mpr rfl

theorem isNondegenerateCriticalPointAt_ospFun_saddle :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, ℂ) ospFun ospSaddlePt :=
  (isNondegenerateCriticalPointAt_comp_localDiffeomorph_iff
    (isLocalDiffeomorph_subtype_val ospDom ospSaddlePt)
    ((contDiffAt_ospHeight ospG_ospSaddle_pos.ne').contMDiffAt.of_le (by simp))).mpr
    isNondegenerateCriticalPointAt_ospHeight_saddle

theorem sigNeg_chartHessianAt_ospFun_saddle :
    sigNeg (chartHessianAt (fun y => ospFun ((extChartAt 𝓘(ℝ, ℂ) ospSaddlePt).symm y))
      (extChartAt 𝓘(ℝ, ℂ) ospSaddlePt ospSaddlePt)) = 1 := by
  rw [← sigNeg_chartHessianAt_ospHeight_saddle]
  exact sigNeg_chartHessianAt_comp_localDiffeomorph
    (isLocalDiffeomorph_subtype_val ospDom ospSaddlePt)
    ((contDiffAt_ospHeight ospG_ospSaddle_pos.ne').contMDiffAt.of_le (by simp))
    isCriticalPointAt_ospHeight_saddle

theorem isConnected_ospFun_preimage_Icc : IsConnected (ospFun ⁻¹' Icc 0 1) := by
  rw [ospFun_preimage_Icc]
  have himg : Subtype.val '' (Subtype.val ⁻¹' ospSlab : Set ospDom) = ospSlab := by
    rw [image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact ospSlab_subset_ospDom)]
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := isConnected_ospSlab.nonempty
    exact ⟨⟨z, ospSlab_subset_ospDom hz⟩, hz⟩
  · refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    convert isConnected_ospSlab.isPreconnected using 1

abbrev ospSlabAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 (slabSet ospFun 0 1) :=
  slabAtlas Complex.finrank_real_complex contMDiff_ospFun zero_lt_one ospFun_regular

theorem exists_ospPants :
    letI := ospSlabAtlas.toChartedSpace
    ∃ e : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet ospFun 0 1,
      ∀ j t, ospFun (e (pantsPlanarBase.{u}.collar j (t, halfZero))) =
        if j.val = 0 then 1 else 0 :=
  exists_planarBase_of_saddleSlab'.{u} 𝓘(ℝ, ℂ) Complex.finrank_real_complex contMDiff_ospFun
    zero_lt_one ospFun_regular ospFun_saddle_mem isNondegenerateCriticalPointAt_ospFun_saddle
    sigNeg_chartHessianAt_ospFun_saddle
    (fun z hz hc => Subtype.ext (eq_saddle_of_isCriticalPointAt (z := z) hz hc))
    isCompact_ospFun_preimage_Icc isConnected_ospFun_preimage_Icc not_isPreconnected_ospFun_zero

end Pants

end GC.Seifert
