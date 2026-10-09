import DifferentialGeometry.Analysis.Complex.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Homeomorph

private theorem horizontal_line_curve (h : ℂ → ℂ) (x y : ℝ) :
    (fun t : ℝ => h ((⟨x, y⟩ : ℂ) + t • (1 : ℂ))) =
      (fun t : ℝ => h (⟨x + t, y⟩ : ℂ)) := by
  funext t
  congr 1
  apply Complex.ext <;> simp

private theorem lineDifferentiableAt_horizontal_iff (h : ℂ → ℂ) (x y : ℝ) :
    LineDifferentiableAt ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) ↔
      DifferentiableAt ℝ (fun t : ℝ => h (⟨t, y⟩ : ℂ)) x := by
  rw [LineDifferentiableAt, horizontal_line_curve]
  simpa only [add_zero] using
    (differentiableAt_comp_add_left (𝕜 := ℝ)
      (f := fun t : ℝ => h (⟨t, y⟩ : ℂ)) (x := (0 : ℝ)) x)

private theorem lineDeriv_horizontal (h : ℂ → ℂ) (x y : ℝ) :
    lineDeriv ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) =
      deriv (fun t : ℝ => h (⟨t, y⟩ : ℂ)) x := by
  rw [lineDeriv, horizontal_line_curve]
  simpa only [add_zero] using
    (deriv_comp_const_add (fun t : ℝ => h (⟨t, y⟩ : ℂ)) x 0)

private theorem measurableSet_horizontal_regular (h : ℂ ≃ₜ ℂ) (a b c d : ℝ) :
    MeasurableSet {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
      LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0} := by
  have hd : MeasurableSet {z : ℂ | LineDifferentiableAt ℝ h z (1 : ℂ)} :=
    measurableSet_lineDifferentiableAt h.continuous
  have hn : MeasurableSet {z : ℂ | lineDeriv ℝ h z (1 : ℂ) ≠ 0} :=
    ((measurable_lineDeriv h.continuous) (measurableSet_singleton (0 : ℂ))).compl
  exact (isOpen_Ioo.measurableSet.preimage Complex.continuous_re.measurable).inter
    ((isOpen_Ioo.measurableSet.preimage Complex.continuous_im.measurable).inter (hd.inter hn))

theorem volume_pos_lineDeriv_ne_zero_horizontal
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    0 < MeasureTheory.volume {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
      LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0} := by
  let S : Set ℂ := {z | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
    LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0}
  have hS : MeasurableSet S := measurableSet_horizontal_regular h a b c d
  by_contra hnpos
  have hzero : MeasureTheory.volume S = 0 := le_antisymm (le_of_not_gt hnpos) bot_le
  let ψ : ℝ × ℝ → ℂ := fun p => ⟨p.2, p.1⟩
  have hψ : MeasureTheory.MeasurePreserving ψ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume := by
    exact (MeasureTheory.MeasurePreserving.symm Complex.measurableEquivRealProd
      Complex.volume_preserving_equiv_real_prod).comp MeasureTheory.Measure.measurePreserving_swap
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      (ψ ⁻¹' S) = 0 := (hψ.measure_preimage hS.nullMeasurableSet).trans hzero
  have hsections := MeasureTheory.Measure.measure_ae_null_of_prod_null hprod
  have hgood : ∀ᵐ y : ℝ ∂MeasureTheory.volume.restrict (Set.Ioo c d),
      AbsolutelyContinuousOnInterval (fun x : ℝ => h (⟨x, y⟩ : ℂ)) a b ∧
        MeasureTheory.volume ((fun x : ℝ => (⟨x, y⟩ : ℂ)) ⁻¹' S) = 0 := by
    filter_upwards [h.ae_absolutelyContinuousOnInterval_horizontal κ hdisks a b c d,
      MeasureTheory.ae_restrict_of_ae hsections] with y hy hnull
    exact ⟨hy, hnull⟩
  have hheightpos : MeasureTheory.volume (Set.Ioo c d) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)).ne'
  obtain ⟨y, hycd, hyAC, hyzero⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hheightpos hgood
  let g (x : ℝ) := h (⟨x, y⟩ : ℂ)
  have hdiff := hyAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hnot : ∀ᵐ x : ℝ ∂MeasureTheory.volume, (⟨x, y⟩ : ℂ) ∉ S :=
    (MeasureTheory.measure_eq_zero_iff_ae_notMem).mp hyzero
  have hae0 : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ∈ Set.uIcc a b → HasDerivAt g 0 x := by
    have hna : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ a := by simp [MeasureTheory.ae_iff]
    have hnb : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ b := by simp [MeasureTheory.ae_iff]
    filter_upwards [hdiff, hnot, hna, hnb] with x hdx hns hxa hxb
    intro hx
    have hxIcc : x ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab.le] using hx
    have hxIoo : x ∈ Set.Ioo a b :=
      ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxa), lt_of_le_of_ne hxIcc.2 hxb⟩
    have hdx' : DifferentiableAt ℝ g x := hdx hx
    have hline : LineDifferentiableAt ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) :=
      (lineDifferentiableAt_horizontal_iff h x y).mpr hdx'
    have hder : lineDeriv ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) = 0 := by
      by_contra hne
      exact hns ⟨hxIoo, hycd, hline, hne⟩
    have hgzero : deriv g x = 0 := by
      rw [← lineDeriv_horizontal h x y]
      exact hder
    rw [← hgzero]
    exact hdx'.hasDerivAt
  obtain ⟨w, hw⟩ := hyAC.const_of_ae_hasDerivAt_zero hae0
  have heq : h (⟨a, y⟩ : ℂ) = h (⟨b, y⟩ : ℂ) :=
    (hw a (Set.left_mem_uIcc)).trans (hw b (Set.right_mem_uIcc)).symm
  have hab' : a = b := congrArg Complex.re (h.injective heq)
  exact hab.ne hab'

private theorem ae_lineDifferentiableAt_horizontal
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ) :
    ∀ᵐ z : ℂ ∂MeasureTheory.volume, LineDifferentiableAt ℝ h z (1 : ℂ) := by
  let ψ : ℝ × ℝ → ℂ := fun p => ⟨p.2, p.1⟩
  have hψc : Continuous ψ := by
    change Continuous (Complex.measurableEquivRealProd.symm ∘ Prod.swap)
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_swap
  have hrect (n : ℕ) :
      ∀ᵐ p : ℝ × ℝ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume),
        p.1 ∈ Set.Ioo (-(n : ℝ)) n → p.2 ∈ Set.Ioo (-(n : ℝ)) n →
          LineDifferentiableAt ℝ h (ψ p) (1 : ℂ) := by
    have hm : MeasurableSet {p : ℝ × ℝ |
        p.1 ∈ Set.Ioo (-(n : ℝ)) n → p.2 ∈ Set.Ioo (-(n : ℝ)) n →
          LineDifferentiableAt ℝ h (ψ p) (1 : ℂ)} := by
      have hd := (measurableSet_lineDifferentiableAt (𝕜 := ℝ) (v := (1 : ℂ))
        h.continuous).preimage hψc.measurable
      have hfst : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Ioo (-(n : ℝ)) n} :=
        isOpen_Ioo.measurableSet.preimage measurable_fst
      have hsnd : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo (-(n : ℝ)) n} :=
        isOpen_Ioo.measurableSet.preimage measurable_snd
      convert hfst.compl.union (hsnd.compl.union hd) using 1
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage,
        imp_iff_not_or]
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae hm).mpr
    have hac := (MeasureTheory.ae_restrict_iff' isOpen_Ioo.measurableSet).mp
      (h.ae_absolutelyContinuousOnInterval_horizontal κ hdisks (-(n : ℝ)) n (-(n : ℝ)) n)
    filter_upwards [hac] with y hy
    by_cases hyin : y ∈ Set.Ioo (-(n : ℝ)) n
    · have hd := (hy hyin).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
      filter_upwards [hd] with x hx
      intro _ hxint
      apply (lineDifferentiableAt_horizontal_iff h x y).mpr
      exact hx (by
        rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n : ℝ) ≤ n)]
        exact ⟨hxint.1.le, hxint.2.le⟩)
    · exact Filter.Eventually.of_forall fun _ hyfalse => False.elim (hyin hyfalse)
  have hall : ∀ᵐ p : ℝ × ℝ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume),
      ∀ n : ℕ, p.1 ∈ Set.Ioo (-(n : ℝ)) n → p.2 ∈ Set.Ioo (-(n : ℝ)) n →
        LineDifferentiableAt ℝ h (ψ p) (1 : ℂ) := MeasureTheory.ae_all_iff.mpr hrect
  have hcoord : MeasureTheory.MeasurePreserving (fun z : ℂ => (z.im, z.re))
      MeasureTheory.volume ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) :=
    MeasureTheory.Measure.measurePreserving_swap.comp Complex.volume_preserving_equiv_real_prod
  filter_upwards [hcoord.quasiMeasurePreserving.ae hall] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt (max |z.re| |z.im|)
  have hre : |z.re| < n := (le_max_left _ _).trans_lt hn
  have him : |z.im| < n := (le_max_right _ _).trans_lt hn
  exact hz n (abs_lt.mp him) (abs_lt.mp hre)

private theorem complex_smul_ball_image (v : ℂ) (hv : v ≠ 0) (z : ℂ) (r : ℝ) :
    (fun w : ℂ => v * w) '' Metric.ball z r = Metric.ball (v * z) (‖v‖ * r) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, ← mul_sub, norm_mul]
    exact mul_lt_mul_of_pos_left (by simpa only [Metric.mem_ball, dist_eq_norm] using hu) (norm_pos_iff.mpr hv)
  · intro hw
    refine ⟨v⁻¹ * w, ?_, by simp [hv]⟩
    have he : v * (v⁻¹ * w - z) = w - v * z := by rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    have hnorm : ‖v‖ * ‖v⁻¹ * w - z‖ = ‖w - v * z‖ := by rw [← norm_mul, he]
    apply Metric.mem_ball.mpr
    rw [dist_eq_norm]
    apply (mul_lt_mul_iff_right₀ (norm_pos_iff.mpr hv)).mp
    simpa only [hnorm, dist_eq_norm] using Metric.mem_ball.mp hw

private theorem complex_smul_closedBall_image (v : ℂ) (hv : v ≠ 0) (z : ℂ) (r : ℝ) :
    (fun w : ℂ => v * w) '' Metric.closedBall z r = Metric.closedBall (v * z) (‖v‖ * r) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu) (norm_nonneg v)
  · intro hw
    refine ⟨v⁻¹ * w, ?_, by simp [hv]⟩
    have he : v * (v⁻¹ * w - z) = w - v * z := by rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    have hnorm : ‖v‖ * ‖v⁻¹ * w - z‖ = ‖w - v * z‖ := by rw [← norm_mul, he]
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hv)).mp
    simpa only [hnorm, dist_eq_norm] using Metric.mem_closedBall.mp hw

theorem ae_lineDifferentiableAt
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (v : ℂ) : ∀ᵐ z : ℂ ∂MeasureTheory.volume, LineDifferentiableAt ℝ h z v := by
  by_cases hv : v = 0
  · subst v
    exact Filter.Eventually.of_forall fun _ => lineDifferentiableAt_zero
  let L : ℂ ≃L[ℝ] ℂ :=
    ((LinearEquiv.smulOfNeZero ℂ ℂ v hv).restrictScalars ℝ).toContinuousLinearEquiv
  have hL (z : ℂ) : L z = v * z := rfl
  let f : ℂ ≃ₜ ℂ := L.toHomeomorph.trans h
  have hf (z : ℂ) : f z = h (v * z) := rfl
  have hfdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (f z) ρ ⊆ f '' Metric.ball z r ∧
      f '' Metric.closedBall z r ⊆ Metric.closedBall (f z) R ∧ R ≤ κ * ρ := by
    intro z r hr
    obtain ⟨ρ, R, hρ, hi, ho, hratio⟩ := hdisks (v * z) (‖v‖ * r)
      (mul_pos (norm_pos_iff.mpr hv) hr)
    refine ⟨ρ, R, hρ, ?_, ?_, hratio⟩
    · rw [← complex_smul_ball_image v hv z r, Set.image_image] at hi
      exact hi
    · rw [← complex_smul_closedBall_image v hv z r, Set.image_image] at ho
      exact ho
  have hhorizontal := ae_lineDifferentiableAt_horizontal f κ hfdisks
  let A : Set ℂ := {z | ¬LineDifferentiableAt ℝ f z (1 : ℂ)}
  have hAnull : MeasureTheory.volume A = 0 := by
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    simpa only [A, Set.mem_ofPred_eq, not_not] using hhorizontal
  have himageNull : MeasureTheory.volume (L '' A) = 0 := by
    rw [MeasureTheory.Measure.addHaar_image_continuousLinearEquiv, hAnull, mul_zero]
  have hout := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp himageNull
  filter_upwards [hout] with z hz
  have hg : LineDifferentiableAt ℝ f (L.symm z) (1 : ℂ) := by
    by_contra hnot
    exact hz ⟨L.symm z, hnot, L.apply_symm_apply z⟩
  have hg' : LineDifferentiableAt ℝ (h ∘ L.toLinearMap) (L.symm z) (1 : ℂ) := hg
  have hd := hg'.of_comp
  change LineDifferentiableAt ℝ h (L (L.symm z)) (L 1) at hd
  simpa only [L.apply_symm_apply, hL, mul_one] using hd

theorem volume_pos_rational_lineDifferentiableAt_and_lineDeriv_ne_zero
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    let S := {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
      (∀ p q : ℚ, LineDifferentiableAt ℝ h z
        (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)) ∧
      lineDeriv ℝ h z (1 : ℂ) ≠ 0}
    MeasurableSet S ∧ 0 < MeasureTheory.volume S := by
  let U : Set ℂ := {z | ∀ p q : ℚ, LineDifferentiableAt ℝ h z
    (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)}
  have hU : MeasurableSet U := by
    simp only [U, Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q =>
      measurableSet_lineDifferentiableAt h.continuous
  have hUae : ∀ᵐ z : ℂ ∂MeasureTheory.volume, z ∈ U := by
    apply MeasureTheory.ae_all_iff.mpr
    intro p
    apply MeasureTheory.ae_all_iff.mpr
    intro q
    exact h.ae_lineDifferentiableAt κ hdisks (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)
  have hnonzero : MeasurableSet {z : ℂ | lineDeriv ℝ h z (1 : ℂ) ≠ 0} :=
    ((measurable_lineDeriv h.continuous) (measurableSet_singleton (0 : ℂ))).compl
  constructor
  · exact (isOpen_Ioo.measurableSet.preimage Complex.continuous_re.measurable).inter
      ((isOpen_Ioo.measurableSet.preimage Complex.continuous_im.measurable).inter
        (hU.inter hnonzero))
  · have hpos := h.volume_pos_lineDeriv_ne_zero_horizontal κ hdisks a b c d hab hcd
    have heq : {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
        (∀ p q : ℚ, LineDifferentiableAt ℝ h z
          (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0} =ᵐ[MeasureTheory.volume]
        {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
          LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0} := by
      filter_upwards [hUae] with z hz
      have hhorizontal : LineDifferentiableAt ℝ h z (1 : ℂ) := by
        simpa only [Rat.cast_one, Rat.cast_zero, Complex.ofReal_one, Complex.ofReal_zero,
          zero_mul, add_zero] using hz 1 0
      apply propext
      constructor
      · rintro ⟨hre, him, _, hn⟩
        exact ⟨hre, him, hhorizontal, hn⟩
      · rintro ⟨hre, him, _, hn⟩
        exact ⟨hre, him, hz, hn⟩
    rw [MeasureTheory.measure_congr heq]
    exact hpos

end Homeomorph
