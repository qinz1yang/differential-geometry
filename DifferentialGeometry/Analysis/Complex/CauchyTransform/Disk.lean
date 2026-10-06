import DifferentialGeometry.Analysis.Integration.PolarDisk
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

private theorem closedBall_ae_ball (a : ℂ) (R : ℝ) :
    closedBall a R =ᵐ[volume] ball a R := by
  have hs : ∀ᵐ w : ℂ, w ∉ sphere a R := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using Measure.addHaar_sphere volume a R
  filter_upwards [hs] with w hw
  exact propext (by
    change dist w a ≤ R ↔ dist w a < R
    exact ⟨fun h => lt_of_le_of_ne h hw, le_of_lt⟩)

private theorem integrableOn_norm_rpow {q : ℝ} (hq : q < 2) (R : ℝ) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ (-q)) (ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := q)
    (by norm_num [Complex.finrank_real_complex])
    (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hq)
  · exact Eventually.of_forall fun w => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _), one_mul]
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

private theorem integral_norm_rpow {q R : ℝ} (hq : q < 2) (hR : 0 < R) :
    (∫ w in closedBall (0 : ℂ) R, ‖w‖ ^ (-q)) =
      2 * Real.pi * R ^ (2 - q) / (2 - q) := by
  rw [setIntegral_congr_set (closedBall_ae_ball 0 R),
    integral_ball_zero_eq_integral_circle (integrableOn_norm_rpow hq R)]
  have hradial :
      (fun r : ℝ => r • ∫ θ in Ioo (-Real.pi) Real.pi,
        ‖circleMap 0 r θ‖ ^ (-q)) =ᵐ[volume.restrict (Ioo 0 R)]
      fun r => (2 * Real.pi) * r ^ (1 - q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    simp only [norm_circleMap_zero, abs_of_pos hr.1]
    rw [integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_neg_eq_add,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi + Real.pi), smul_eq_mul]
    rw [show r * ((Real.pi + Real.pi) * r ^ (-q)) =
      (2 * Real.pi) * (r ^ (1 : ℝ) * r ^ (-q)) by rw [Real.rpow_one]; ring,
      ← Real.rpow_add hr.1]
    congr 2
  rw [integral_congr_ae hradial, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl (by linarith : -1 < 1 - q))]
  have he : 1 - q + 1 = 2 - q := by ring
  rw [he, Real.zero_rpow (by linarith : 2 - q ≠ 0), sub_zero]
  ring

private theorem translated_kernel_integrable_bound {a : ℂ} {R q : ℝ}
    (hR : 0 < R) (hq : q < 2) (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ‖(z : ℂ) - w‖ ^ (-q))
        (volume.comap ((↑) : closedBall a R → ℂ)) ∧
      (∫ w : closedBall a R, ‖(z : ℂ) - w‖ ^ (-q)
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) ≤
        2 * Real.pi * (2 * R) ^ (2 - q) / (2 - q) := by
  let e := Homeomorph.subLeft (z : ℂ)
  have hm : MeasurePreserving e volume volume :=
    (volume : Measure ℂ).measurePreserving_sub_left (z : ℂ)
  have hpre : e ⁻¹' closedBall (0 : ℂ) (2 * R) = closedBall (z : ℂ) (2 * R) := by
    ext w
    change dist ((z : ℂ) - w) 0 ≤ 2 * R ↔ dist w (z : ℂ) ≤ 2 * R
    rw [dist_zero_right, dist_eq_norm, norm_sub_rev]
  have hi0 : IntegrableOn (fun w : ℂ => ‖w‖ ^ (-q)) (closedBall 0 (2 * R)) :=
    (integrableOn_norm_rpow hq (2 * R)).congr_set_ae (closedBall_ae_ball 0 (2 * R))
  have hi : IntegrableOn (fun w : ℂ => ‖(z : ℂ) - w‖ ^ (-q))
      (closedBall (z : ℂ) (2 * R)) := by
    have hh := (hm.integrableOn_comp_preimage e.measurableEmbedding).mpr hi0
    simpa only [hpre, Function.comp_def, e, Homeomorph.subLeft_apply] using hh
  have hsub : closedBall a R ⊆ closedBall (z : ℂ) (2 * R) := by
    intro w hw
    apply (dist_triangle w a z).trans
    have hz : dist a (z : ℂ) ≤ R := by
      simpa only [mem_closedBall, dist_comm] using z.property
    linarith [show dist w a ≤ R from hw]
  refine ⟨(integrableOn_iff_comap_subtypeVal isClosed_closedBall.measurableSet).mp
    (hi.mono_set hsub), ?_⟩
  rw [integral_subtype_comap (μ := volume) (s := closedBall a R)
    isClosed_closedBall.measurableSet (fun w : ℂ => ‖(z : ℂ) - w‖ ^ (-q))]
  calc
    _ ≤ ∫ w in closedBall (z : ℂ) (2 * R), ‖(z : ℂ) - w‖ ^ (-q) :=
      setIntegral_mono_set hi (Eventually.of_forall fun w =>
        Real.rpow_nonneg (norm_nonneg _) _) (Eventually.of_forall hsub)
    _ = ∫ w in closedBall (0 : ℂ) (2 * R), ‖w‖ ^ (-q) := by
      have hh := hm.setIntegral_preimage_emb e.measurableEmbedding
        (fun w : ℂ => ‖w‖ ^ (-q)) (closedBall 0 (2 * R))
      simpa only [hpre, e, Homeomorph.subLeft_apply] using hh
    _ = _ := integral_norm_rpow hq (by positivity)

private theorem rpow_neg_three_halves {r : ℝ} (hr : 0 ≤ r) :
    r ^ (-(3 / 2 : ℝ)) = (r * Real.sqrt r)⁻¹ := by
  by_cases h : r = 0
  · simp [h]
  rw [Real.rpow_neg hr, Real.sqrt_eq_rpow,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (lt_of_le_of_ne hr (Ne.symm h)),
    Real.rpow_one]

private theorem inverse_sub_holder {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x⁻¹ - y⁻¹‖ ≤ Real.sqrt (2 * ‖x - y‖) *
      (‖x‖ ^ (-(3 / 2 : ℝ)) + ‖y‖ ^ (-(3 / 2 : ℝ))) := by
  have hsmall {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : ‖u‖ ≤ ‖v‖) :
      ‖u⁻¹ - v⁻¹‖ ≤ Real.sqrt (2 * ‖u - v‖) * ‖u‖ ^ (-(3 / 2 : ℝ)) := by
    have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hs : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h1 : ‖u⁻¹ - v⁻¹‖ * ‖u‖ ≤ 2 := by
      have hh := norm_sub_le (u⁻¹) (v⁻¹)
      rw [norm_inv, norm_inv] at hh
      have hvr : ‖u‖ / ‖v‖ ≤ 1 := (div_le_one hs).mpr huv
      calc
        _ ≤ (‖u‖⁻¹ + ‖v‖⁻¹) * ‖u‖ := mul_le_mul_of_nonneg_right hh hr.le
        _ = 1 + ‖u‖ / ‖v‖ := by field_simp [ne_of_gt hr, ne_of_gt hs]
        _ ≤ 2 := by linarith
    have he : ‖u⁻¹ - v⁻¹‖ = ‖u - v‖ / (‖u‖ * ‖v‖) := by
      rw [inv_sub_inv hu hv, norm_div, norm_mul, norm_sub_rev]
    have h2 : ‖u⁻¹ - v⁻¹‖ * ‖u‖ ^ 2 ≤ ‖u - v‖ := by
      rw [he, div_mul_eq_mul_div]
      apply (div_le_iff₀ (mul_pos hr hs)).mpr
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left huv hr.le) (norm_nonneg (u - v))
      nlinarith
    have hprod := mul_le_mul h1 h2 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
    have hsq : (‖u⁻¹ - v⁻¹‖ * (‖u‖ * Real.sqrt ‖u‖)) ^ 2 ≤ 2 * ‖u - v‖ := by
      calc
        _ = (‖u⁻¹ - v⁻¹‖ * ‖u‖) * (‖u⁻¹ - v⁻¹‖ * ‖u‖ ^ 2) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hr.le]
          ring
        _ ≤ _ := hprod
    have hroot : ‖u⁻¹ - v⁻¹‖ * (‖u‖ * Real.sqrt ‖u‖) ≤
        Real.sqrt (2 * ‖u - v‖) :=
      (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
    rw [rpow_neg_three_halves hr.le]
    exact (le_div_iff₀ (mul_pos hr (Real.sqrt_pos.mpr hr))).mpr hroot
  rcases le_total ‖x‖ ‖y‖ with h | h
  · exact (hsmall hx hy h).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)) (Real.sqrt_nonneg _))
  · have hh := hsmall hy hx h
    rw [norm_sub_rev (y⁻¹), norm_sub_rev y] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)) (Real.sqrt_nonneg _))

private theorem kernel_one_integrable_bound {a : ℂ} {R : ℝ} (hR : 0 < R)
    (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ‖(z : ℂ) - w‖⁻¹)
        (volume.comap ((↑) : closedBall a R → ℂ)) ∧
      (∫ w : closedBall a R, ‖(z : ℂ) - w‖⁻¹
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) ≤ 4 * Real.pi * R := by
  obtain ⟨hi, hb⟩ := translated_kernel_integrable_bound hR (by norm_num : (1 : ℝ) < 2) z
  simp only [Real.rpow_neg_one] at hi hb
  refine ⟨hi, ?_⟩
  have hb' : (∫ w : closedBall a R, ‖(z : ℂ) - w‖⁻¹
      ∂(volume.comap ((↑) : closedBall a R → ℂ))) ≤ 2 * Real.pi * (2 * R) := by
    norm_num at hb
    exact hb
  exact hb'.trans_eq (by ring)

private theorem kernel_three_halves_integrable_bound {a : ℂ} {R : ℝ} (hR : 0 < R)
    (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ‖(z : ℂ) - w‖ ^ (-(3 / 2 : ℝ)))
        (volume.comap ((↑) : closedBall a R → ℂ)) ∧
      (∫ w : closedBall a R, ‖(z : ℂ) - w‖ ^ (-(3 / 2 : ℝ))
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) ≤
        4 * Real.pi * Real.sqrt (2 * R) := by
  obtain ⟨hi, hb⟩ := translated_kernel_integrable_bound hR
    (by norm_num : (3 / 2 : ℝ) < 2) z
  refine ⟨hi, ?_⟩
  convert hb using 1
  rw [show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem cauchy_integrand_integrable {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : C(closedBall a R, F)) (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ((z : ℂ) - (w : ℂ))⁻¹ • f w)
      (volume.comap ((↑) : closedBall a R → ℂ)) := by
  have hi := (kernel_one_integrable_bound hR z).1.mul_const ‖f‖
  apply hi.mono'
  · exact ((measurable_const.sub measurable_subtype_coe).inv.aestronglyMeasurable).smul
      f.continuous.stronglyMeasurable.aestronglyMeasurable
  · exact Eventually.of_forall fun w => by
      rw [norm_smul, norm_inv]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm w) (by positivity)

private def cauchyIntegral {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (z : closedBall a R) : F :=
  (Real.pi : ℂ)⁻¹ • ∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • f w
    ∂(volume.comap ((↑) : closedBall a R → ℂ))

private theorem norm_cauchyIntegral_le {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : C(closedBall a R, F)) (z : closedBall a R) :
    ‖cauchyIntegral f z‖ ≤ (4 * R) * ‖f‖ := by
  have hi := cauchy_integrand_integrable hR f z
  obtain ⟨hk, hb⟩ := kernel_one_integrable_bound hR z
  have hπ : ‖(Real.pi : ℂ)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ = Real.pi⁻¹ * ‖∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • f w
        ∂(volume.comap ((↑) : closedBall a R → ℂ))‖ := by
      rw [cauchyIntegral, norm_smul, hπ]
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R, ‖((z : ℂ) - (w : ℂ))⁻¹ • f w‖
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R, ‖(z : ℂ) - (w : ℂ)‖⁻¹ * ‖f‖
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae hi.norm (hk.mul_const ‖f‖)
      exact Eventually.of_forall fun w => by
        dsimp only
        rw [norm_smul, norm_inv]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm w) (by positivity)
    _ = Real.pi⁻¹ * ((∫ w : closedBall a R, ‖(z : ℂ) - (w : ℂ)‖⁻¹
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) * ‖f‖) := by
      rw [integral_mul_const]
    _ ≤ Real.pi⁻¹ * ((4 * Real.pi * R) * ‖f‖) := by gcongr
    _ = _ := by field_simp

private theorem norm_cauchyIntegral_sub_le {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : C(closedBall a R, F)) (z z' : closedBall a R) :
    ‖cauchyIntegral f z - cauchyIntegral f z'‖ ≤
      16 * Real.sqrt R * ‖f‖ * Real.sqrt ‖(z : ℂ) - (z' : ℂ)‖ := by
  let μ : Measure (closedBall a R) := volume.comap ((↑) : closedBall a R → ℂ)
  let δ := ‖(z : ℂ) - (z' : ℂ)‖
  let b : ℝ := Real.sqrt (2 * δ) * ‖f‖
  let k (z : closedBall a R) (w : closedBall a R) := ‖(z : ℂ) - (w : ℂ)‖ ^ (-(3 / 2 : ℝ))
  have hb : 0 ≤ b := by positivity
  obtain ⟨hk, hkb⟩ := kernel_three_halves_integrable_bound hR z
  obtain ⟨hk', hkb'⟩ := kernel_three_halves_integrable_bound hR z'
  have hmajor : Integrable (fun w => b * (k z w + k z' w)) μ :=
    (hk.add hk').const_mul b
  have hsing : ∀ᵐ w : closedBall a R ∂μ,
      (z : ℂ) - (w : ℂ) ≠ 0 ∧ (z' : ℂ) - (w : ℂ) ≠ 0 := by
    apply (ae_restrict_iff_subtype (μ := (volume : Measure ℂ)) (s := closedBall a R)
      (p := fun w : ℂ => (z : ℂ) - w ≠ 0 ∧ (z' : ℂ) - w ≠ 0)
      isClosed_closedBall.measurableSet).mp
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (z : ℂ)),
      ae_restrict_of_ae (volume.ae_ne (z' : ℂ))] with w hw hw'
    exact ⟨sub_ne_zero.mpr hw.symm, sub_ne_zero.mpr hw'.symm⟩
  have hpoint : ∀ᵐ w : closedBall a R ∂μ,
      ‖((z : ℂ) - (w : ℂ))⁻¹ • f w - ((z' : ℂ) - (w : ℂ))⁻¹ • f w‖ ≤
        b * (k z w + k z' w) := by
    filter_upwards [hsing] with w hw
    rw [← sub_smul, norm_smul]
    have hh := inverse_sub_holder hw.1 hw.2
    rw [sub_sub_sub_cancel_right] at hh
    calc
      _ ≤ (Real.sqrt (2 * δ) * (k z w + k z' w)) * ‖f‖ :=
        mul_le_mul hh (f.norm_coe_le_norm w) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [b]; ring
  have hi := (cauchy_integrand_integrable hR f z).sub
    (cauchy_integrand_integrable hR f z')
  have hπ : ‖(Real.pi : ℂ)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ = Real.pi⁻¹ * ‖∫ w : closedBall a R,
        (((z : ℂ) - (w : ℂ))⁻¹ • f w - ((z' : ℂ) - (w : ℂ))⁻¹ • f w) ∂μ‖ := by
      rw [cauchyIntegral, cauchyIntegral, ← smul_sub,
        ← integral_sub (cauchy_integrand_integrable hR f z)
          (cauchy_integrand_integrable hR f z'), norm_smul, hπ]
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R,
        ‖((z : ℂ) - (w : ℂ))⁻¹ • f w - ((z' : ℂ) - (w : ℂ))⁻¹ • f w‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R, b * (k z w + k z' w) ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hi.norm hmajor hpoint) (by positivity)
    _ = Real.pi⁻¹ * (b * ((∫ w, k z w ∂μ) + ∫ w, k z' w ∂μ)) := by
      rw [integral_const_mul, integral_add hk hk']
    _ ≤ Real.pi⁻¹ * (b * (8 * Real.pi * Real.sqrt (2 * R))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hb
      linarith
    _ = _ := by
      dsimp [b, δ]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ = (8 * (Real.sqrt 2) ^ 2) * Real.sqrt R * ‖f‖ *
            Real.sqrt ‖(z : ℂ) - (z' : ℂ)‖ := by field_simp
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

private theorem continuous_cauchyIntegral {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : C(closedBall a R, F)) : Continuous (cauchyIntegral f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun w => norm_nonneg _) (fun w => norm_cauchyIntegral_sub_le hR f w z)
  have hc : Continuous (fun w : closedBall a R =>
      16 * Real.sqrt R * ‖f‖ * Real.sqrt ‖(w : ℂ) - (z : ℂ)‖) :=
    continuous_const.mul (Real.continuous_sqrt.comp
      ((continuous_subtype_val.sub continuous_const).norm))
  simpa using hc.tendsto z

private def cauchyLinearMap (a : ℂ) (R : ℝ) (hR : 0 < R) :
    C(closedBall a R, F) →ₗ[ℂ] C(closedBall a R, F) where
  toFun f := ⟨cauchyIntegral f, continuous_cauchyIntegral hR f⟩
  map_add' f g := by
    ext z
    change cauchyIntegral (f + g) z = cauchyIntegral f z + cauchyIntegral g z
    simp only [cauchyIntegral, ContinuousMap.add_apply, smul_add]
    rw [integral_add (cauchy_integrand_integrable hR f z)
      (cauchy_integrand_integrable hR g z), smul_add]
  map_smul' c f := by
    ext z
    change cauchyIntegral (c • f) z = c • cauchyIntegral f z
    simp only [cauchyIntegral, ContinuousMap.smul_apply]
    have he : (fun w : closedBall a R => ((z : ℂ) - (w : ℂ))⁻¹ • (c • f w)) =
        fun w : closedBall a R => c • (((z : ℂ) - (w : ℂ))⁻¹ • f w) :=
      funext fun w => smul_comm _ _ _
    rw [he, integral_smul, smul_comm]

private theorem norm_cauchyLinearMap_le (a : ℂ) (R : ℝ) (hR : 0 < R)
    (f : C(closedBall a R, F)) :
    ‖cauchyLinearMap a R hR f‖ ≤ (4 * R) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact norm_cauchyIntegral_le hR f

/-- The disk Cauchy integral on continuous normed-space-valued functions, with the literal
Lebesgue measure on the closed disk. Its continuity follows from the singular-kernel
Hölder estimate; no differentiability or right-inverse assertion is part of this definition. -/
def diskCauchyTransform (a : ℂ) (R : ℝ) (hR : 0 < R) :
    C(closedBall a R, F) →L[ℂ] C(closedBall a R, F) :=
  (cauchyLinearMap a R hR).mkContinuous (4 * R) (norm_cauchyLinearMap_le a R hR)


/-- The defining integral uses the explicit comap of ambient Lebesgue measure. -/
theorem diskCauchyTransform_apply (a : ℂ) (R : ℝ) (hR : 0 < R)
    (f : C(closedBall a R, F)) (z : closedBall a R) :
    diskCauchyTransform a R hR f z =
      (Real.pi : ℂ)⁻¹ • ∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • f w
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) := rfl

/-- The disk Cauchy operator has norm at most four times the radius. -/
theorem norm_diskCauchyTransform_le (a : ℂ) (R : ℝ) (hR : 0 < R) :
    ‖diskCauchyTransform (F := F) a R hR‖ ≤ 4 * R :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- A quantitative one-half Hölder estimate, valid through the boundary of the disk. -/
theorem diskCauchyTransform_sub_le (a : ℂ) (R : ℝ) (hR : 0 < R)
    (f : C(closedBall a R, F)) (z w : closedBall a R) :
    ‖diskCauchyTransform a R hR f z - diskCauchyTransform a R hR f w‖ ≤
      16 * Real.sqrt R * ‖f‖ * Real.sqrt ‖(z : ℂ) - (w : ℂ)‖ :=
  norm_cauchyIntegral_sub_le hR f z w


/-- The inverse-distance kernel is integrable on the disk, with its uniform radius bound. -/
theorem integrable_disk_inverse_kernel_and_bound {a : ℂ} {R : ℝ} (hR : 0 < R)
    (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ‖(z : ℂ) - w‖⁻¹)
        (volume.comap ((↑) : closedBall a R → ℂ)) ∧
      (∫ w : closedBall a R, ‖(z : ℂ) - w‖⁻¹
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) ≤ 4 * Real.pi * R :=
  kernel_one_integrable_bound hR z

/-- The three-halves-distance kernel is integrable on the disk, with its uniform bound. -/
theorem integrable_disk_three_halves_kernel_and_bound {a : ℂ} {R : ℝ} (hR : 0 < R)
    (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ‖(z : ℂ) - w‖ ^ (-(3 / 2 : ℝ)))
        (volume.comap ((↑) : closedBall a R → ℂ)) ∧
      (∫ w : closedBall a R, ‖(z : ℂ) - w‖ ^ (-(3 / 2 : ℝ))
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) ≤
        4 * Real.pi * Real.sqrt (2 * R) :=
  kernel_three_halves_integrable_bound hR z

/-- A one-half Hölder difference estimate for the inverse kernel away from its poles. -/
theorem norm_inv_sub_le_sqrt {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x⁻¹ - y⁻¹‖ ≤ Real.sqrt (2 * ‖x - y‖) *
      (‖x‖ ^ (-(3 / 2 : ℝ)) + ‖y‖ ^ (-(3 / 2 : ℝ))) :=
  inverse_sub_holder hx hy

end DifferentialGeometry.Analysis
