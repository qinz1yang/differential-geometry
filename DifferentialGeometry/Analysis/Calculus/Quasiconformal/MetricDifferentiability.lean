/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Stepanov
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.MetricDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasLocalDistortion (f : E → E) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ∀ x : E, ∃ r : ℝ, 0 < r ∧
    ∀ y z : E, dist y x < r → dist z x < r → dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x)

def HasGlobalDistortion (f : E → E) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ∀ x y z : E, dist y x ≤ dist z x →
    dist (f y) (f x) ≤ H * dist (f z) (f x)

omit [NormedSpace ℝ E] in
theorem HasGlobalDistortion.local {f : E → E} (hf : HasGlobalDistortion f) :
    HasLocalDistortion f := by
  obtain ⟨H, hH, hb⟩ := hf
  exact ⟨H, hH, fun x => ⟨1, zero_lt_one, fun y z _ _ hyz => hb x y z hyz⟩⟩

theorem radius_comparison_pow_two {f : E → E} {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y z : E, dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x))
    (k : ℕ) (x y z : E) (hyz : dist y x ≤ (2 : ℝ) ^ k * dist z x) :
    dist (f y) (f x) ≤ ((H + 1) ^ k * H) * dist (f z) (f x) := by
  induction k generalizing x y z with
  | zero => simpa using hf x y z (by simpa using hyz)
  | succ k ih =>
    let p := midpoint ℝ x y
    have hp : dist p x = dist y x / 2 := by
      simp [p, dist_comm, div_eq_mul_inv, mul_comm]
    have hmid : dist (f y) (f p) ≤ H * dist (f x) (f p) :=
      hf p y x (by simp [p, dist_left_midpoint, dist_right_midpoint])
    have hhalf : dist p x ≤ (2 : ℝ) ^ k * dist z x := by
      rw [hp]
      rw [pow_succ] at hyz
      linarith
    calc
      _ ≤ dist (f y) (f p) + dist (f p) (f x) := dist_triangle _ _ _
      _ ≤ (H + 1) * dist (f p) (f x) := by rw [dist_comm (f x) (f p)] at hmid; linarith
      _ ≤ (H + 1) * (((H + 1) ^ k * H) * dist (f z) (f x)) :=
        mul_le_mul_of_nonneg_left (ih x p z hhalf) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem HasGlobalDistortion.conjugate {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : W ≃L[ℝ] E) (f : E ≃ₜ E) (hf : HasGlobalDistortion f) :
    HasGlobalDistortion ((e.toHomeomorph.trans f).trans e.symm.toHomeomorph) := by
  obtain ⟨H, hH, hcomp⟩ := hf
  let L := ‖e.toContinuousLinearMap‖
  let M := ‖e.symm.toContinuousLinearMap‖
  obtain ⟨k, hk⟩ := exists_nat_gt (L * M)
  have hk2 : L * M ≤ (2 : ℝ) ^ k :=
    hk.le.trans (by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le)
  let B := (H + 1) ^ k * H
  have hL : 0 ≤ L := norm_nonneg _
  have hM : 0 ≤ M := norm_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨M * B * L + 1, by positivity, fun x y z hyz => ?_⟩
  have hz : dist z x ≤ M * dist (e z) (e x) := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.toContinuousLinearMap.dist_le_opNorm (e z) (e x)
  have he : dist (e y) (e x) ≤ (2 : ℝ) ^ k * dist (e z) (e x) := by
    calc
      _ ≤ L * dist y x := e.toContinuousLinearMap.dist_le_opNorm y x
      _ ≤ L * dist z x := mul_le_mul_of_nonneg_left hyz hL
      _ ≤ L * (M * dist (e z) (e x)) := mul_le_mul_of_nonneg_left hz hL
      _ = (L * M) * dist (e z) (e x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk2 dist_nonneg
  change dist (e.symm (f (e y))) (e.symm (f (e x))) ≤
    (M * B * L + 1) * dist (e.symm (f (e z))) (e.symm (f (e x)))
  have hb := radius_comparison_pow_two hH hcomp k (e x) (e y) (e z) he
  have hz' : dist (f (e z)) (f (e x)) ≤
      L * dist (e.symm (f (e z))) (e.symm (f (e x))) := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      e.toContinuousLinearMap.dist_le_opNorm (e.symm (f (e z))) (e.symm (f (e x)))
  calc
    _ ≤ M * dist (f (e y)) (f (e x)) :=
      e.symm.toContinuousLinearMap.dist_le_opNorm _ _
    _ ≤ M * (B * dist (f (e z)) (f (e x))) := mul_le_mul_of_nonneg_left hb hM
    _ ≤ M * (B * (L * dist (e.symm (f (e z))) (e.symm (f (e x))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' hB) hM
    _ ≤ _ := by nlinarith [dist_nonneg (x := e.symm (f (e z))) (y := e.symm (f (e x)))]

theorem ball_subset_image_ball (f : E ≃ₜ E) {x : E} {r s : ℝ} (hr : 0 < r)
    (hboundary : ∀ z : E, dist z x = r → s ≤ dist (f z) (f x)) :
    ball (f x) s ⊆ f '' ball x r := by
  intro w hw
  refine ⟨f.symm w, ?_, f.apply_symm_apply w⟩
  by_contra! hnot
  simp only [mem_ball, not_lt] at hnot
  let p : ℝ → E := fun t => f.symm (f x + t • (w - f x))
  have hp : Continuous p := f.symm.continuous.comp (by fun_prop)
  have hp0 : p 0 = x := by simp [p]
  have hp1 : p 1 = f.symm w := by simp [p]
  have hd : Continuous (fun t => dist (p t) x) := hp.dist continuous_const
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hd.continuousOn (show r ∈ Icc (dist (p 0) x) (dist (p 1) x) by
      simpa [hp0, hp1] using And.intro hr.le hnot)
  have hpt : dist (f (p t)) (f x) ≤ dist w (f x) := by
    simp only [p, Homeomorph.apply_symm_apply, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact (not_lt_of_ge ((hboundary (p t) htr).trans hpt)) hw

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

def imageMeasure (f : E ≃ₜ E) : Measure E := μ.comap f

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
theorem imageMeasure_apply (f : E ≃ₜ E) (s : Set E) :
    imageMeasure μ f s = μ (f '' s) :=
  f.toMeasurableEquiv.measurableEmbedding.comap_apply μ s

instance imageMeasure_isFiniteMeasureOnCompacts (f : E ≃ₜ E) :
    IsFiniteMeasureOnCompacts (imageMeasure μ f) where
  lt_top_of_isCompact K hK := by
    rw [imageMeasure_apply]
    exact (hK.image f.continuous).measure_lt_top

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
theorem image_ball_volume_lower (f : E ≃ₜ E) {x y : E} {H r₀ : ℝ}
    (hH : 0 < H) (hxy : y ≠ x) (hyr : dist y x < r₀)
    (hcomp : ∀ z : E, dist z x < r₀ → dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x)) :
    μ (ball (f x) (dist (f y) (f x) / H)) ≤
      imageMeasure μ f (closedBall x (dist y x)) := by
  rw [imageMeasure_apply]
  apply measure_mono
  apply (ball_subset_image_ball f (dist_pos.mpr hxy) ?_).trans
    (image_mono ball_subset_closedBall)
  intro z hz
  apply (div_le_iff₀ hH).mpr
  simpa [mul_comm] using hcomp z (hz ▸ hyr) hz.ge

theorem ae_centered_bound [Nontrivial E] (f : E ≃ₜ E) (hf : HasLocalDistortion f) :
    ∀ᵐ x ∂μ, ∃ C r : ℝ, 0 < r ∧
      ∀ y, dist y x < r → dist (f y) (f x) ≤ C * dist y x := by
  obtain ⟨H, hH, hlocal⟩ := hf
  let ν := imageMeasure μ f
  have hν : IsLocallyFiniteMeasure ν := inferInstance
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν μ, Measure.rnDeriv_lt_top ν μ]
    with x hx hfin
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin.ne
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (closedBall x r) / μ (closedBall x r) < N :=
    hx.eventually (Iio_mem_nhds hN)
  obtain ⟨a, ha, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  obtain ⟨r₀, hr₀, hcomp⟩ := hlocal x
  refine ⟨H * ((N : ℝ) + 1), min a r₀, lt_min ha hr₀, fun y hy => ?_⟩
  by_cases hyx : y = x
  · subst y
    simp
  have hr : 0 < dist y x := dist_pos.mpr hyx
  have hratio := hbound ⟨hr, (lt_min_iff.mp hy).1.le⟩
  have hμr : μ (closedBall x (dist y x)) ≠ 0 := (measure_closedBall_pos μ x hr).ne'
  have hμrtop : μ (closedBall x (dist y x)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hl : μ (ball (f x) (dist (f y) (f x) / H)) <
      (N : ℝ≥0∞) * μ (closedBall x (dist y x)) := by
    apply (image_ball_volume_lower μ f hH hyx (lt_min_iff.mp hy).2
      (fun z hz hzy => hcomp y z (lt_min_iff.mp hy).2 hz hzy)).trans_lt
    exact (ENNReal.div_lt_iff (Or.inl hμr) (Or.inl hμrtop)).mp hratio
  have hv : 0 < (μ (ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have htgt : 0 < dist (f y) (f x) / H :=
    div_pos (dist_pos.mpr (fun h => hyx (f.injective h))) hH
  have hreal : (dist (f y) (f x) / H) ^ Module.finrank ℝ E <
      (N : ℝ) * dist y x ^ Module.finrank ℝ E := by
    have h := (ENNReal.toReal_lt_toReal (measure_ball_lt_top.ne)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hμrtop)).mpr hl
    rw [addHaar_ball_of_pos μ _ htgt, addHaar_closedBall μ _ hr.le] at h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg htgt.le _),
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)] at h
    nlinarith
  have hpow : (dist (f y) (f x) / H / dist y x) ^ Module.finrank ℝ E < (N : ℝ) := by
    rw [div_pow, div_lt_iff₀ (pow_pos hr _)]
    exact hreal
  have hsmall : dist (f y) (f x) / H / dist y x < (N : ℝ) + 1 := by
    by_contra! hlarge
    have hone : 1 ≤ dist (f y) (f x) / H / dist y x :=
      le_trans (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hlarge
    have hp := le_self_pow₀ hone (Module.finrank_pos (R := ℝ) (M := E)).ne'
    linarith
  have h := (div_lt_iff₀ hr).mp hsmall
  have h' := (div_lt_iff₀ hH).mp h
  nlinarith

theorem ae_differentiableAt [Nontrivial E] (f : E ≃ₜ E) (hf : HasLocalDistortion f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x :=
  Stepanov.ae_differentiableAt_of_ae_centered_bound μ f.continuous (ae_centered_bound μ f hf)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_derivative_comparison {f : E → E} {x : E} {A : E →L[ℝ] E}
    {H r : ℝ} (hr : 0 < r)
    (hcomp : ∀ y z : E, dist y x < r → dist z x < r → dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x))
    (hA : HasFDerivAt f A x) (v w : E) (hvw : ‖v‖ ≤ ‖w‖) :
    ‖A v‖ ≤ H * ‖A w‖ := by
  have hv := (hA.hasLineDerivAt v).tendsto_slope_zero_right.norm
  have hw := (hA.hasLineDerivAt w).tendsto_slope_zero_right.norm
  have hp (u : E) : ∀ᶠ t : ℝ in 𝓝[>] 0, dist (x + t • u) x < r := by
    have hc : Continuous (fun t : ℝ => x + t • u) := by fun_prop
    have ht : Tendsto (fun t : ℝ => x + t • u) (𝓝[>] 0) (𝓝 x) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ht (ball_mem_nhds x hr)
  apply le_of_tendsto_of_tendsto hv (hw.const_mul H)
  filter_upwards [hp v, hp w, self_mem_nhdsWithin] with t htv htw ht
  have ht0 : 0 < t := ht
  have hb := hcomp (x + t • v) (x + t • w) htv htw (by
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht0] using mul_le_mul_of_nonneg_left hvw ht0.le)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
  simpa only [dist_eq_norm, mul_assoc, mul_left_comm H] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht0.le)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem zero_or_injective_of_norm_comparison (A : E →L[ℝ] E) (H : ℝ)
    (hcomp : ∀ v w : E, ‖v‖ ≤ ‖w‖ → ‖A v‖ ≤ H * ‖A w‖) :
    A = 0 ∨ Function.Injective A := by
  by_cases hi : Function.Injective A
  · exact Or.inr hi
  left
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hi
  have hw : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hwA : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hwn : 0 < ‖u - v‖ := norm_pos_iff.mpr hw
  ext z
  have hn : ‖(‖z‖ / ‖u - v‖) • (u - v)‖ = ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hwn.le),
      div_mul_cancel₀ _ hwn.ne']
  have h := hcomp z ((‖z‖ / ‖u - v‖) • (u - v)) hn.ge
  rw [map_smul, hwA, smul_zero, norm_zero, mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem derivative_zero_or_injective {f : E → E} (hf : HasLocalDistortion f)
    {x : E} {A : E →L[ℝ] E} (hA : HasFDerivAt f A x) :
    A = 0 ∨ Function.Injective A := by
  obtain ⟨H, _, hlocal⟩ := hf
  obtain ⟨r, hr, hcomp⟩ := hlocal x
  exact zero_or_injective_of_norm_comparison A H (norm_derivative_comparison hr hcomp hA)

theorem image_zero_derivative_null [Nontrivial E] (f : E → E) :
    μ (f '' {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun _ => (0 : E →L[ℝ] E))
  · intro x hx
    exact hx.2 ▸ hx.1.hasFDerivAt.hasFDerivWithinAt
  · intro x _
    change LinearMap.det (0 : E →ₗ[ℝ] E) = 0
    rw [LinearMap.det_zero, zero_pow (Module.finrank_pos (R := ℝ) (M := E)).ne']

theorem image_null_of_differentiableAt {f : E → E} {s : Set E} (hs : μ s = 0)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) : μ (f '' s) = 0 :=
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (fun x hx => (hf x hx).differentiableWithinAt) hs

theorem displacement_pow_le_imageMeasure [Nontrivial E] (f : E ≃ₜ E)
    {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y z : E, dist y x ≤ dist z x →
      dist (f y) (f x) ≤ H * dist (f z) (f x))
    (x y : E) {r : ℝ} (_hr : 0 < r) (hy : dist y x ≤ r) :
    dist (f y) (f x) ^ Module.finrank ℝ E ≤
      (H ^ Module.finrank ℝ E / (μ (ball (0 : E) 1)).toReal) *
        (imageMeasure μ f (closedBall x r)).toReal := by
  have hc : 0 < (μ (ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne
  by_cases hxy : y = x
  · subst y
    rw [dist_self, zero_pow (Module.finrank_pos (R := ℝ) (M := E)).ne']
    positivity
  have hd : 0 < dist (f y) (f x) / H :=
    div_pos (dist_pos.mpr (fun h => hxy (f.injective h))) hH
  have hl : μ (ball (f x) (dist (f y) (f x) / H)) ≤
      imageMeasure μ f (closedBall x r) :=
    (image_ball_volume_lower μ f hH hxy (by linarith : dist y x < r + 1)
      (fun z _ hz => hf x y z hz)).trans
        (measure_mono (closedBall_subset_closedBall hy))
  have hreal := ENNReal.toReal_mono
    ((isCompact_closedBall x r).measure_lt_top (μ := imageMeasure μ f)).ne hl
  rw [addHaar_ball_of_pos μ _ hd, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hd.le _), div_pow] at hreal
  have hp : 0 < H ^ Module.finrank ℝ E := pow_pos hH _
  have h := (div_le_iff₀ hp).mp (show
      (dist (f y) (f x) ^ Module.finrank ℝ E * (μ (ball (0 : E) 1)).toReal) /
          H ^ Module.finrank ℝ E ≤ (imageMeasure μ f (closedBall x r)).toReal by
        simpa only [div_mul_eq_mul_div] using hreal)
  calc
    _ ≤ ((imageMeasure μ f (closedBall x r)).toReal * H ^ Module.finrank ℝ E) /
        (μ (ball (0 : E) 1)).toReal := (le_div_iff₀ hc).mpr h
    _ = _ := by ring

end DifferentialGeometry.MetricDifferentiability
