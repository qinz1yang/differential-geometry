import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Energy
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem absolutelyContinuousOnInterval_clm_apply
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : ℝ → X →L[ℝ] Y} {u : ℝ → X} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => A t (u t)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hu.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hu ⊢
  apply squeeze_zero' ?_ ?_
    (by simpa using (hu.const_mul C).add (hA.const_mul D))
  · exact Filter.Eventually.of_forall <| fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hleft : (I i).1 ∈ uIcc a b := (hnI.left i hi).1
  have hright : (I i).2 ∈ uIcc a b := (hnI.left i hi).2
  calc
    dist (A (I i).1 (u (I i).1)) (A (I i).2 (u (I i).2)) ≤
        dist (A (I i).1 (u (I i).1)) (A (I i).1 (u (I i).2)) +
        dist (A (I i).1 (u (I i).2)) (A (I i).2 (u (I i).2)) := dist_triangle _ _ _
    _ ≤ C * dist (u (I i).1) (u (I i).2) +
        D * dist (A (I i).1) (A (I i).2) := by
      apply add_le_add
      · rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact ((A (I i).1).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC _ hleft) (norm_nonneg _))
      · rw [dist_eq_norm, dist_eq_norm, ← sub_apply]
        exact ((A (I i).1 - A (I i).2).le_opNorm _).trans
          (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hD _ hright) (norm_nonneg _))

private theorem absolutelyContinuousOnInterval_comp_clm
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {u : ℝ → X} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => L (u t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hu ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using hu.const_mul ‖L‖)
  · exact Filter.Eventually.of_forall <| fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)
  filter_upwards with p
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact L.le_opNorm _

private theorem memLp_clm_apply_of_bound_right
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : ℝ → X →L[ℝ] Y} {u : ℝ → X} {μ : Measure ℝ}
    {C : ℝ} (hA : MemLp A 2 μ) (hu : AEStronglyMeasurable u μ)
    (hb : ∀ᵐ t ∂μ, ‖u t‖ ≤ C) : MemLp (fun t => A t (u t)) 2 μ := by
  refine MemLp.of_le_mul (c := C) hA
    ((ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂ hu hA.1) ?_
  filter_upwards [hb] with t ht
  exact ((A t).le_opNorm _).trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _))

private theorem memLp_clm_apply_of_bound_left
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : ℝ → X →L[ℝ] Y} {u : ℝ → X} {μ : Measure ℝ}
    {C : ℝ} (hA : AEStronglyMeasurable A μ) (hu : MemLp u 2 μ)
    (hb : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) : MemLp (fun t => A t (u t)) 2 μ := by
  refine MemLp.of_le_mul (c := C) hu
    ((ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂ hu.1 hA) ?_
  filter_upwards [hb] with t ht
  exact ((A t).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {T : ℝ}

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem memLp_timeH1_clm_apply_derivative
    (A : timeH1 (X →L[ℝ] Y) T) (u : timeH1 X T) :
    MemLp (fun t => A.deriv t (u.toFun t) + A.toFun t (u.deriv t)) 2 (timeMeasure T) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn u.continuousOn_toFun
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn A.continuousOn_toFun
  have hum : AEStronglyMeasurable u.toFun (timeMeasure T) :=
    u.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc
  have hAm : AEStronglyMeasurable A.toFun (timeMeasure T) :=
    A.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc
  have h1 : MemLp (fun t => A.deriv t (u.toFun t)) 2 (timeMeasure T) :=
    memLp_clm_apply_of_bound_right (Lp.memLp A.deriv) hum
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hC t ht)
  have h2 : MemLp (fun t => A.toFun t (u.deriv t)) 2 (timeMeasure T) :=
    memLp_clm_apply_of_bound_left hAm (Lp.memLp u.deriv)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hD t ht)
  exact h1.add h2

private theorem integral_timeH1_clm_apply_derivative
    (A : timeH1 (X →L[ℝ] Y) T) (u : timeH1 X T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, A.deriv s (u.toFun s) + A.toFun s (u.deriv s)) =
      A.toFun t (u.toFun t) - A.initial u.initial := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hsub : uIcc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht
  have hAu := absolutelyContinuousOnInterval_clm_apply
    (A.absolutelyContinuousOnInterval_toFun (ht.1.trans ht.2))
    (u.absolutelyContinuousOnInterval_toFun (ht.1.trans ht.2))
  have hAC := (absolutelyContinuousOnInterval_comp_clm L hAu).mono
    (by simpa only [uIcc_of_le (ht.1.trans ht.2)] using hsub)
  have hid := hAC.integral_deriv_eq_sub
  have hder : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) t →
      _root_.deriv (fun r => L (A.toFun r (u.toFun r))) s =
        L (A.deriv s (u.toFun s) + A.toFun s (u.deriv s)) := by
    have hA := (ae_restrict_iff' measurableSet_Icc).mp A.ae_hasDerivWithinAt_toFun
    have hu := (ae_restrict_iff' measurableSet_Icc).mp u.ae_hasDerivWithinAt_toFun
    filter_upwards [hA, hu, Measure.ae_ne volume 0, Measure.ae_ne volume T]
      with s hAs hus hs0 hsT hst
    have hsI := hsub (uIoc_subset_uIcc hst)
    have hsN : Icc (0 : ℝ) T ∈ 𝓝 s := Icc_mem_nhds
      (lt_of_le_of_ne hsI.1 hs0.symm) (lt_of_le_of_ne hsI.2 hsT)
    have hd := ((hAs hsI).hasDerivAt hsN).clm_apply ((hus hsI).hasDerivAt hsN)
    exact (L.hasFDerivAt.comp_hasDerivAt s hd).deriv
  rw [intervalIntegral.integral_congr_ae hder, timeH1.toFun_zero, timeH1.toFun_zero] at hid
  have hqi : IntegrableOn (fun s => A.deriv s (u.toFun s) + A.toFun s (u.deriv s))
      (Icc (0 : ℝ) T) volume :=
    (memLp_timeH1_clm_apply_derivative A u).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [← L.intervalIntegral_comp_comm (hqi.mono_set hsub).intervalIntegrable]
  simpa only [map_sub] using hid

theorem exists_timeH1_clm_apply
    (A : timeH1 (X →L[ℝ] Y) T) (u : timeH1 X T) :
    ∃ w : timeH1 Y T,
      w.initial = A.initial u.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = A.toFun t (u.toFun t)) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => A.deriv t (u.toFun t) + A.toFun t (u.deriv t)) := by
  let q := fun t => A.deriv t (u.toFun t) + A.toFun t (u.deriv t)
  have hq : MemLp q 2 (timeMeasure T) := memLp_timeH1_clm_apply_derivative A u
  let w := timeH1.mk (A.initial u.initial) (hq.toLp q)
  have hwd : w.deriv =ᵐ[timeMeasure T] q := hq.coeFn_toLp
  refine ⟨w, rfl, ?_, hwd⟩
  intro t ht
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hi : (∫ s in (0 : ℝ)..t, w.deriv s) = ∫ s in (0 : ℝ)..t, q s :=
    intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict
      (hwd.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))
  rw [timeH1.toFun_apply, hi, integral_timeH1_clm_apply_derivative A u ht]
  change A.initial u.initial + (A.toFun t (u.toFun t) - A.initial u.initial) = _
  abel

theorem exists_timeH1_clm_apply_of_contDiffOn
    (hT : 0 ≤ T) {A : ℝ → X →L[ℝ] Y}
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) (u : timeH1 X T) :
    ∃ w : timeH1 Y T,
      w.initial = A 0 u.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = A t (u.toFun t)) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => _root_.deriv A t (u.toFun t) + A t (u.deriv t)) := by
  let v := timeH1.ofContDiffOn hT A hA
  have hv : ∀ t ∈ Icc (0 : ℝ) T, v.toFun t = A t := timeH1.toFun_ofContDiffOn hT A hA
  have hvd : v.deriv =ᵐ[timeMeasure T] _root_.deriv A := timeH1.deriv_ofContDiffOn hT A hA
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_clm_apply v u
  refine ⟨w, hwi, ?_, ?_⟩
  · intro t ht
    rw [hw t ht, hv t ht]
  · filter_upwards [hwd, hvd, ae_restrict_mem measurableSet_Icc] with t hwt hvdt ht
    rw [hwt, hvdt, hv t ht]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev


namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem exists_timeH1_comp_clm
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {T : ℝ}
    (L : X →L[ℝ] Y) (u : timeH1 X T) :
    ∃ v : timeH1 Y T,
      v.initial = L u.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T, v.toFun t = L (u.toFun t)) ∧
      v.deriv =ᵐ[timeMeasure T] (fun t => L (u.deriv t)) := by
  let v := timeH1.mk (L u.initial) (L.compLpL 2 (timeMeasure T) u.deriv)
  have hd : v.deriv =ᵐ[timeMeasure T] (fun t => L (u.deriv t)) := L.coeFn_compLpL u.deriv
  refine ⟨v, rfl, ?_, hd⟩
  intro t ht
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hi : (∫ s in (0 : ℝ)..t, v.deriv s) = ∫ s in (0 : ℝ)..t, L (u.deriv s) :=
    intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict
      (hd.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))
  rw [timeH1.toFun_apply, hi, L.intervalIntegral_comp_comm
    (u.intervalIntegrable_deriv ⟨le_rfl, ht.1.trans ht.2⟩ ht), timeH1.toFun_apply, map_add]
  rfl

theorem exists_timeH1_bilin
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] {T : ℝ}
    (B : X →L[ℝ] Y →L[ℝ] Z) (u : timeH1 X T) (v : timeH1 Y T) :
    ∃ w : timeH1 Z T,
      w.initial = B u.initial v.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = B (u.toFun t) (v.toFun t)) ∧
      w.deriv =ᵐ[timeMeasure T]
        (fun t => B (u.deriv t) (v.toFun t) + B (u.toFun t) (v.deriv t)) := by
  obtain ⟨A, hAi, hA, hAd⟩ := exists_timeH1_comp_clm B u
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_clm_apply A v
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [hwi, hAi]
  · intro t ht
    rw [hw t ht, hA t ht]
  · filter_upwards [hwd, hAd, ae_restrict_mem measurableSet_Icc] with t hwt hAt ht
    rw [hwt, hAt, hA t ht]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {T : ℝ}

theorem exists_timeH1_smul (z : timeH1 ℝ T) (u : timeH1 X T) :
    ∃ w : timeH1 X T,
      w.initial = z.initial • u.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = z.toFun t • u.toFun t) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => z.deriv t • u.toFun t + z.toFun t • u.deriv t) := by
  simpa only [ContinuousLinearMap.lsmul_apply] using
    exists_timeH1_bilin (ContinuousLinearMap.lsmul ℝ ℝ) z u

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end

section
noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem exists_timeH1_strongPair_comp
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (P L : X →L[ℝ] Y) (P' L' : X →L[ℝ] Z) (R : Y →L[ℝ] Z)
    (hP : ∀ x, R (P x) = P' x) (hL : ∀ x, R (L x) = L' x)
    {T : ℝ} (u : timeH1 Y T) (field : timeL2 X T) (force : timeL2 Y T)
    (hzero : timeH1.trace0 Y T u = 0)
    (hlink : P.compLpL 2 (timeMeasure T) field = u.toFunL2)
    (hpde : timeH1.timeDeriv Y T u = L.compLpL 2 (timeMeasure T) field + force) :
    ∃ v : timeH1 Z T, timeH1.trace0 Z T v = 0 ∧
      EqOn v.toFun (fun t => R (u.toFun t)) (Icc 0 T) ∧
      P'.compLpL 2 (timeMeasure T) field = v.toFunL2 ∧
      timeH1.timeDeriv Z T v = L'.compLpL 2 (timeMeasure T) field +
        R.compLpL 2 (timeMeasure T) force := by
  obtain ⟨v, hv0, hvt, hvd⟩ := exists_timeH1_comp_clm R u
  refine ⟨v, ?_, fun t ht => hvt t ht, ?_, ?_⟩
  · change v.initial = 0
    rw [hv0, show u.initial = 0 from hzero, map_zero]
  · apply Lp.ext
    filter_upwards [P'.coeFn_compLpL field, P.coeFn_compLpL field,
      coeFn_ofContinuousOn u.continuousOn_toFun,
      coeFn_ofContinuousOn v.continuousOn_toFun,
      ae_restrict_mem measurableSet_Icc] with t hP' htP hu hv ht
    change u.toFunL2 t = u.toFun t at hu
    change v.toFunL2 t = v.toFun t at hv
    rw [hP', hv, hvt t ht, ← hu, ← hlink, htP, hP]
  · change v.deriv = _
    apply Lp.ext
    filter_upwards [hvd, L.coeFn_compLpL field, L'.coeFn_compLpL field,
      R.coeFn_compLpL force,
      Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) force,
      Lp.coeFn_add (L'.compLpL 2 (timeMeasure T) field)
        (R.compLpL 2 (timeMeasure T) force)] with t hd hLt hL't hRt hsum hsum'
    change u.deriv = _ at hpde
    rw [hd, hpde, hsum, hsum']
    simp only [Pi.add_apply, map_add, hLt, hL, hL't, hRt]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
end
