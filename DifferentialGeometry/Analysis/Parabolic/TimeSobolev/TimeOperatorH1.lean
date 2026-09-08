import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperator

noncomputable section

open MeasureTheory Filter Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {T : ℝ}

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeH1_toFunL2_eq_timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeH1 X T) (w : timeH1 Y T)
    (hw : ∀ t ∈ Icc (0 : ℝ) T, w.toFun t = A t (u.toFun t)) :
    w.toFunL2 = timeOp A hA C hC u.toFunL2 := by
  apply Lp.ext
  filter_upwards [coeFn_ofContinuousOn w.continuousOn_toFun,
    timeOp_apply_ae A hA C hC u.toFunL2,
    coeFn_ofContinuousOn u.continuousOn_toFun,
    ae_restrict_mem measurableSet_Icc] with t hwt hAt hut ht
  change w.toFunL2 t = w.toFun t at hwt
  change u.toFunL2 t = u.toFun t at hut
  rw [hwt, hAt, hut]
  exact hw t ht

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeH1_deriv_eq_timeOp_add
    (A A' : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hA' : AEStronglyMeasurable A' (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖A' t‖ ≤ (C' : ℝ))
    (u : timeH1 X T) (w : timeH1 Y T)
    (hwd : w.deriv =ᵐ[timeMeasure T]
      (fun t => A' t (u.toFun t) + A t (u.deriv t))) :
    w.deriv = timeOp A' hA' C' hC' u.toFunL2 +
      timeOp A hA C hC u.deriv := by
  apply Lp.ext
  filter_upwards [hwd,
    Lp.coeFn_add (timeOp A' hA' C' hC' u.toFunL2)
      (timeOp A hA C hC u.deriv),
    timeOp_apply_ae A' hA' C' hC' u.toFunL2,
    timeOp_apply_ae A hA C hC u.deriv,
    coeFn_ofContinuousOn u.continuousOn_toFun] with t hwt hsum hAt hAu hut
  change u.toFunL2 t = u.toFun t at hut
  rw [hwt, hsum, Pi.add_apply, hAt, hAu, hut]

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem time_coefficients_bounded
    {A : ℝ → X →L[ℝ] Y} (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) :
    AEStronglyMeasurable A (timeMeasure T) ∧
      ∃ C : NNReal, ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ) := by
  have hcont := hA.continuousOn
  have hmeas : AEStronglyMeasurable A (timeMeasure T) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let B : ℝ := max K 0
  refine ⟨hmeas, Real.toNNReal B, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hK t ht).trans (le_max_left _ _)

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem time_deriv_coefficients_bounded
    {A : ℝ → X →L[ℝ] Y} (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) :
    AEStronglyMeasurable (_root_.deriv A) (timeMeasure T) ∧
      ∃ C : NNReal, ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C : ℝ) := by
  by_cases hT : 0 < T
  · let v : ℝ → X →L[ℝ] Y := derivWithin A (Icc (0 : ℝ) T)
    have hv : ContinuousOn v (Icc (0 : ℝ) T) :=
      hA.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
    have hvd : v =ᵐ[timeMeasure T] _root_.deriv A := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    refine ⟨(hv.aestronglyMeasurable measurableSet_Icc).congr hvd, ?_⟩
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
    refine ⟨Real.toNNReal (max K 0), ?_⟩
    filter_upwards [hvd, ae_restrict_mem measurableSet_Icc] with t ht htmem
    rw [← ht, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hK t htmem).trans (le_max_left _ _)
  · rw [timeMeasure_eq_zero_of_nonpos (le_of_not_gt hT)]
    exact ⟨aestronglyMeasurable_zero_measure _, 0, by simp⟩

private def timeOpH1Aux
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hA' : AEStronglyMeasurable (_root_.deriv A) (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ)) :
    timeH1 X T →L[ℝ] timeH1 Y T :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Y (timeL2 Y T)).symm.toContinuousLinearMap.comp
    (((A 0).comp (timeH1.trace0 X T)).prod
      ((timeOp (_root_.deriv A) hA' C' hC').comp (timeH1.toTimeL2 X T) +
        (timeOp A hA C hC).comp (timeH1.timeDeriv X T)))

private theorem timeOpH1Aux_spec
    (hT : 0 ≤ T) {A : ℝ → X →L[ℝ] Y}
    (hAcont : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T))
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hA' : AEStronglyMeasurable (_root_.deriv A) (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ))
    (u : timeH1 X T) :
    (timeOpH1Aux A hA hA' C C' hC hC' u).init = A 0 u.init ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        (timeOpH1Aux A hA hA' C C' hC hC' u).toFun t = A t (u.toFun t)) ∧
      (timeOpH1Aux A hA hA' C C' hC hC' u).deriv =ᵐ[timeMeasure T]
        (fun t => _root_.deriv A t (u.toFun t) + A t (u.deriv t)) := by
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_clm_apply_of_contDiffOn hT hAcont u
  have hdeq := timeH1_deriv_eq_timeOp_add A (_root_.deriv A) hA hA' C C' hC hC' u w hwd
  have heq : timeOpH1Aux A hA hA' C C' hC hC' u = w := by
    apply timeH1.ext
    · exact hwi.symm
    · exact hdeq.symm
  rw [heq]
  exact ⟨hwi, hw, hwd⟩


def timeOpH1 (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) : timeH1 X T →L[ℝ] timeH1 Y T :=
  timeOpH1Aux A (time_coefficients_bounded hA).1 (time_deriv_coefficients_bounded hA).1
    (time_coefficients_bounded hA).2.choose (time_deriv_coefficients_bounded hA).2.choose
    (time_coefficients_bounded hA).2.choose_spec
    (time_deriv_coefficients_bounded hA).2.choose_spec

omit [CompleteSpace Y] in
@[simp] theorem timeOpH1_init (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) (u : timeH1 X T) :
    (timeOpH1 A hA u).init = A 0 u.init := rfl

theorem timeOpH1_toFun (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) (u : timeH1 X T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (timeOpH1 A hA u).toFun t = A t (u.toFun t) := by
  exact (timeOpH1Aux_spec (ht.1.trans ht.2) hA
    (time_coefficients_bounded hA).1 (time_deriv_coefficients_bounded hA).1
    (time_coefficients_bounded hA).2.choose (time_deriv_coefficients_bounded hA).2.choose
    (time_coefficients_bounded hA).2.choose_spec
    (time_deriv_coefficients_bounded hA).2.choose_spec u).2.1 t ht

omit [CompleteSpace Y] in
theorem timeOpH1_deriv_ae (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T)) (u : timeH1 X T) :
    (timeOpH1 A hA u).deriv =ᵐ[timeMeasure T]
      (fun t => _root_.deriv A t (u.toFun t) + A t (u.deriv t)) := by
  let hAm := (time_coefficients_bounded hA).1
  let hA'm := (time_deriv_coefficients_bounded hA).1
  let C := (time_coefficients_bounded hA).2.choose
  let C' := (time_deriv_coefficients_bounded hA).2.choose
  let hC := (time_coefficients_bounded hA).2.choose_spec
  let hC' := (time_deriv_coefficients_bounded hA).2.choose_spec
  change (timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2 +
    timeOp A hAm C hC u.deriv : timeL2 Y T) =ᵐ[timeMeasure T] _
  filter_upwards [Lp.coeFn_add (timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2)
      (timeOp A hAm C hC u.deriv),
    timeOp_apply_ae (_root_.deriv A) hA'm C' hC' u.toFunL2,
    timeOp_apply_ae A hAm C hC u.deriv,
    coeFn_ofContinuousOn u.continuousOn_toFun] with t hsum hA't hAt hut
  change u.toFunL2 t = u.toFun t at hut
  rw [hsum, Pi.add_apply, hA't, hAt, hut]

theorem toTimeL2_comp_timeOpH1 (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T))
    (hAm : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    (timeH1.toTimeL2 Y T).comp (timeOpH1 A hA) =
      (timeOp A hAm C hC).comp (timeH1.toTimeL2 X T) := by
  apply ContinuousLinearMap.ext
  intro u
  exact timeH1_toFunL2_eq_timeOp A hAm C hC u (timeOpH1 A hA u)
    (fun _ ht => timeOpH1_toFun A hA u ht)

omit [CompleteSpace Y] in
theorem timeDeriv_comp_timeOpH1 (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T))
    (hAm : AEStronglyMeasurable A (timeMeasure T))
    (hA'm : AEStronglyMeasurable (_root_.deriv A) (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ)) :
    (timeH1.timeDeriv Y T).comp (timeOpH1 A hA) =
      (timeOp (_root_.deriv A) hA'm C' hC').comp (timeH1.toTimeL2 X T) +
        (timeOp A hAm C hC).comp (timeH1.timeDeriv X T) := by
  apply ContinuousLinearMap.ext
  intro u
  exact timeH1_deriv_eq_timeOp_add A (_root_.deriv A) hAm hA'm C C' hC hC'
    u (timeOpH1 A hA u) (timeOpH1_deriv_ae A hA u)

omit [CompleteSpace Y] in
theorem timeOpH1_norm_le (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ)) :
    ‖timeOpH1 A hA‖ ≤ ‖A 0‖ + (C' : ℝ) * Real.sqrt T * (1 + Real.sqrt T) + C := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro u
  let w := timeOpH1 A hA u
  have hwi : ‖w.init‖ ≤ ‖A 0‖ * ‖u‖ := by
    rw [show w.init = A 0 u.init from timeOpH1_init A hA u]
    exact ((A 0).le_opNorm u.init).trans
      (mul_le_mul_of_nonneg_left u.norm_init_le (norm_nonneg _))
  have hAm := (time_coefficients_bounded hA).1
  have hA'm := (time_deriv_coefficients_bounded hA).1
  have hwd : w.deriv = timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2 +
      timeOp A hAm C hC u.deriv :=
    timeH1_deriv_eq_timeOp_add A (_root_.deriv A) hAm hA'm C C' hC hC'
      u w (timeOpH1_deriv_ae A hA u)
  have hnorm (B : ℝ → X →L[ℝ] Y) (hBm : AEStronglyMeasurable B (timeMeasure T))
      (D : NNReal) (hD : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (D : ℝ)) (v : timeL2 X T) :
      ‖timeOp B hBm D hD v‖ ≤ (D : ℝ) * ‖v‖ :=
    ((timeOp B hBm D hD).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (timeOp_norm_le B hBm D hD) (norm_nonneg _))
  have hwdnorm : ‖w.deriv‖ ≤
      ((C' : ℝ) * Real.sqrt T * (1 + Real.sqrt T) + C) * ‖u‖ := by
    rw [hwd]
    calc
      ‖timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2 + timeOp A hAm C hC u.deriv‖ ≤
          (C' : ℝ) * ‖u.toFunL2‖ + (C : ℝ) * ‖u.deriv‖ :=
        (norm_add_le _ _).trans (add_le_add (hnorm _ _ _ _ _) (hnorm _ _ _ _ _))
      _ ≤ (C' : ℝ) * (Real.sqrt T * ((1 + Real.sqrt T) * ‖u‖)) + C * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left u.norm_toFunL2_le C'.coe_nonneg)
          (mul_le_mul_of_nonneg_left u.norm_deriv_le C.coe_nonneg)
      _ = _ := by ring
  have hnormsum : ‖w‖ ≤ ‖w.init‖ + ‖w.deriv‖ := by
    have hsq := w.norm_sq_eq
    nlinarith [norm_nonneg w, norm_nonneg w.init, norm_nonneg w.deriv,
      mul_nonneg (norm_nonneg w.init) (norm_nonneg w.deriv)]
  exact hnormsum.trans ((add_le_add hwi hwdnorm).trans_eq (by ring))

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
