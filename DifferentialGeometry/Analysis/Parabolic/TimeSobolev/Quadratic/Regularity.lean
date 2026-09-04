import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.EulerLagrange
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.WeakDerivative.FundamentalTheorem

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]
variable {T : ℝ}

theorem mom_primitive
    (hT : 0 < T)
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeH1 X T) (F : timeL2 X T)
    (hEuler : ∀ v : timeH1 X T, v.init = 0 → v.toFun T = 0 →
      2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
        inner ℝ F v.toFunL2 = 0) :
    ∃ c : X, (fun t ↦ (2 : ℝ) • A t (u.deriv t))
      =ᵐ[volume.restrict (Ioo (0 : ℝ) T)]
        fun t ↦ c + ∫ r in (0 : ℝ)..t, F r := by
  let L : timeL2 X T := timeOp A hA C hC u.deriv
  have hL : L =ᵐ[timeMeasure T] fun t ↦ A t (u.deriv t) := by
    simpa only [L] using timeOp_apply_ae A hA C hC u.deriv
  have hp_mem : MemLp (fun t ↦ (2 : ℝ) • A t (u.deriv t)) 2 (timeMeasure T) := by
    have h2L : ((2 : ℝ) • L : timeL2 X T) =ᵐ[timeMeasure T]
        fun t ↦ (2 : ℝ) • A t (u.deriv t) := by
      filter_upwards [Lp.coeFn_smul (2 : ℝ) L, hL] with t hsmul hLt
      rw [hsmul, Pi.smul_apply, hLt]
    exact (Lp.memLp ((2 : ℝ) • L)).ae_eq h2L
  have hp : IntegrableOn (fun t ↦ (2 : ℝ) • A t (u.deriv t))
      (Ioo (0 : ℝ) T) volume := by
    have hpIcc : IntegrableOn (fun t ↦ (2 : ℝ) • A t (u.deriv t))
        (Icc (0 : ℝ) T) volume := hp_mem.integrable (by norm_num)
    exact hpIcc.congr_set_ae Ioo_ae_eq_Icc
  have hF : IntegrableOn (fun t ↦ F t) (Ioo (0 : ℝ) T) volume := by
    have hFIcc : IntegrableOn (fun t ↦ F t) (Icc (0 : ℝ) T) volume :=
      (Lp.memLp F).integrable (by norm_num)
    exact hFIcc.congr_set_ae Ioo_ae_eq_Icc
  apply weakDeriv_primitive hT hp hF
  intro φ hφ hφ_comp hφ_supp
  have hφ0 : φ 0 = 0 := by
    by_contra hne
    have hmem : (0 : ℝ) ∈ tsupport φ := subset_tsupport φ hne
    exact (lt_irrefl (0 : ℝ)) (hφ_supp hmem).1
  have hφT : φ T = 0 := by
    by_contra hne
    have hmem : T ∈ tsupport φ := subset_tsupport φ hne
    exact (lt_irrefl T) (hφ_supp hmem).2
  apply ext_inner_right ℝ
  intro x
  let fx : ℝ → X := fun t ↦ φ t • x
  have hfx : ContDiff ℝ 1 fx :=
    (hφ.of_le (by norm_num)).smul contDiff_const
  let v : timeH1 X T := timeH1.ofContDiffOn hT.le fx hfx.contDiffOn
  have hv0 : v.init = 0 := by
    change fx 0 = 0
    simp only [fx, hφ0, zero_smul]
  have hvT : v.toFun T = 0 := by
    rw [timeH1.toFun_ofContDiffOn hT.le fx hfx.contDiffOn ⟨hT.le, le_rfl⟩]
    simp only [fx, hφT, zero_smul]
  have he := hEuler v hv0 hvT
  have hv_deriv : v.deriv =ᵐ[timeMeasure T] fun t ↦ deriv φ t • x := by
    have hφdiff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    filter_upwards [timeH1.deriv_ofContDiffOn hT.le fx hfx.contDiffOn] with t ht
    rw [ht]
    exact deriv_smul_const hφdiff.differentiableAt x
  have hv_fun : v.toFunL2 =ᵐ[timeMeasure T] fun t ↦ φ t • x := by
    filter_upwards [TimeSobolev.coeFn_ofContinuousOn v.continuousOn_toFun,
      ae_restrict_mem measurableSet_Icc] with t ht htmem
    exact ht.trans (timeH1.toFun_ofContDiffOn hT.le fx hfx.contDiffOn htmem)
  rw [TimeSobolev.inner_def, TimeSobolev.inner_def] at he
  have hscalar :
      (∫ t in Ioo (0 : ℝ) T,
          inner ℝ ((deriv φ t) • ((2 : ℝ) • A t (u.deriv t))) x) =
        -(∫ t in Ioo (0 : ℝ) T, inner ℝ ((φ t) • F t) x) := by
    have hkin :
        (∫ t in Icc (0 : ℝ) T, inner ℝ (L t) (v.deriv t)) =
          ∫ t in Ioo (0 : ℝ) T,
            deriv φ t * inner ℝ (A t (u.deriv t)) x := by
      rw [show (∫ t in Icc (0 : ℝ) T, inner ℝ (L t) (v.deriv t)) =
          ∫ t in Ioo (0 : ℝ) T, inner ℝ (L t) (v.deriv t) by
        rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]]
      apply MeasureTheory.integral_congr_ae
      have hL' : L =ᵐ[volume.restrict (Ioo (0 : ℝ) T)]
          fun t ↦ A t (u.deriv t) := by
        simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc]
          using hL
      have hv' : v.deriv =ᵐ[volume.restrict (Ioo (0 : ℝ) T)]
          fun t ↦ deriv φ t • x := by
        simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc]
          using hv_deriv
      filter_upwards [hL', hv'] with t hLt hvt
      rw [hLt, hvt, real_inner_smul_right]
    have hpot :
        (∫ t in Icc (0 : ℝ) T, inner ℝ (F t) (v.toFunL2 t)) =
          ∫ t in Ioo (0 : ℝ) T, φ t * inner ℝ (F t) x := by
      rw [show (∫ t in Icc (0 : ℝ) T, inner ℝ (F t) (v.toFunL2 t)) =
          ∫ t in Ioo (0 : ℝ) T, inner ℝ (F t) (v.toFunL2 t) by
        rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]]
      apply MeasureTheory.integral_congr_ae
      have hv' : v.toFunL2 =ᵐ[volume.restrict (Ioo (0 : ℝ) T)]
          fun t ↦ φ t • x := by
        simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc]
          using hv_fun
      filter_upwards [hv'] with t hvt
      rw [hvt, real_inner_smul_right]
    change 2 * (∫ t in Icc (0 : ℝ) T, inner ℝ (L t) (v.deriv t)) +
      (∫ t in Icc (0 : ℝ) T, inner ℝ (F t) (v.toFunL2 t)) = 0 at he
    rw [hkin, hpot] at he
    calc
      (∫ t in Ioo (0 : ℝ) T,
          inner ℝ ((deriv φ t) • ((2 : ℝ) • A t (u.deriv t))) x)
          = 2 * ∫ t in Ioo (0 : ℝ) T,
              deriv φ t * inner ℝ (A t (u.deriv t)) x := by
              rw [← MeasureTheory.integral_const_mul]
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with t
              simp only [smul_smul, real_inner_smul_left]
              ring
      _ = -(∫ t in Ioo (0 : ℝ) T, φ t * inner ℝ (F t) x) := by linarith
      _ = -(∫ t in Ioo (0 : ℝ) T, inner ℝ ((φ t) • F t) x) := by
            congr 1
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with t
            rw [real_inner_smul_left]
  have hleft : inner ℝ (∫ t in Ioo (0 : ℝ) T,
      deriv φ t • ((2 : ℝ) • A t (u.deriv t))) x =
      ∫ t in Ioo (0 : ℝ) T,
        inner ℝ (deriv φ t • ((2 : ℝ) • A t (u.deriv t))) x := by
    have hpφ : Integrable (fun t ↦ deriv φ t • ((2 : ℝ) • A t (u.deriv t)))
        (volume.restrict (Ioo (0 : ℝ) T)) :=
      (show Integrable (fun t ↦ (2 : ℝ) • A t (u.deriv t))
          (volume.restrict (Ioo (0 : ℝ) T)) from hp).locallyIntegrable
        |>.integrable_smul_left_of_hasCompactSupport
          (hφ.continuous_deriv (by norm_cast)) hφ_comp.deriv
    calc
      inner ℝ (∫ t in Ioo (0 : ℝ) T,
          deriv φ t • ((2 : ℝ) • A t (u.deriv t))) x =
          inner ℝ x (∫ t in Ioo (0 : ℝ) T,
            deriv φ t • ((2 : ℝ) • A t (u.deriv t))) := real_inner_comm _ _
      _ = ∫ t in Ioo (0 : ℝ) T,
          inner ℝ x (deriv φ t • ((2 : ℝ) • A t (u.deriv t))) :=
            ((innerSL ℝ x).integral_comp_comm hpφ).symm
      _ = ∫ t in Ioo (0 : ℝ) T,
          inner ℝ (deriv φ t • ((2 : ℝ) • A t (u.deriv t))) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with t
            exact real_inner_comm _ _
  have hright : inner ℝ (-∫ t in Ioo (0 : ℝ) T, φ t • F t) x =
      -(∫ t in Ioo (0 : ℝ) T, inner ℝ ((φ t) • F t) x) := by
    have hFφ : Integrable (fun t ↦ φ t • F t)
        (volume.restrict (Ioo (0 : ℝ) T)) :=
      (show Integrable (fun t ↦ F t) (volume.restrict (Ioo (0 : ℝ) T)) from hF)
        |>.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hφ.continuous hφ_comp
    rw [inner_neg_left]
    congr 1
    calc
      inner ℝ (∫ t in Ioo (0 : ℝ) T, φ t • F t) x =
          inner ℝ x (∫ t in Ioo (0 : ℝ) T, φ t • F t) := real_inner_comm _ _
      _ = ∫ t in Ioo (0 : ℝ) T, inner ℝ x (φ t • F t) :=
        ((innerSL ℝ x).integral_comp_comm hFφ).symm
      _ = ∫ t in Ioo (0 : ℝ) T, inner ℝ (φ t • F t) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        exact real_inner_comm _ _
  rw [hleft, hright]
  exact hscalar

theorem mom_rep_cont
    (hT : 0 < T)
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeH1 X T) (F : timeL2 X T)
    (hEuler : ∀ v : timeH1 X T, v.init = 0 → v.toFun T = 0 →
      2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
        inner ℝ F v.toFunL2 = 0) :
    ∃ c : X,
      ((fun t ↦ (2 : ℝ) • A t (u.deriv t))
        =ᵐ[volume.restrict (Ioo (0 : ℝ) T)]
          fun t ↦ c + ∫ r in (0 : ℝ)..t, F r) ∧
      ContinuousOn (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (Icc (0 : ℝ) T) := by
  obtain ⟨c, hc⟩ := mom_primitive hT A hA C hC u F hEuler
  refine ⟨c, hc, continuousOn_const.add ?_⟩
  have hFIcc : IntegrableOn (fun t ↦ F t) (Icc (0 : ℝ) T) volume :=
    (Lp.memLp F).integrable (by norm_num)
  have hcont := continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
    (f := fun t ↦ F t) (μ := volume) (by
      rw [uIcc_of_le hT.le]
      exact hFIcc)
  rwa [uIcc_of_le hT.le] at hcont

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
