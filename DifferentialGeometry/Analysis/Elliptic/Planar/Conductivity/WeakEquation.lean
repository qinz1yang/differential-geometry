import DifferentialGeometry.Analysis.Elliptic.Planar.CoordinateChange
import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem planar_flux_divergence
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) {w : ℂ → ℝ} {x : ℂ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hw : ContDiffAt ℝ 2 w x) :
    (∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2,
      A y i j * fderiv ℝ w y ((![1, Complex.I] : Fin 2 → ℂ) j)) x
        ((![1, Complex.I] : Fin 2 → ℂ) i)) =
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j * fderiv ℝ (fderiv ℝ w) x
        ((![1, Complex.I] : Fin 2 → ℂ) i) ((![1, Complex.I] : Fin 2 → ℂ) j)) +
      ∑ j : Fin 2, (∑ i : Fin 2, fderiv ℝ (fun y => A y i j) x
        ((![1, Complex.I] : Fin 2 → ℂ) i)) *
          fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ w) x :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG (j : Fin 2) : DifferentiableAt ℝ
      (fun y => fderiv ℝ w y ((![1, Complex.I] : Fin 2 → ℂ) j)) x :=
    hD.clm_apply (differentiableAt_const _)
  have hflux (i : Fin 2) :
      fderiv ℝ (fun y => ∑ j : Fin 2,
        A y i j * fderiv ℝ w y ((![1, Complex.I] : Fin 2 → ℂ) j)) x
          ((![1, Complex.I] : Fin 2 → ℂ) i) =
        ∑ j : Fin 2, (fderiv ℝ (fun y => A y i j) x
          ((![1, Complex.I] : Fin 2 → ℂ) i) *
            fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j) +
          A x i j * fderiv ℝ (fderiv ℝ w) x
            ((![1, Complex.I] : Fin 2 → ℂ) i) ((![1, Complex.I] : Fin 2 → ℂ) j)) := by
    rw [fderiv_fun_sum (fun j _ => (hA i j).fun_mul (hG j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hG j),
      fderiv_clm_apply hD (differentiableAt_const _)]
    simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
    ring
  simp_rw [hflux]
  simp only [Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun i j =>
    fderiv ℝ (fun y => A y i j) x ((![1, Complex.I] : Fin 2 → ℂ) i) *
      fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j))]
  ring

/-- The literal planar nondivergence operator equals the divergence of its
conductivity flux plus the original drift minus the column divergence of `A`.
Only the principal coefficients and the scalar are differentiated. -/
theorem planarScalarOperator_eq_divergenceForm
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
    {w : ℂ → ℝ} {x : ℂ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hw : ContDiffAt ℝ 2 w x) :
    planarScalarOperator A beta c w x =
      (∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2,
        A y i j * fderiv ℝ w y ((![1, Complex.I] : Fin 2 → ℂ) j)) x
          ((![1, Complex.I] : Fin 2 → ℂ) i)) +
      (∑ j : Fin 2, (beta x j - ∑ i : Fin 2,
        fderiv ℝ (fun y => A y i j) x ((![1, Complex.I] : Fin 2 → ℂ) i)) *
          fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j)) + c x * w x := by
  rw [planar_flux_divergence A hA hw]
  simp only [planarScalarOperator, sub_mul, Finset.sum_sub_distrib]
  ring

/-- A classical equation with `C¹` principal coefficients and the same `C²`
scalar has the exact conductivity weak form against compactly supported `C¹`
tests. The lower coefficients need no regularity for this implication: the
combined right side equals the continuous negative flux divergence on `Ω`. -/
theorem planarScalarOperator_zero_weak_divergence
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
    {w : ℂ → ℝ} (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A x i j) Ω)
    (hw : ContDiffOn ℝ 2 w Ω)
    (hpde : ∀ x ∈ Ω, planarScalarOperator A beta c w x = 0)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, ∑ i : Fin 2, (∑ j : Fin 2,
      A x i j * fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j)) *
        fderiv ℝ φ x ((![1, Complex.I] : Fin 2 → ℂ) i)) =
      ∫ x in Ω, ((∑ j : Fin 2, (beta x j - ∑ i : Fin 2,
        fderiv ℝ (fun y => A y i j) x ((![1, Complex.I] : Fin 2 → ℂ) i)) *
          fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j)) + c x * w x) * φ x := by
  let F (i : Fin 2) (x : ℂ) := ∑ j : Fin 2,
    A x i j * fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j)
  have hF (i : Fin 2) : ContDiffOn ℝ 1 (F i) Ω := by
    apply ContDiffOn.sum
    intro j _
    exact (hA i j).mul
      ((hw.fderiv_of_isOpen (m := 1) hΩ (by norm_num)).clm_apply contDiffOn_const)
  have hI (i : Fin 2) : Integrable (fun x =>
      F i x * fderiv ℝ φ x ((![1, Complex.I] : Fin 2 → ℂ) i)) (volume.restrict Ω) := by
    have hdφ : Continuous (fun x =>
        fderiv ℝ φ x ((![1, Complex.I] : Fin 2 → ℂ) i)) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdφs : tsupport (fun x => fderiv ℝ φ x ((![1, Complex.I] : Fin 2 → ℂ) i)) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ _).trans hφs
    exact (((hF i).continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hdφs)).integrable_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) _).mul_left |>.restrict
  have hD (i : Fin 2) : Integrable (fun x =>
      fderiv ℝ (F i) x ((![1, Complex.I] : Fin 2 → ℂ) i) * φ x) (volume.restrict Ω) := by
    have hdc := ((hF i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
      (continuousOn_const (c := ((![1, Complex.I] : Fin 2 → ℂ) i)))
    exact ((hdc.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
        |>.restrict
  have hweak : (∫ x in Ω, ∑ i : Fin 2,
      F i x * fderiv ℝ φ x ((![1, Complex.I] : Fin 2 → ℂ) i)) =
      -∫ x in Ω, (∑ i : Fin 2,
        fderiv ℝ (F i) x ((![1, Complex.I] : Fin 2 → ℂ) i)) * φ x := by
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn hΩ (hF _)
      hφ hφc hφs]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hD i)]
    simp only [Finset.sum_mul]
  change (∫ x in Ω, ∑ i : Fin 2,
    F i x * fderiv ℝ φ x ((![1, Complex.I] : Fin 2 → ℂ) i)) = _
  rw [hweak, ← integral_neg]
  apply setIntegral_congr_fun hΩ.measurableSet
  intro x hx
  have he := planarScalarOperator_eq_divergenceForm A beta c
    (fun i j => ((hA i j).contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero)
    (hw.contDiffAt (hΩ.mem_nhds hx))
  rw [hpde x hx] at he
  change 0 = (∑ i : Fin 2,
    fderiv ℝ (F i) x ((![1, Complex.I] : Fin 2 → ℂ) i)) + _ + _ at he
  nlinarith only [congrArg (fun t : ℝ => t * φ x) he]

end DifferentialGeometry.Analysis
