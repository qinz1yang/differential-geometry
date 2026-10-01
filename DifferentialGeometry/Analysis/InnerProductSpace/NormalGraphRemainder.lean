import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators ContDiff

namespace DifferentialGeometry.Analysis
section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem norm_fderiv_normal_graph_remainder_le
    (g : E → F) (t : E) (v : F)
    (hg : DifferentiableAt ℝ g t)
    (hdg : DifferentiableAt ℝ (fderiv ℝ g) t) :
    ‖fderiv ℝ (fun s => (ContinuousLinearMap.adjoint (fderiv ℝ g s)) (g s - v)) t‖ ≤
      ‖fderiv ℝ g t‖ ^ 2 + ‖fderiv ℝ (fderiv ℝ g) t‖ * ‖g t - v‖ := by
  let J : (E →L[ℝ] F) →L[ℝ] F →L[ℝ] E :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hJnorm (A : E →L[ℝ] F) : ‖J A‖ = ‖A‖ :=
    ContinuousLinearMap.adjoint.norm_map A
  have hc := (J.hasFDerivAt.comp t hdg.hasFDerivAt).clm_apply
    (hg.hasFDerivAt.sub_const v)
  change ‖fderiv ℝ (fun y => ((J : (E →L[ℝ] F) → F →L[ℝ] E) ∘ fderiv ℝ g) y
    (g y - v)) t‖ ≤ _
  rw [hc.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change ‖J (fderiv ℝ g t) ((fderiv ℝ g t) w) +
    J ((fderiv ℝ (fderiv ℝ g) t) w) (g t - v)‖ ≤ _
  have hfirst : ‖J (fderiv ℝ g t) ((fderiv ℝ g t) w)‖ ≤
      ‖fderiv ℝ g t‖ ^ 2 * ‖w‖ := by
    calc
      _ ≤ ‖J (fderiv ℝ g t)‖ * ‖(fderiv ℝ g t) w‖ :=
        (J (fderiv ℝ g t)).le_opNorm _
      _ ≤ ‖fderiv ℝ g t‖ * (‖fderiv ℝ g t‖ * ‖w‖) := by
        rw [hJnorm]
        exact mul_le_mul_of_nonneg_left ((fderiv ℝ g t).le_opNorm w) (norm_nonneg _)
      _ = _ := by ring
  have hsecond : ‖J ((fderiv ℝ (fderiv ℝ g) t) w) (g t - v)‖ ≤
      (‖fderiv ℝ (fderiv ℝ g) t‖ * ‖g t - v‖) * ‖w‖ := by
    calc
      _ ≤ ‖J ((fderiv ℝ (fderiv ℝ g) t) w)‖ * ‖g t - v‖ :=
        (J ((fderiv ℝ (fderiv ℝ g) t) w)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ g) t‖ * ‖w‖) * ‖g t - v‖ := by
        rw [hJnorm]
        exact mul_le_mul_of_nonneg_right
          ((fderiv ℝ (fderiv ℝ g) t).le_opNorm w) (norm_nonneg _)
      _ = _ := by ring
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

theorem normal_graph_remainder_small_of_scaled_bounds
    (g : E → F) (t : E) (v : F) (R a : ℝ) (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : DifferentiableAt ℝ g t) (hdg : DifferentiableAt ℝ (fderiv ℝ g) t)
    (hvalue : ‖g t‖ ≤ a * R) (hfirst : ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R) (hv : ‖v‖ ≤ R) :
    ‖(ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v)‖ ≤ R / 4 ∧
      ‖fderiv ℝ (fun s => (ContinuousLinearMap.adjoint (fderiv ℝ g s)) (g s - v)) t‖
        ≤ 1 / 2 := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans hfirst
  have hres : ‖g t - v‖ ≤ (a + 1) * R := by
    have hh := (norm_sub_le (g t) v).trans (add_le_add hvalue hv)
    nlinarith
  have haa := mul_le_mul_of_nonneg_left ha ha0
  have hquarter : a * (a + 1) ≤ (1:ℝ) / 4 := by nlinarith
  have hhalf : a ^ 2 + a * (a + 1) ≤ (1:ℝ) / 2 := by nlinarith
  constructor
  · calc
      _ ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ g t)‖ * ‖g t - v‖ :=
        (ContinuousLinearMap.adjoint (fderiv ℝ g t)).le_opNorm _
      _ = ‖fderiv ℝ g t‖ * ‖g t - v‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ a * ((a + 1) * R) := mul_le_mul hfirst hres (norm_nonneg _) ha0
      _ = (a * (a + 1)) * R := by ring
      _ ≤ ((1:ℝ) / 4) * R := mul_le_mul_of_nonneg_right hquarter hR.le
      _ = R / 4 := by ring
  · have hsquare : ‖fderiv ℝ g t‖ ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hfirst 2
    have hproduct : ‖fderiv ℝ (fderiv ℝ g) t‖ * ‖g t - v‖ ≤ a * (a + 1) := by
      calc
        _ ≤ (a / R) * ((a + 1) * R) :=
          mul_le_mul hsecond hres (norm_nonneg _) (div_nonneg ha0 hR.le)
        _ = a * (a + 1) := by field_simp [hR.ne']
    exact (norm_fderiv_normal_graph_remainder_le g t v hg hdg).trans
      ((add_le_add hsquare hproduct).trans hhalf)

end
end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis
section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem norm_iteratedFDeriv_normal_graph_remainder_le
    (g : E → F) (U : Set E) (hU : IsOpen U) (j : ℕ)
    (hg : ContDiffOn ℝ (j + 1 : ℕ) g U) (t : E) (ht : t ∈ U) (v : F) :
    ‖iteratedFDeriv ℝ j
      (fun s => (ContinuousLinearMap.adjoint (fderiv ℝ g s)) (g s - v)) t‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ (i + 1) g t‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun s => g s - v) t‖ := by
  let J : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.adjoint
  have hdg : ContDiffOn ℝ (j : ℕ) (fderiv ℝ g) U :=
    hg.fderiv_of_isOpen hU (by simp)
  have hJ : ContDiffOn ℝ (j : ℕ) (fun s => J (fderiv ℝ g s)) U :=
    J.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hdg
  have hgv : ContDiffOn ℝ (j : ℕ) (fun s => g s - v) U :=
    (hg.of_le (by simp)).sub contDiffOn_const
  have h := norm_iteratedFDerivWithin_clm_apply hJ hgv hU.uniqueDiffOn ht
    (le_rfl : (j : ℕ∞ω) ≤ j)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU ht] at h
  have hnorm (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun s => J (fderiv ℝ g s)) t‖ =
        ‖iteratedFDeriv ℝ (i + 1) g t‖ := by
    change ‖iteratedFDeriv ℝ i (J ∘ fderiv ℝ g) t‖ = _
    rw [J.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]
  simp_rw [hnorm] at h
  exact h

end
end DifferentialGeometry.Analysis
