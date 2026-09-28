import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.NonnegativeApproximation
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Operator.Bilinear


noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_nonneg_smooth_compactSupport_approx_of_measurePreserving
    (e : X ≃L[ℝ] E) (he : MeasurePreserving e μ volume)
    {u : X → ℝ} (hu : LocallyLipschitz u) (huc : HasCompactSupport u)
    (hunonneg : ∀ x, 0 ≤ u x) {Ω : Set X} (hΩ : IsOpen Ω) (hsupport : tsupport u ⊆ Ω) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ Ω ∧ tsupport u ⊆ K ∧
      Integrable u μ ∧ Integrable (fderiv ℝ u) μ ∧
      ∃ v : ℕ → X → ℝ,
        (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ tsupport (v n) ⊆ K ∧
          (∀ x, 0 ≤ v n x) ∧ Integrable (v n) μ ∧ Integrable (fderiv ℝ (v n)) μ) ∧
        Tendsto (fun n => ∫ x, ‖v n x - u x‖ ∂μ) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x, ‖fderiv ℝ (v n) x - fderiv ℝ u x‖ ∂μ) atTop (𝓝 0) := by
  let u' : E → ℝ := u ∘ e.symm
  let Ω' : Set E := e.symm ⁻¹' Ω
  have hemb : MeasurableEmbedding e := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hu' : LocallyLipschitz u' := hu.comp e.symm.toContinuousLinearMap.lipschitzWith.locallyLipschitz
  have huc' : HasCompactSupport u' := huc.comp_homeomorph e.symm.toHomeomorph
  have hu'support : tsupport u' ⊆ Ω' :=
    (tsupport_comp_subset_preimage u e.symm.continuous).trans (preimage_mono hsupport)
  obtain ⟨K', hK', hKΩ', hu'K, hu'Int, hdu'Int, v', hv', hlim', hdlim'⟩ :=
    exists_nonneg_smooth_compactSupport_approx_of_locallyLipschitz hu' huc'
      (fun x => hunonneg (e.symm x)) (hΩ.preimage e.symm.continuous) hu'support
  let K : Set X := e ⁻¹' K'
  let v : ℕ → X → ℝ := fun n => v' n ∘ e
  have hu'e : u' ∘ e = u := by funext x; simp only [u', Function.comp_apply, e.symm_apply_apply]
  have hK : IsCompact K := by
    dsimp only [K]
    rw [← e.image_symm_eq_preimage]
    exact hK'.image e.symm.continuous
  have hKΩ : K ⊆ Ω := by
    intro x hx
    have h := hKΩ' hx
    simpa only [Ω', mem_preimage, e.symm_apply_apply] using h
  have huK : tsupport u ⊆ K := by
    rw [← hu'e]
    exact (tsupport_comp_subset_preimage u' e.continuous).trans (preimage_mono hu'K)
  let T : (E →L[ℝ] ℝ) →L[ℝ] X →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ X E ℝ).flip e.toContinuousLinearMap
  have hderiv (f : E → ℝ) (x : X) :
      fderiv ℝ (f ∘ e) x = T (fderiv ℝ f (e x)) := e.comp_right_fderiv
  have hdu (x : X) : fderiv ℝ u x = T (fderiv ℝ u' (e x)) := by
    rw [← hu'e]
    exact hderiv u' x
  have hdInt (f : E → ℝ) (hf : Integrable (fderiv ℝ f) volume) :
      Integrable (fderiv ℝ (f ∘ e)) μ := by
    have h := T.integrable_comp (he.integrable_comp_of_integrable hf)
    rw [show fderiv ℝ (f ∘ e) = (fun x => T (fderiv ℝ f (e x))) by
      funext x
      exact hderiv f x]
    exact h
  have huInt : Integrable u μ := by
    simpa only [hu'e] using he.integrable_comp_of_integrable hu'Int
  have hduInt : Integrable (fderiv ℝ u) μ := by
    simpa only [hu'e] using hdInt u' hdu'Int
  have hv (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ tsupport (v n) ⊆ K ∧
      (∀ x, 0 ≤ v n x) ∧ Integrable (v n) μ ∧ Integrable (fderiv ℝ (v n)) μ := by
    refine ⟨(hv' n).1.comp e.contDiff, ?_, (fun x => (hv' n).2.2.1 (e x)),
      he.integrable_comp_of_integrable (hv' n).2.2.2.1, hdInt (v' n) (hv' n).2.2.2.2⟩
    exact (tsupport_comp_subset_preimage (v' n) e.continuous).trans
      (preimage_mono (hv' n).2.1)
  refine ⟨K, hK, hKΩ, huK, huInt, hduInt, v, hv, ?_, ?_⟩
  · have heq (n : ℕ) : (∫ x, ‖v n x - u x‖ ∂μ) = ∫ y, ‖v' n y - u' y‖ := by
      simpa only [v, Function.comp_apply, u', e.symm_apply_apply] using
        he.integral_comp hemb (fun y => ‖v' n y - u' y‖)
    simpa only [heq] using hlim'
  · have hbound (n : ℕ) :
        (∫ x, ‖fderiv ℝ (v n) x - fderiv ℝ u x‖ ∂μ) ≤
          ‖T‖ * ∫ y, ‖fderiv ℝ (v' n) y - fderiv ℝ u' y‖ := by
      calc
        _ ≤ ∫ x, ‖T‖ * ‖fderiv ℝ (v' n) (e x) - fderiv ℝ u' (e x)‖ ∂μ := by
          apply integral_mono ((hv n).2.2.2.2.sub hduInt).norm
            ((he.integrable_comp_of_integrable
              (((hv' n).2.2.2.2.sub hdu'Int).norm)).const_mul ‖T‖)
          intro x
          change ‖fderiv ℝ (v n) x - fderiv ℝ u x‖ ≤
            ‖T‖ * ‖fderiv ℝ (v' n) (e x) - fderiv ℝ u' (e x)‖
          rw [hdu, show fderiv ℝ (v n) x = T (fderiv ℝ (v' n) (e x)) from hderiv _ x,
            ← T.map_sub]
          exact T.le_opNorm _
        _ = _ := by
          rw [integral_const_mul]
          exact congrArg (fun r => ‖T‖ * r)
            (he.integral_comp hemb (fun y => ‖fderiv ℝ (v' n) y - fderiv ℝ u' y‖))
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound
    simpa only [mul_zero] using hdlim'.const_mul ‖T‖

end DifferentialGeometry.Analysis.Sobolev
