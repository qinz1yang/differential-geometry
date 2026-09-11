import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.Analysis.Integration.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [OpensMeasurableSpace Z]
variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
    {μ : Measure Z} {Ω : Set E} {U V : Z × E → ℝ}
    (hU : LocallyIntegrable U (μ.prod (volume.restrict Ω)))
    (hV : LocallyIntegrable V (μ.prod (volume.restrict Ω)))
    (i : Fin d)
    (hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => V (t, x)) (fun x => U (t, x)) Ω)
    (φ : Z × E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (univ : Set Z) ×ˢ Ω) :
    (∫ p, U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂μ.prod (volume.restrict Ω)) =
      -∫ p, V p * φ p ∂μ.prod (volume.restrict Ω) := by
  have hdφ : Continuous (fun p => fderiv ℝ φ p (0, EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft : Integrable (fun p => U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
      (μ.prod (volume.restrict Ω)) :=
    hU.integrable_smul_right_of_hasCompactSupport hdφ
      (hφc.fderiv_apply (𝕜 := ℝ) (0, EuclideanSpace.single i 1))
  have hright : Integrable (fun p => V p * φ p) (μ.prod (volume.restrict Ω)) :=
    hV.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  rw [hleft.integral_prod, hright.integral_prod, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hweak] with t ht
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => φ (t, x)) :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have hsupp : tsupport (fun x : E => φ (t, x)) ⊆ Prod.snd '' tsupport φ := by
    intro x hx
    exact ⟨(t, x), tsupport_comp_subset_preimage (f := fun y : E => (t, y)) φ (by fun_prop) hx, rfl⟩
  have hslice_c : HasCompactSupport (fun x : E => φ (t, x)) :=
    IsCompact.of_isClosed_subset (hφc.image continuous_snd) (isClosed_tsupport _) hsupp
  have hslice_s : tsupport (fun x : E => φ (t, x)) ⊆ Ω := by
    intro x hx
    exact (hφs (tsupport_comp_subset_preimage (f := fun y : E => (t, y)) φ (by fun_prop) hx)).2
  have hd (x : E) : fderiv ℝ (fun y : E => φ (t, y)) x (EuclideanSpace.single i 1) =
      fderiv ℝ φ (t, x) (0, EuclideanSpace.single i 1) := by
    have h := (hφ.differentiable (by simp) (t, x)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    exact congrArg (fun L => L (EuclideanSpace.single i 1)) h.fderiv
  simpa only [hd] using ht (fun x => φ (t, x)) hslice hslice_c hslice_s

end DifferentialGeometry.Analysis.Sobolev.Euclidean
