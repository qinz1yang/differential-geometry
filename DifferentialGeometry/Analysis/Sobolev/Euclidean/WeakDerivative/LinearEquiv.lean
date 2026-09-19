import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_comp_continuousLinearEquiv
    (e : E ≃L[ℝ] F) {μ : Measure F} (he : MeasurePreserving e volume μ)
    {Ω : Set F} (i : Fin d) {u v : F → ℝ}
    (hweak : ∀ φ : F → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ q, u q * fderiv ℝ φ q (e (EuclideanSpace.single i 1)) ∂μ.restrict Ω) =
        -∫ q, v q * φ q ∂μ.restrict Ω) :
    DeGiorgi.HasWeakPartialDeriv i (v ∘ e) (u ∘ e) (e ⁻¹' Ω) := by
  intro φ hφ hφc hφs
  let ψ : F → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph e.symm.toHomeomorph
  have hψs : tsupport ψ ⊆ Ω := by
    intro y hy
    have hmem := hφs (tsupport_comp_subset_preimage φ e.symm.continuous hy)
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hmem
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hrestr := he.restrict_preimage_emb hemb Ω
  have hd (x : E) : fderiv ℝ ψ (e x) (e (EuclideanSpace.single i 1)) =
      fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    change fderiv ℝ (φ ∘ e.symm) (e x) (e (EuclideanSpace.single i 1)) = _
    rw [fderiv_comp _ (hφ.differentiable (by simp) _) e.symm.differentiableAt]
    rw [e.symm.hasFDerivAt.fderiv]
    simp
  have hleft := hrestr.integral_comp hemb
    (fun y => u y * fderiv ℝ ψ y (e (EuclideanSpace.single i 1)))
  have hright := hrestr.integral_comp hemb (fun y => v y * ψ y)
  simp only [hd] at hleft
  simp only [ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] at hright
  exact hleft.trans ((hweak ψ hψ hψc hψs).trans (congrArg Neg.neg hright.symm))

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
