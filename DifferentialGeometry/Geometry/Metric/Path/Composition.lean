import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold Topology

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ y : N, ENorm (TangentSpace J y)]

theorem pathELength_comp_le_of_enorm_mfderiv_le
    (f : M → N) {γ : ℝ → M} {a b : ℝ} (C : NNReal)
    (hγ : ∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hf : ∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt I J f (γ t))
    (hnorm : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖mfderiv I J f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)‖ₑ ≤
        (C : ENNReal) * ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ) :
    pathELength J (f ∘ γ) a b ≤ (C : ENNReal) * pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hγ, hf, hnorm] with t hγt hft hnormt
  have hcomp := mfderiv_comp t hft hγt
  change ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t 1‖ₑ ≤
    (C : ENNReal) * ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
  rw [hcomp]
  exact hnormt

theorem pathELength_comp_eq_of_enorm_mfderiv_eq
    (f : M → N) {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hf : ∀ᵐ t ∂volume.restrict (Ioo a b), MDifferentiableAt I J f (γ t))
    (hnorm : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖mfderiv I J f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)‖ₑ =
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ) :
    pathELength J (f ∘ γ) a b = pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo]
  apply lintegral_congr_ae
  filter_upwards [hγ, hf, hnorm] with t hγt hft hnormt
  have hcomp := mfderiv_comp t hft hγt
  change ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t 1‖ₑ =
    ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
  rw [hcomp]
  exact hnormt

end Manifold
