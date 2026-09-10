import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold Topology
namespace Poincare.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}


theorem hasDerivWithinAt_scalar_comp_integralCurve {f : M → ℝ} {γ : ℝ → M}
    {V : (x : M) → TangentSpace I x} {s : Set ℝ} {t : ℝ}
    (hγ : IsMIntegralCurveOn γ V s) (ht : t ∈ s)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t)) :
    HasDerivWithinAt (f ∘ γ) ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (V (γ t))) s t := by
  let D : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f (γ t)
  have hh := hf.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
  have hd : HasFDerivWithinAt (f ∘ γ)
      (D.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (show E from V (γ t)))) s t := hh.hasFDerivWithinAt
  have he : (D.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (show E from V (γ t)))) 1 = D (V (γ t)) := by
    change D ((1 : ℝ) • (show E from V (γ t))) = D (V (γ t))
    rw [one_smul]
  exact he ▸ hd.hasDerivWithinAt


theorem scalar_eq_affine_of_integralCurve_constant_rate {f : M → ℝ} {γ : ℝ → M}
    {V : (x : M) → TangentSpace I x} {s : Set ℝ} {a k : ℝ}
    (hγ : IsMIntegralCurveOn γ V s) (hs : Convex ℝ s) (ha : a ∈ s)
    (hf : ∀ t ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t))
    (hrate : ∀ t ∈ s, (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (V (γ t)) = k) :
    EqOn (f ∘ γ) (fun t => f (γ a) + k * (t-a)) s := by
  have hD : ∀ t ∈ s, HasDerivWithinAt (fun u => f (γ u) - k*u) 0 s t := by
    intro t ht
    have hh := hasDerivWithinAt_scalar_comp_integralCurve hγ ht (hf t ht)
    rw [hrate t ht] at hh
    have hsub := hh.sub (((hasDerivAt_id t).const_mul k).hasDerivWithinAt (s := s))
    convert hsub using 1 <;> first | rfl | simp
  intro t ht
  have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD
    (C := 0) (fun _ _ => by simp) hs ha ht
  have he : (f (γ t) - k*t) - (f (γ a) - k*a) = 0 :=
    norm_le_zero_iff.mp (by simpa only [zero_mul] using hn)
  change f (γ t) = f (γ a) + k*(t-a)
  linarith

end Poincare.Manifold
