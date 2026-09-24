import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ForwardIntegralCurveUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Topology.Manifold.AddCircle.PeriodicExtension
import DifferentialGeometry.Topology.Manifold.AddCircle.VectorField
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section

open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace AddCircle

private theorem hasMFDerivWithinAt_of_local_lift
    {J : Set ℝ} {t b : ℝ} {l : ℝ → ℝ} {γ : ℝ → AddCircle (1 : ℝ)}
    (ht : t ∈ J) (hl : HasDerivWithinAt l b J t)
    (heq : (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[J] t] γ) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (b • parameterTangent (γ t))) := by
  have heqt := heq.eq_of_nhdsWithin ht
  have hq := (contMDiff_coe.mdifferentiableAt (x := l t)
    (by decide : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt
  have hcomp := hq.comp_hasMFDerivWithinAt t hl.hasFDerivWithinAt.hasMFDerivWithinAt
  have hval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) (l t) b =
      b • parameterTangent (γ t) := by
    rw [← heqt, parameterTangent_coe]
    let L : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) (l t)
    change L b = b • L 1
    simpa only [smul_eq_mul, mul_one] using L.map_smul b (1 : ℝ)
  have hcomp' : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun s => (l s : AddCircle (1 : ℝ))) J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (b • parameterTangent (γ t))) := by
    refine hcomp.congr_mfderiv ?_
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) (l t) (r • b) =
      r • (b • parameterTangent (γ t))
    erw [map_smul, hval]
    rfl
  exact hcomp'.congr_of_eventuallyEq heq.symm heqt.symm

theorem eqOn_of_periodic_ode {a b : ℝ} {β : ℝ → ℝ → ℝ}
    (hβ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1 p.2)
      (Icc a b ×ˢ (univ : Set ℝ)))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (β t) 1)
    {γ η : ℝ → AddCircle (1 : ℝ)}
    (hγ : ∀ t ∈ Icc a b, ∃ l : ℝ → ℝ,
      (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[Icc a b] t] γ ∧
      HasDerivWithinAt l (β t (l t)) (Icc a b) t)
    (hη : ∀ t ∈ Icc a b, ∃ l : ℝ → ℝ,
      (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[Icc a b] t] η ∧
      HasDerivWithinAt l (β t (l t)) (Icc a b) t)
    (hstart : γ a = η a) : EqOn γ η (Icc a b) := by
  obtain ⟨f, hf, hfeq⟩ := exists_contMDiff_extension_of_periodic hβ hper
  let X : ℝ → ∀ z : AddCircle (1 : ℝ), TangentSpace 𝓘(ℝ, ℝ) z :=
    fun t z => f (t, z) • parameterTangent z
  have hX := DifferentialGeometry.Analysis.ODE.autonomizedFieldJointC1_of_contMDiff
    X (contMDiff_parameterTangent_smul hf)
  have hcurve (σ : ℝ → AddCircle (1 : ℝ))
      (hσ : ∀ t ∈ Icc a b, ∃ l : ℝ → ℝ,
        (fun s => (l s : AddCircle (1 : ℝ))) =ᶠ[𝓝[Icc a b] t] σ ∧
        HasDerivWithinAt l (β t (l t)) (Icc a b) t) :
      ∀ t ∈ Icc a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ (Icc a b) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (σ t))) := by
    intro t ht
    obtain ⟨l, hleq, hld⟩ := hσ t ht
    have hval : f (t, σ t) = β t (l t) := by
      rw [← hleq.eq_of_nhdsWithin ht, hfeq t ht]
    simpa only [X, hval] using hasMFDerivWithinAt_of_local_lift ht hld hleq
  exact DifferentialGeometry.Analysis.ODE.forward_integral_curves_eqOn_of_jointC1
    X hX (fun t _ => γ t) (fun t _ => η t) 0 0
    (hcurve γ hγ) (hcurve η hη) hstart

end AddCircle

end
