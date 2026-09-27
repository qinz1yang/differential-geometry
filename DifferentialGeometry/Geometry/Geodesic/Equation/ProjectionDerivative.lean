import DifferentialGeometry.Geometry.Geodesic.Flow.VectorField
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Geodesic.Local.Existence
import DifferentialGeometry.Geometry.Geodesic.Equation.FromIntegralCurve
import DifferentialGeometry.Geometry.Geodesic.Local.Smoothness
import DifferentialGeometry.Geometry.Exponential.ChartFlow.Coordinates.Chart
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

omit [NeZero (Module.finrank ℝ E)] in
theorem IsMIntegralCurveAt.mfderiv_proj_one {g : SmoothRiemannianMetric I M} {f : ℝ → TangentBundle I M}
    {α : M} {t₀ : ℝ}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀)
    (hsrc : (f t₀).proj ∈ (chartAt H α).source) :
    mfderiv 𝓘(ℝ, ℝ) I (fun t => (f t).proj) t₀ (1 : ℝ) = (f t₀).snd := by
  classical
  have hpush :=
    chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := α) (t₀ := t₀)
      (f := f) hf
  have hpush_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPushVF (I := I) g α f t₀ t₀) t₀ := hpush.self_of_nhds
  have hpush_t₀' : HasDerivAt (chartPushLift (I := I) f t₀)
      (geodesicVectorFieldChart (I := I) g α (f t₀)) t₀ := by
    rw [← chartPushVF_self (I := I) g α f t₀]
    exact hpush_t₀
  have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
    hasFDerivAt_fst
  have hfst :
      HasDerivAt (fun t => (chartPushLift (I := I) f t₀ t).1)
        ((geodesicVectorFieldChart (I := I) g α (f t₀) : E × E).1) t₀ :=
    hfst_clm.comp_hasDerivAt t₀ hpush_t₀'
  have hfun_eq :
      (fun t : ℝ => (chartPushLift (I := I) f t₀ t).1) =
        (fun t : ℝ => extChartAt I (f t₀).proj (f t).proj) := by
    funext t
    exact chartPushLift_fst_eq (I := I) (f := f) t₀ t
  rw [hfun_eq] at hfst
  have hfst_eq_snd : (geodesicVectorFieldChart (I := I) g α (f t₀) : E × E).1 =
      ((f t₀).snd : E) :=
    geodesicVectorFieldChart_fst (I := I) g α (p := f t₀) hsrc
  rw [hfst_eq_snd] at hfst
  set γ : ℝ → M := fun t => (f t).proj with hγ_def
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hγ_cont : ContinuousAt γ t₀ :=
    hπ_cont.continuousAt.comp hf.continuousAt
  have hfd : HasFDerivAt (extChartAt I (f t₀).proj ∘ γ)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E))) t₀ :=
    hfst.hasFDerivAt
  have hfdw : HasFDerivWithinAt (extChartAt I (f t₀).proj ∘ γ)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E)))
      (range 𝓘(ℝ, ℝ)) t₀ := by
    rw [ModelWithCorners.range_eq_univ]
    exact hfd.hasFDerivWithinAt
  have hMF : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E)) := by
    refine ⟨hγ_cont, ?_⟩
    have hext_self : extChartAt 𝓘(ℝ, ℝ) t₀ t₀ = t₀ := by
      simp [extChartAt, chartAt_self_eq]
    rw [hext_self]
    have hrewrite :
        writtenInExtChartAt 𝓘(ℝ, ℝ) I t₀ γ = extChartAt I (f t₀).proj ∘ γ := by
      funext s
      simp [writtenInExtChartAt, hγ_def, chartAt_self_eq]
    rw [hrewrite]
    exact hfdw
  have hmfd : mfderiv 𝓘(ℝ, ℝ) I γ t₀ =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E) := hMF.mfderiv
  have happly : mfderiv 𝓘(ℝ, ℝ) I γ t₀ (1 : ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E) (1 : ℝ) := by
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1) hmfd
  have hsr_apply :
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E) (1 : ℝ) =
        ((f t₀).snd : E) := by
    rw [ContinuousLinearMap.smulRight_apply]; simp
  rw [happly]
  exact hsr_apply

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
