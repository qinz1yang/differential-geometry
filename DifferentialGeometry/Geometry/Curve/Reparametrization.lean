import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section

open Bundle Manifold
open scoped Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_comp_add_apply_one {γ : ℝ → M} (s d : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (s + d)) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun t ↦ γ (t + d)) s (1 : ℝ) : E) =
      mfderiv 𝓘(ℝ, ℝ) I γ (s + d) (1 : ℝ) := by
  have hadd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t + d) s
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) s)) :=
    ((hasFDerivAt_id s).add_const d).hasMFDerivAt
  exact congrArg (fun A : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (γ (s + d)) ↦ A (1 : ℝ))
    (hγ.hasMFDerivAt.comp s hadd).mfderiv

theorem mfderiv_comp_affine_apply_one {γ : ℝ → M} (s c d : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * s + d)) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun t ↦ γ (c * t + d)) s (1 : ℝ) : E) =
      c • (mfderiv 𝓘(ℝ, ℝ) I γ (c * s + d) (1 : ℝ) : E) := by
  have ha : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ c * t + d) s
      (c • ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) s)) :=
    (((hasFDerivAt_id s).const_smul c).add_const d).hasMFDerivAt
  have hh := congrArg
    (fun A : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I (γ (c * s + d)) ↦ A (1 : ℝ))
    (hγ.hasMFDerivAt.comp s ha).mfderiv
  exact hh.trans ((mfderiv 𝓘(ℝ, ℝ) I γ (c * s + d)).map_smul c (1 : ℝ))

end DifferentialGeometry.Geometry
