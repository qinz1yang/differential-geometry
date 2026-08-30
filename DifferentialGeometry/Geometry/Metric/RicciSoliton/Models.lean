import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

noncomputable def gaussianPotential : C^∞⟮𝓘(Real, E), E; Real⟯ :=
  ⟨fun x : E => ‖x‖ ^ 2 / 4,
    ((contDiff_norm_sq Real).div_const 4).contMDiff⟩

omit [FiniteDimensional Real E] in
@[simp] theorem gaussianPotential_apply (x : E) :
    gaussianPotential x = ‖x‖ ^ 2 / 4 := by
  rfl

def isGaussianGradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (σ : Real) : Prop :=
  ∃ hσ : 0 < σ, ∃ Ψ : M ≃ₘ⟮I, 𝓘(Real, E)⟯ E, ∃ b : Real,
    Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
        scaleMetric (I := I) σ hσ g ∧
      f + ContMDiffMap.const b = gaussianPotential.comp Ψ.toContMDiffMap

theorem isGaussianGradientRicciSoliton_add_const
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (c : Real) :
    isGaussianGradientRicciSoliton (I := I) g
      (f + ContMDiffMap.const c) σ ↔
      isGaussianGradientRicciSoliton (I := I) g f σ := by
  constructor
  · rintro ⟨hσ, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b + c, hmetric, ?_⟩
    apply ContMDiffMap.ext
    intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q x) hpotential
    change f x + (b + c) = gaussianPotential (Ψ x)
    change (f x + c) + b = gaussianPotential (Ψ x) at hx
    rw [show f x + (b + c) = (f x + c) + b by ring]
    exact hx
  · rintro ⟨hσ, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b - c, hmetric, ?_⟩
    apply ContMDiffMap.ext
    intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q x) hpotential
    change (f x + c) + (b - c) = gaussianPotential (Ψ x)
    change f x + b = gaussianPotential (Ψ x) at hx
    rw [show (f x + c) + (b - c) = f x + b by ring]
    exact hx

theorem isGaussianGradientRicciSoliton_euclidean :
    isGaussianGradientRicciSoliton
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 := by
  refine ⟨zero_lt_one, _root_.Diffeomorph.refl 𝓘(Real, E) E ∞, 0, ?_, ?_⟩
  · rw [Diffeomorph.pullbackMetricCross_refl]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner]
    ring
  · apply ContMDiffMap.ext
    intro x
    change gaussianPotential x + 0 = gaussianPotential x
    ring

end DifferentialGeometry.Geometry
