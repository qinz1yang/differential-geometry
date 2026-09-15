import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry

noncomputable section

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem velocity_add_period (c : CurveMap M) (J : Set ℝ) (t x : ℝ) :
    c.velocity (I := I) J (x + 1) t = c.velocity (I := I) J x t := by
  have hfun : c.lift (x + 1) = c.lift x := by
    funext s
    exact c.lift_add_period s x
  exact congrArg (fun f : ℝ → M => mfderivWithin 𝓘(ℝ, ℝ) I f J t (1 : ℝ)) hfun

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless]

theorem curvatureVector_add_period (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    c.curvatureVector g (x + 1) t = c.curvatureVector g x t := by
  have hγ : ∀ y, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.lift z t) y :=
    fun y => (contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)).mdifferentiableAt (by norm_num)
  have hs : c.speed g (x + 1) t = c.speed g x t :=
    c.speed_add_period g t x (hγ (x + 1))
  have hD : c.Dx g (c.unitTangent g) (x + 1) t = c.Dx g (c.unitTangent g) x t :=
    c.Dx_add_period g t x (c.unitTangent g)
      (fun y => c.unitTangent_add_period g t y (hγ (y + 1)))
      (c.unitTangent_contMDiff g J hc hi t ht) (hγ (x + 1))
  change (c.speed g (x + 1) t)⁻¹ • c.Dx g (c.unitTangent g) (x + 1) t =
    (c.speed g x t)⁻¹ • c.Dx g (c.unitTangent g) x t
  rw [hs, hD]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
