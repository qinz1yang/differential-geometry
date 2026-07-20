import DifferentialGeometry.Geometry.Hodge.OneFormHodgeLaplacian
import DifferentialGeometry.Geometry.Surface.GaussCurvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


theorem neg_oneFormHodgeLaplacianAt_eq_roughLap_sub_gauss_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x))
    (x : M) (X : TangentSpace I x) :
    -(oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x (fun _ : Fin 1 => X))
      = roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X)
        - gaussCurvature (I := I) g x * α x (fun _ : Fin 1 => X) := by
  have hW := oneFormWeitzenbockIdentity (I := I) g α nablaAlpha nabla2Alpha hRealizes2 x X
  have hRic : metricRicciAt (I := I) (M := M) g x
      (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X)
      = gaussCurvature (I := I) g x * α x (fun _ : Fin 1 => X) := by
    rw [ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim g x,
      cotangentSharp_inner, cotangentToDual_apply]
  rw [hW, hRic]
  ring


theorem neg_oneFormHodgeLaplacian_eq_roughLap_sub_gauss_smul_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x))
    (x : M) :
    -(oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x)
      = roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x)
        - gaussCurvature (I := I) g x • (α x) := by
  ext v
  have hv : (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  rw [← hv, Tensor0SSpace.neg_apply]
  exact neg_oneFormHodgeLaplacianAt_eq_roughLap_sub_gauss_twoDim (I := I) hdim g α nablaAlpha
    nabla2Alpha hRealizes2 x (v 0)


end DifferentialGeometry.Integral.Connection
