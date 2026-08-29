import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.HeatEquation

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem paraNablaRmNormSq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic
        (paraSolution (I := I) S τ R hR hτ) 1 s x =
      (R⁻¹) ^ 3 *
        nablaKRm04NormSqIntrinsic S 1 (paraTime τ R s) x := by
  let := tensor0SBundleTopology
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
  have hconn :
      (paraSolution (I := I) S τ R hR hτ).family.connection s =
        S.family.connection (paraTime τ R s) := by
    simpa only [SolutionOn.family_connection] using
      congrFun (paraSolution_connection (I := I) S τ R hR hτ) s
  have hrm :
      (paraSolution (I := I) S τ R hR hτ).base.rm04 s =
        R • S.base.rm04 (paraTime τ R s) := by
    apply DFunLike.ext
    intro y
    exact paraSolution_rm04 (I := I) S τ R hR hτ s y
  have hfield :
      nablaKRm04Field (I := I)
          (paraSolution (I := I) S τ R hR hτ) s 1 x =
        R • nablaKRm04Field (I := I) S (paraTime τ R s) 1 x := by
    change
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          ((paraSolution (I := I) S τ R hR hτ).family.connection s)
          ((paraSolution (I := I) S τ R hR hτ).base.rm04 s) x =
        R • totalNabla0SFun
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (S.family.connection (paraTime τ R s))
          (S.base.rm04 (paraTime τ R s)) x
    rw [hconn, hrm]
    exact totalNabla0SFun_smul
      (S.family.connection (paraTime τ R s)) R
      (S.base.rm04 (paraTime τ R s)) x
  unfold nablaKRm04NormSqIntrinsic
  rw [hfield, show
    (paraSolution (I := I) S τ R hR hτ).base.metric s =
      scaleMetric (I := I) R hR (S.base.metric (paraTime τ R s)) by rfl,
    Tensor0SBundle.normSq0S_scale, Tensor0SBundle.normSq0S_smul]
  norm_num
  field_simp [ne_of_gt hR]

end DifferentialGeometry.PDE.RicciFlow
