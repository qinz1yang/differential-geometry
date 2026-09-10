import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation

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
theorem parabolicNablaKRm04Field
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (k : ℕ) :
    nablaKRm04Field (I := I) (parabolicSolution (I := I) S τ R hR hτ) s k =
      R • nablaKRm04Field (I := I) S (parabolicTime τ R s) k := by
  have hconn :
      (parabolicSolution (I := I) S τ R hR hτ).family.connection s =
        S.family.connection (parabolicTime τ R s) := by
    simpa only [SolutionOn.family_connection] using
      congrFun (parabolicSolution_connection (I := I) S τ R hR hτ) s
  induction k with
  | zero =>
      let := tensor0SBundleTopology
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + 0)
      apply DFunLike.ext
      intro y
      exact parabolicSolution_rm04 (I := I) S τ R hR hτ s y
  | succ k ih =>
      let := tensor0SBundleTopology
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + (k + 1))
      apply DFunLike.ext
      intro y
      change
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k)
            ((parabolicSolution (I := I) S τ R hR hτ).family.connection s)
            (nablaKRm04Field (I := I) (parabolicSolution (I := I) S τ R hR hτ) s k) y =
          R • totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k)
            (S.family.connection (parabolicTime τ R s))
            (nablaKRm04Field (I := I) S (parabolicTime τ R s) k) y
      rw [totalNabla0SFun_congr (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) hconn ih y]
      exact totalNabla0SFun_smul (S.family.connection (parabolicTime τ R s)) R
        (nablaKRm04Field (I := I) S (parabolicTime τ R s) k) y

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem parabolicNablaKRmNormSq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (k : ℕ) (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic
        (parabolicSolution (I := I) S τ R hR hτ) k s x =
      (R⁻¹) ^ (2 + k) *
        nablaKRm04NormSqIntrinsic S k (parabolicTime τ R s) x := by
  have hfield :
      nablaKRm04Field (I := I) (parabolicSolution (I := I) S τ R hR hτ) s k x =
        R • nablaKRm04Field (I := I) S (parabolicTime τ R s) k x := by
    rw [parabolicNablaKRm04Field (I := I) S τ R hR hτ s k]
    rfl
  have hcoef : (R⁻¹ : Real) ^ (4 + k) * R ^ 2 = (R⁻¹ : Real) ^ (2 + k) := by
    have hk : 4 + k = 2 + (2 + k) := by omega
    rw [hk, pow_add, mul_comm ((R⁻¹ : Real) ^ 2) ((R⁻¹ : Real) ^ (2 + k)),
      mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hR), one_pow, mul_one]
  unfold nablaKRm04NormSqIntrinsic
  rw [hfield, show
    (parabolicSolution (I := I) S τ R hR hτ).base.metric s =
      scaleMetric (I := I) R hR (S.base.metric (parabolicTime τ R s)) by rfl,
    Tensor0SBundle.normSq0S_scale, Tensor0SBundle.normSq0S_smul,
    ← mul_assoc, hcoef]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem parabolicNablaRmNormSq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic
        (parabolicSolution (I := I) S τ R hR hτ) 1 s x =
      (R⁻¹) ^ 3 *
        nablaKRm04NormSqIntrinsic S 1 (parabolicTime τ R s) x :=
  parabolicNablaKRmNormSq (I := I) S τ R hR hτ 1 s x

end DifferentialGeometry.PDE.RicciFlow
