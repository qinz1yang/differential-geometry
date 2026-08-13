import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlgebraicSectionalNonnegativeCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private local instance parallelCurvatureOperatorTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance parallelCurvatureOperatorTensor04NormedSpace (x : M) :
    NormedSpace Real (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance parallelCurvatureOperatorTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor04At (I := I) (M := M) x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (parallelCurvatureOperatorTensor04NormedAddCommGroup (I := I) x)

private local instance parallelCurvatureOperatorTensor04Module (x : M) :
    Module Real (Tensor04At (I := I) (M := M) x) :=
  @NormedSpace.toModule _ _ _ _
    (parallelCurvatureOperatorTensor04NormedSpace (I := I) x)

private local instance parallelCurvatureOperatorTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (parallelCurvatureOperatorTensor04NormedAddCommGroup (I := I) x))))

@[simp]
theorem parallelTransportAlgebraicCurvatureTensorCLEOnIcc_curvatureOperatorQuadraticEval
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I (gamma 0)) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M)
        (parallelTransportAlgebraicCurvatureTensorCLEOnIcc
          (I := I) g gamma hgamma hL A) c
        (fun i => parallelTransportLinearEquivOnIcc
          (I := I) g gamma hgamma hL (v i))
        (fun i => parallelTransportLinearEquivOnIcc
          (I := I) g gamma hgamma hL (w i)) =
      algebraicCurvatureOperatorQuadraticEval
        (I := I) (M := M) A c v w := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL
  change algebraicCurvatureOperatorQuadraticEval (I := I) (M := M)
      (algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A) c
          (fun i => e (v i)) (fun i => e (w i)) = _
  rw [algebraicCurvatureOperatorQuadraticEval_pullback]
  simp

theorem parallelTransportAlgebraicCurvatureTensorCLEOnIcc_mem_curvatureOperatorNonnegativeCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0)) :
    parallelTransportAlgebraicCurvatureTensorCLEOnIcc
        (I := I) g gamma hgamma hL A ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
        A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
  algebraicCurvatureTensorPullbackCLE_mem_curvatureOperatorNonnegativeCone_iff
    (I := I) (M := M)
      (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm A

theorem algebraicCurvatureOperatorNonnegativeCone_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) :
    ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))).map
          (parallelTransportAlgebraicCurvatureTensorCLEOnIcc
            (I := I) g gamma hgamma hL).toContinuousLinearMap) =
      (algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L))) :=
  algebraicCurvatureOperatorNonnegativeCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm

theorem algebraicCurvatureOperatorNonnegative_dualZeroFace_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) {n : Nat}
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I (gamma 0)) :
    (((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w)).map
              (parallelTransportAlgebraicCurvatureTensorCLEOnIcc
                (I := I) g gamma hgamma hL).toContinuousLinearMap) =
      ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L))).dualZeroFace
            (algebraicCurvatureOperatorQuadraticEvalCLM (I := I) (M := M) c
              (fun i => parallelTransportLinearEquivOnIcc
                (I := I) g gamma hgamma hL (v i))
              (fun i => parallelTransportLinearEquivOnIcc
                (I := I) g gamma hgamma hL (w i)))) := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL
  change (((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w)).map
              (algebraicCurvatureTensorPullbackCLE
                (I := I) (M := M) e.symm).toContinuousLinearMap) =
    ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L))).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM (I := I) (M := M) c
            (fun i => e (v i)) (fun i => e (w i))))
  simpa using algebraicCurvatureOperatorNonnegative_dualZeroFace_map_pullback
    (I := I) (M := M) e.symm c (fun i => e (v i)) (fun i => e (w i))

theorem parallelTransportAlgebraicCurvatureTensorCLEOnIcc_mem_curvatureOperatorDualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I (gamma 0)) :
    parallelTransportAlgebraicCurvatureTensorCLEOnIcc
        (I := I) g gamma hgamma hL A ∈
      (algebraicCurvatureOperatorNonnegativeCone
        (I := I) (M := M)).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM (I := I) (M := M) c
            (fun i => parallelTransportLinearEquivOnIcc
              (I := I) g gamma hgamma hL (v i))
            (fun i => parallelTransportLinearEquivOnIcc
              (I := I) g gamma hgamma hL (w i))) ↔
      A ∈ (algebraicCurvatureOperatorNonnegativeCone
        (I := I) (M := M)).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w) := by
  rw [mem_algebraicCurvatureOperatorNonnegative_dualZeroFace,
    mem_algebraicCurvatureOperatorNonnegative_dualZeroFace]
  rw [parallelTransportAlgebraicCurvatureTensorCLEOnIcc_mem_curvatureOperatorNonnegativeCone_iff]
  rw [parallelTransportAlgebraicCurvatureTensorCLEOnIcc_curvatureOperatorQuadraticEval]

@[simp]
theorem parallelTransportAlgebraicCurvatureTensorCLEBetween_curvatureOperatorQuadraticEval
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I (gamma a)) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M)
        (parallelTransportAlgebraicCurvatureTensorCLEBetween
          (I := I) g gamma hgamma hab A) c
        (fun i => parallelTransportLinearEquivBetween
          (I := I) g gamma hgamma hab (v i))
        (fun i => parallelTransportLinearEquivBetween
          (I := I) g gamma hgamma hab (w i)) =
      algebraicCurvatureOperatorQuadraticEval
        (I := I) (M := M) A c v w := by
  let e := parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
  change algebraicCurvatureOperatorQuadraticEval (I := I) (M := M)
      (algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A) c
          (fun i => e (v i)) (fun i => e (w i)) = _
  rw [algebraicCurvatureOperatorQuadraticEval_pullback]
  simp

theorem parallelTransportAlgebraicCurvatureTensorCLEBetween_mem_curvatureOperatorNonnegativeCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a)) :
    parallelTransportAlgebraicCurvatureTensorCLEBetween
        (I := I) g gamma hgamma hab A ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
        A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
  algebraicCurvatureTensorPullbackCLE_mem_curvatureOperatorNonnegativeCone_iff
    (I := I) (M := M)
      (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm A

theorem algebraicCurvatureOperatorNonnegativeCone_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))).map
          (parallelTransportAlgebraicCurvatureTensorCLEBetween
            (I := I) g gamma hgamma hab).toContinuousLinearMap) =
      (algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b))) :=
  algebraicCurvatureOperatorNonnegativeCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm

theorem algebraicCurvatureOperatorNonnegative_dualZeroFace_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) {n : Nat}
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I (gamma a)) :
    (((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w)).map
              (parallelTransportAlgebraicCurvatureTensorCLEBetween
                (I := I) g gamma hgamma hab).toContinuousLinearMap) =
      ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b))).dualZeroFace
            (algebraicCurvatureOperatorQuadraticEvalCLM (I := I) (M := M) c
              (fun i => parallelTransportLinearEquivBetween
                (I := I) g gamma hgamma hab (v i))
              (fun i => parallelTransportLinearEquivBetween
                (I := I) g gamma hgamma hab (w i)))) := by
  let e := parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
  change (((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w)).map
              (algebraicCurvatureTensorPullbackCLE
                (I := I) (M := M) e.symm).toContinuousLinearMap) =
    ((algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b))).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM (I := I) (M := M) c
            (fun i => e (v i)) (fun i => e (w i))))
  simpa using algebraicCurvatureOperatorNonnegative_dualZeroFace_map_pullback
    (I := I) (M := M) e.symm c (fun i => e (v i)) (fun i => e (w i))

theorem parallelTransportAlgebraicCurvatureTensorCLEBetween_mem_curvatureOperatorDualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))
    (c : Fin n → Real)
    (v w : Fin n → TangentSpace I (gamma a)) :
    parallelTransportAlgebraicCurvatureTensorCLEBetween
        (I := I) g gamma hgamma hab A ∈
      (algebraicCurvatureOperatorNonnegativeCone
        (I := I) (M := M)).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM (I := I) (M := M) c
            (fun i => parallelTransportLinearEquivBetween
              (I := I) g gamma hgamma hab (v i))
            (fun i => parallelTransportLinearEquivBetween
              (I := I) g gamma hgamma hab (w i))) ↔
      A ∈ (algebraicCurvatureOperatorNonnegativeCone
        (I := I) (M := M)).dualZeroFace
          (algebraicCurvatureOperatorQuadraticEvalCLM
            (I := I) (M := M) c v w) := by
  rw [mem_algebraicCurvatureOperatorNonnegative_dualZeroFace,
    mem_algebraicCurvatureOperatorNonnegative_dualZeroFace]
  rw [parallelTransportAlgebraicCurvatureTensorCLEBetween_mem_curvatureOperatorNonnegativeCone_iff]
  rw [parallelTransportAlgebraicCurvatureTensorCLEBetween_curvatureOperatorQuadraticEval]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
