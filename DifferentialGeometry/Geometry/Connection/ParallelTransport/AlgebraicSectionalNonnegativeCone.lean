import DifferentialGeometry.Geometry.Connection.ParallelTransport.SectionalNonnegativeCone
import DifferentialGeometry.Geometry.Curvature.AlgebraicSectionalCone

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

private local instance parallelAlgebraicTensor04NormedAddCommGroup (x : M) :
    NormedAddCommGroup (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 4 x

private local instance parallelAlgebraicTensor04NormedSpace (x : M) :
    NormedSpace Real (Tensor04At (I := I) (M := M) x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 4 x

private local instance parallelAlgebraicTensor04AddCommGroup (x : M) :
    AddCommGroup (Tensor04At (I := I) (M := M) x) :=
  @NormedAddCommGroup.toAddCommGroup _
    (parallelAlgebraicTensor04NormedAddCommGroup (I := I) x)

private local instance parallelAlgebraicTensor04Module (x : M) :
    Module Real (Tensor04At (I := I) (M := M) x) :=
  @NormedSpace.toModule _ _ _ _
    (parallelAlgebraicTensor04NormedSpace (I := I) x)

private local instance parallelAlgebraicTensor04TopologicalSpace (x : M) :
    TopologicalSpace (Tensor04At (I := I) (M := M) x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _
          (parallelAlgebraicTensor04NormedAddCommGroup (I := I) x))))

noncomputable def parallelTransportAlgebraicCurvatureTensorCLEOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0) ≃L[Real]
      algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L) :=
  algebraicCurvatureTensorPullbackCLE (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm

@[simp]
theorem parallelTransportAlgebraicCurvatureTensorCLEOnIcc_sectionalEval
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))
    (v w : TangentSpace I (gamma 0)) :
    tensor04SectionalEval (I := I) (M := M)
        ((parallelTransportAlgebraicCurvatureTensorCLEOnIcc
          (I := I) g gamma hgamma hL A :
            algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L)) :
          Tensor04At (I := I) (M := M) (gamma L))
        (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL v)
        (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL w) =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) (gamma 0)) v w := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL
  change tensor04SectionalEval (I := I) (M := M)
      ((algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L)) :
        Tensor04At (I := I) (M := M) (gamma L)) (e v) (e w) = _
  rw [algebraicSectionalEval_pullback]
  simp

theorem parallelTransportAlgebraicCurvatureTensorCLEOnIcc_mem_sectionalNonnegativeCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0)) :
    parallelTransportAlgebraicCurvatureTensorCLEOnIcc
        (I := I) g gamma hgamma hL A ∈
      algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
        A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) :=
  algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff
    (I := I) (M := M)
      (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm A

theorem algebraicSectionalNonnegativeCone_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) :
    ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))).map
          (parallelTransportAlgebraicCurvatureTensorCLEOnIcc
            (I := I) g gamma hgamma hL).toContinuousLinearMap) =
      (algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L))) :=
  algebraicSectionalNonnegativeCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL).symm

theorem algebraicSectionalNonnegative_dualZeroFace_map_parallelTransportOnIcc
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L) (v w : TangentSpace I (gamma 0)) :
    (((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) v w)).map
            (parallelTransportAlgebraicCurvatureTensorCLEOnIcc
              (I := I) g gamma hgamma hL).toContinuousLinearMap) =
      ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L))).dualZeroFace
            (algebraicSectionalEvalCLM (I := I) (M := M)
              (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL v)
              (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL w))) := by
  let e := parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL
  change (((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) v w)).map
            (algebraicCurvatureTensorPullbackCLE
              (I := I) (M := M) e.symm).toContinuousLinearMap) =
    ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma L))).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) (e v) (e w)))
  simpa using algebraicSectionalNonnegative_dualZeroFace_map_pullback
    (I := I) (M := M) e.symm (e v) (e w)

theorem parallelTransportAlgebraicCurvatureTensorCLEOnIcc_mem_dualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {L : Real} (hL : 0 < L)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma 0))
    (v w : TangentSpace I (gamma 0)) :
    parallelTransportAlgebraicCurvatureTensorCLEOnIcc
        (I := I) g gamma hgamma hL A ∈
      (algebraicSectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (algebraicSectionalEvalCLM (I := I) (M := M)
          (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL v)
          (parallelTransportLinearEquivOnIcc (I := I) g gamma hgamma hL w)) ↔
      A ∈ (algebraicSectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (algebraicSectionalEvalCLM (I := I) (M := M) v w) := by
  rw [mem_algebraicSectionalNonnegative_dualZeroFace,
    mem_algebraicSectionalNonnegative_dualZeroFace]
  rw [parallelTransportAlgebraicCurvatureTensorCLEOnIcc_mem_sectionalNonnegativeCone_iff]
  rw [parallelTransportAlgebraicCurvatureTensorCLEOnIcc_sectionalEval]

noncomputable def parallelTransportAlgebraicCurvatureTensorCLEBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a) ≃L[Real]
      algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b) :=
  algebraicCurvatureTensorPullbackCLE (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm

@[simp]
theorem parallelTransportAlgebraicCurvatureTensorCLEBetween_sectionalEval
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))
    (v w : TangentSpace I (gamma a)) :
    tensor04SectionalEval (I := I) (M := M)
        ((parallelTransportAlgebraicCurvatureTensorCLEBetween
          (I := I) g gamma hgamma hab A :
            algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b)) :
          Tensor04At (I := I) (M := M) (gamma b))
        (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab v)
        (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab w) =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) (gamma a)) v w := by
  let e := parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
  change tensor04SectionalEval (I := I) (M := M)
      ((algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b)) :
        Tensor04At (I := I) (M := M) (gamma b)) (e v) (e w) = _
  rw [algebraicSectionalEval_pullback]
  simp

theorem parallelTransportAlgebraicCurvatureTensorCLEBetween_mem_sectionalNonnegativeCone_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a)) :
    parallelTransportAlgebraicCurvatureTensorCLEBetween
        (I := I) g gamma hgamma hab A ∈
      algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
        A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) :=
  algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff
    (I := I) (M := M)
      (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm A

theorem algebraicSectionalNonnegativeCone_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) :
    ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))).map
          (parallelTransportAlgebraicCurvatureTensorCLEBetween
            (I := I) g gamma hgamma hab).toContinuousLinearMap) =
      (algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b))) :=
  algebraicSectionalNonnegativeCone_map_pullback (I := I) (M := M)
    (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab).symm

theorem algebraicSectionalNonnegative_dualZeroFace_map_parallelTransportBetween
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b) (v w : TangentSpace I (gamma a)) :
    (((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) v w)).map
            (parallelTransportAlgebraicCurvatureTensorCLEBetween
              (I := I) g gamma hgamma hab).toContinuousLinearMap) =
      ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b))).dualZeroFace
            (algebraicSectionalEvalCLM (I := I) (M := M)
              (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab v)
              (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab w))) := by
  let e := parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab
  change (((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) v w)).map
            (algebraicCurvatureTensorPullbackCLE
              (I := I) (M := M) e.symm).toContinuousLinearMap) =
    ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma b))).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) (e v) (e w)))
  simpa using algebraicSectionalNonnegative_dualZeroFace_map_pullback
    (I := I) (M := M) e.symm (e v) (e w)

theorem parallelTransportAlgebraicCurvatureTensorCLEBetween_mem_dualZeroFace_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) gamma)
    {a b : Real} (hab : a < b)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) (gamma a))
    (v w : TangentSpace I (gamma a)) :
    parallelTransportAlgebraicCurvatureTensorCLEBetween
        (I := I) g gamma hgamma hab A ∈
      (algebraicSectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (algebraicSectionalEvalCLM (I := I) (M := M)
          (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab v)
          (parallelTransportLinearEquivBetween (I := I) g gamma hgamma hab w)) ↔
      A ∈ (algebraicSectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (algebraicSectionalEvalCLM (I := I) (M := M) v w) := by
  rw [mem_algebraicSectionalNonnegative_dualZeroFace,
    mem_algebraicSectionalNonnegative_dualZeroFace]
  rw [parallelTransportAlgebraicCurvatureTensorCLEBetween_mem_sectionalNonnegativeCone_iff]
  rw [parallelTransportAlgebraicCurvatureTensorCLEBetween_sectionalEval]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
