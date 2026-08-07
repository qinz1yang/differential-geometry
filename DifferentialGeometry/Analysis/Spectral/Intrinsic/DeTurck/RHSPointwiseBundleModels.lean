import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorExtension
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03CovariantDerivativeCalculus
import DifferentialGeometry.Tensor.Multilinear.FiniteCurryNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RicciDiffAffine
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
















































noncomputable section


open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Sobolev.HebeyBlock
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

noncomputable local instance rhsPointwiseModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rhsPointwiseModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rhsPointwiseModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rhsPointwiseModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rhsPointwiseTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rhsPointwiseTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rhsPointwiseTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance rhsPointwiseTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (rhsPointwiseTangentTrilinearNormedAddCommGroup x).toAddCommGroup

local instance rhsPointwiseTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

local instance rhsPointwiseTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (rhsPointwiseTangentTrilinearModule x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

local instance rhsPointwiseTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentTrilinearNormedAddCommGroup x
  infer_instance

local instance rhsPointwiseSectionAddCommGroup :
    AddCommGroup
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.addCommGroup

local instance rhsPointwiseSectionModule :
    Module ℝ
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.module M _ ℝ

noncomputable local instance rhsPointwiseTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rhsPointwiseTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance rhsPointwiseTangentQuadrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  (rhsPointwiseTangentQuadrilinearNormedAddCommGroup x).toAddCommGroup

local instance rhsPointwiseTangentQuadrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentQuadrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentQuadrilinearNormedSpace x
  exact NormedSpace.toModule

local instance rhsPointwiseTangentBilinearAddCommGroup (x : M) :
    AddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (rhsPointwiseTangentBilinearNormedAddCommGroup x).toAddCommGroup

local instance rhsPointwiseTangentBilinearModule (x : M) :
    Module ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentBilinearNormedAddCommGroup x
  letI : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    rhsPointwiseTangentBilinearNormedSpace x
  exact NormedSpace.toModule

local instance rhsPointwiseBilinearSectionAddCommGroup :
    AddCommGroup (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.addCommGroup

local instance rhsPointwiseBilinearSectionModule :
    Module ℝ (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.module M _ ℝ

local instance rhsPointwiseTensor0SModelNormedAddCommGroup {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.instNormedAddCommGroupTensor0SModel s

local instance rhsPointwiseTensor0SModelNormedSpace {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

local instance rhsPointwiseTensorRSModelNormedAddCommGroup {r s : ℕ} :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

local instance rhsPointwiseTensorRSModelNormedSpace {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

local instance rhsPointwiseTensor01TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance rhsPointwiseTensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance rhsPointwiseTensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance rhsPointwiseTensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance rhsPointwiseTensor02TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseIteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseIteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseIteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance rhsPointwiseTensor03TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseTensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseTensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseTensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance rhsPointwiseTensor04TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseTensor04FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseTensor04VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ)

local instance rhsPointwiseTensor04ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance rhsPointwiseTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundle_topology r s

local instance rhsPointwiseTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundle_fiber r s

end Spectral
end Analysis
end DifferentialGeometry

end
