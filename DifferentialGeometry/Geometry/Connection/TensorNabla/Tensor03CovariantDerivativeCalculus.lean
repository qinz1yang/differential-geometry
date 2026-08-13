import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03CovariantDerivative
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

noncomputable local instance tensor03CalculusModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensor03CalculusModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensor03CalculusModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensor03CalculusModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensor03CalculusTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensor03CalculusTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensor03CalculusTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance tensor03CalculusTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tensor03CalculusTangentTrilinearNormedAddCommGroup x).toAddCommGroup

local instance tensor03CalculusTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensor03CalculusTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensor03CalculusTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

local instance tensor03CalculusTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tensor03CalculusTangentTrilinearModule x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

local instance tensor03CalculusTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensor03CalculusTangentTrilinearNormedAddCommGroup x
  infer_instance

local instance tensor03CalculusSectionAddCommGroup :
    AddCommGroup
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.addCommGroup

local instance tensor03CalculusSectionModule :
    Module ℝ
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.module M _ ℝ

noncomputable local instance tensor03CalculusTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance tensor03CalculusTensor01TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance tensor03CalculusTensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance tensor03CalculusTensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance tensor03CalculusTensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance tensor03CalculusTensor02TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance tensor03CalculusIteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance tensor03CalculusIteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance tensor03CalculusIteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance tensor03CalculusTensor03TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance tensor03CalculusTensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance tensor03CalculusTensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance tensor03CalculusTensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

theorem tensor03Cov_pairing
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x)
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x)
    (v : TangentSpace I x) :
    extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x v =
      ((tensor03Cov cov).toFun T x v) (Y x) (Z x) (W x)
        + T x (cov.toFun Y x v) (Z x) (W x)
        + T x (Y x) (cov.toFun Z x v) (W x)
        + T x (Y x) (Z x) (cov.toFun W x v) := by
  classical
  set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
  have hXx : X x = v := by simp [X]
  rw [show v = X x from hXx.symm]
  rw [tensor03Cov_toFun, tensor03CovFun_apply,
      tensor03CovAt_apply_of_diff_extend cov hT hX hY hZ hW]
  unfold tensor03Scalar
  ring

def tensor02CovIterate
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  fun T => (tensor03Cov cov).toFun ((tensor02Cov cov).toFun T)

@[simp] lemma tensor02CovIterate_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    tensor02CovIterate cov T x =
      (tensor03Cov cov).toFun ((tensor02Cov cov).toFun T) x := rfl

theorem tensor03Cov_add
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    (tensor03Cov cov).toFun (T + T') x =
      (tensor03Cov cov).toFun T x + (tensor03Cov cov).toFun T' x := by
  set D := tensor03Cov cov
  exact D.isCovariantDerivativeOnUniv.add hT hT' (Set.mem_univ x)

theorem tensor03Cov_smul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (a : ℝ) (hT : MDiffAtTensor03 T x) :
    (tensor03Cov cov).toFun (a • T) x = a • (tensor03Cov cov).toFun T x := by
  set D := tensor03Cov cov
  exact D.isCovariantDerivativeOnUniv.smul_const a hT (Set.mem_univ x)

theorem tensor03Cov_sub
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    (tensor03Cov cov).toFun (T - T') x =
      (tensor03Cov cov).toFun T x - (tensor03Cov cov).toFun T' x := by
  have hT'neg : MDiffAtTensor03 (-T') x := mdifferentiableAt_neg_section hT'
  have hneg : (tensor03Cov cov).toFun (-T') x = -(tensor03Cov cov).toFun T' x := by
    simpa only [neg_one_smul] using tensor03Cov_smul cov (-1) hT'
  rw [sub_eq_add_neg, tensor03Cov_add cov hT hT'neg, hneg, sub_eq_add_neg]

end Connection
end Geometry
end DifferentialGeometry

end
