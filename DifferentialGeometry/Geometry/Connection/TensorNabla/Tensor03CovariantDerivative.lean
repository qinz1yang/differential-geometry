import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03Tensoriality
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

noncomputable local instance covariantDerivativeModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance covariantDerivativeModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance covariantDerivativeModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance covariantDerivativeModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance covariantDerivativeTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance covariantDerivativeTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance covariantDerivativeTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance covariantDerivativeTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (covariantDerivativeTangentTrilinearNormedAddCommGroup x).toAddCommGroup

local instance covariantDerivativeTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    covariantDerivativeTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    covariantDerivativeTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

local instance covariantDerivativeTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (covariantDerivativeTangentTrilinearModule
    x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

local instance covariantDerivativeTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    covariantDerivativeTangentTrilinearNormedAddCommGroup x
  infer_instance

noncomputable local instance covariantDerivativeTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance covariantDerivativeTensor01TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance covariantDerivativeTensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance covariantDerivativeTensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

local instance covariantDerivativeTensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance covariantDerivativeTensor02TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance covariantDerivativeIteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance covariantDerivativeIteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

local instance covariantDerivativeIteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance covariantDerivativeTensor03TotalSpaceTopology :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance covariantDerivativeTensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance covariantDerivativeTensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

local instance covariantDerivativeTensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

private lemma tensor03CovFun_add_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x)
    (v y z w : TangentSpace I x) :
    tensor03CovFun cov (T + T') x v y z w =
      tensor03CovFun cov T x v y z w + tensor03CovFun cov T' x v y z w := by
    classical
    have hT_t : MDiffAtTensor03 T x := hT
    have hT'_t : MDiffAtTensor03 T' x := hT'
    have hsum_T : MDiffAtTensor03 (T + T') x := mdifferentiableAt_add_section hT hT'
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    have hWx : W x = w := by simp [W]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [tensor03CovFun_apply, tensor03CovFun_apply, tensor03CovFun_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hsum_T hX hY hZ hW,
        tensor03CovAt_apply_of_diff_extend cov hT_t hX hY hZ hW,
        tensor03CovAt_apply_of_diff_extend cov hT'_t hX hY hZ hW]
    change extDerivFun (I := I) (fun b => (T + T') b (Y b) (Z b) (W b)) x (X x)
        - (T + T') x (cov.toFun Y x (X x)) (Z x) (W x)
        - (T + T') x (Y x) (cov.toFun Z x (X x)) (W x)
        - (T + T') x (Y x) (Z x) (cov.toFun W x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T' b (Y b) (Z b) (W b)) x (X x)
        - T' x (cov.toFun Y x (X x)) (Z x) (W x)
        - T' x (Y x) (cov.toFun Z x (X x)) (W x)
        - T' x (Y x) (Z x) (cov.toFun W x (X x)))
    have hpair_T : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT_t hY hZ hW
    have hpair_T' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T' b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT'_t hY hZ hW
    have hpair_eq : (fun b : M => (T + T') b (Y b) (Z b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) +
          (fun b : M => T' b (Y b) (Z b) (W b)) := by
      funext b
      simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    have hext_add : extDerivFun (I := I) (fun b => (T + T') b (Y b) (Z b) (W b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T' b (Y b) (Z b) (W b)) x := by
      rw [hpair_eq, extDerivFun_add hpair_T hpair_T']
    rw [hext_add]
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    ring

private lemma tensor03CovFun_add
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    tensor03CovFun cov (T + T') x =
      tensor03CovFun cov T x + tensor03CovFun cov T' x := by
  ext v y z w
  exact tensor03CovFun_add_apply cov hT hT' v y z w

private lemma tensor03CovFun_leibniz_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {g : M → ℝ} {x : M} (hT : MDiffAtTensor03 T x) (hg : MDiffAt g x)
    (v y z w : TangentSpace I x) :
    tensor03CovFun cov (g • T) x v y z w =
      g x • tensor03CovFun cov T x v y z w + extDerivFun g x v • T x y z w := by
    classical
    have hT_t : MDiffAtTensor03 T x := hT
    have hsum_T : MDiffAtTensor03 (g • T) x := hg.smul_section hT
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    have hWx : W x = w := by simp [W]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [tensor03CovFun_apply, tensor03CovFun_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hsum_T hX hY hZ hW]
    rw [tensor03CovAt_apply_of_diff_extend cov hT_t hX hY hZ hW]
    change extDerivFun (I := I) (fun b => (g • T) b (Y b) (Z b) (W b)) x (X x)
        - (g • T) x (cov.toFun Y x (X x)) (Z x) (W x)
        - (g • T) x (Y x) (cov.toFun Z x (X x)) (W x)
        - (g • T) x (Y x) (Z x) (cov.toFun W x (X x)) =
      g x • (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      extDerivFun (I := I) g x (X x) • T x (Y x) (Z x) (W x)
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT_t hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hpair_eq : (fun b : M => (g • T) b (Y b) (Z b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      simp only [Pi.smul_apply', ContinuousLinearMap.smul_apply, smul_eq_mul, hh_def]
    rw [hpair_eq, extDerivFun_mul_apply hg' hh]
    simp only [Pi.smul_apply', ContinuousLinearMap.smul_apply]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring

private lemma tensor03CovFun_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {g : M → ℝ} {x : M} (hT : MDiffAtTensor03 T x) (hg : MDiffAt g x) :
    tensor03CovFun cov (g • T) x =
      g x • tensor03CovFun cov T x + (extDerivFun g x).smulRight (T x) := by
  ext v y z w
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply] using tensor03CovFun_leibniz_apply cov hT hg v y z w

lemma tensor03CovFun_isCovariantDerivativeOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (V := (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (tensor03CovFun cov) Set.univ where
  add hT hT' _hx := tensor03CovFun_add cov hT hT'
  leibniz hT hg _hx := tensor03CovFun_leibniz cov hT hg

def tensor03Cov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun := tensor03CovFun cov
  isCovariantDerivativeOnUniv := tensor03CovFun_isCovariantDerivativeOn cov

lemma tensor03Cov_toFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (tensor03Cov cov).toFun = tensor03CovFun cov := rfl

end Connection
end Geometry
end DifferentialGeometry

end

