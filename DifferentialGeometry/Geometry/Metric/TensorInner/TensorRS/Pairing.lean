import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

noncomputable def unitZeroSec :
    Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
  ⟨fun _ : M => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
    contMDiff_unitZeroSection (I := I) (M := M)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
@[simp] lemma unitZeroSec_apply (y : M) :
    unitZeroSec (I := I) (M := M) y =
      Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold
open _root_.DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem lowerZero_unit (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W : TensorRSSpace 0 s I x) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) =
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) (1 : Real)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x W (unitZeroSec (I := I) (M := M) x)]
  rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem innerPtDiag (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W : TensorRSSpace 0 s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) =
      normSq0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W)) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  rw [lowerZero_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem innerPt_eq_inner0S (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W₁ W₂ : TensorRSSpace 0 s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W₁) (TensorRSSpace.toModel W₂) =
      inner0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁)
          (unitZeroSec (I := I) (M := M) x))
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₂)
          (unitZeroSec (I := I) (M := M) x)) := by
  have hunit :
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁ + W₂)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁)
            (unitZeroSec (I := I) (M := M) x) +
          (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₂)
            (unitZeroSec (I := I) (M := M) x) := rfl
  have h := innerPtDiag (I := I) g s x (W₁ + W₂)
  rw [TensorRSSpace.toModel_add, hunit, normSq0S_add,
    tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right,
    innerPtDiag (I := I) g s x W₁, innerPtDiag (I := I) g s x W₂,
    tensorInnerPointwise_symm (I := I) (M := M) g 0 s x
      (TensorRSSpace.toModel W₂) (TensorRSSpace.toModel W₁)] at h
  linarith

end DifferentialGeometry.PDE.RicciFlow
