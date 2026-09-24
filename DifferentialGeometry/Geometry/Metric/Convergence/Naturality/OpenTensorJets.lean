import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorCovariantDerivative
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.OpenRestriction


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance openTensorJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance openTensorJetsC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance openTensorJetsRestrictedC1 (U : TopologicalSpace.Opens M) : IsManifold I 1 U :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance openTensorJetsRestrictedC2 (U : TopologicalSpace.Opens M) : IsManifold I 2 U :=
  IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] [T2Space M] in
theorem restrictOpenTensor02Field_apply (U : TopologicalSpace.Opens M)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (x : U)
    (v : Fin 2 → TangentSpace I x) :
    restrictOpen0S (I := I) 2 (V := U) A x v = A (x : M) v := rfl


theorem tensor02CovDerivNormWith_restrictOpen0S (U : TopologicalSpace.Opens M)
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : U) :
    tensor02CovDerivNormWith a (restrictOpen0S (I := I) 2 (V := U) A)
        (gcov.restrictOpen U) (gnorm.restrictOpen U) x =
      tensor02CovDerivNormWith a A gcov gnorm (x : M) := by
  have htower := covDerivOfField_restrictOpen gcov U
    (restrictOpen0S (I := I) 2 (V := U) A) A
    (restrictOpenTensor02Field_apply U A) a x
  have htensor : covDerivOfField (gcov.restrictOpen U)
      (restrictOpen0S (I := I) 2 (V := U) A) a x = covDerivOfField gcov A a (x : M) :=
    ContinuousMultilinearMap.ext htower
  unfold tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field, htensor]
  congr 1
  exact normSq0S_restrictOpen_apply gnorm U (a + 2) x _

omit [CompleteSpace E] [T2Space M] in
theorem hasDerivWithinAt_restrictOpenTensor02Field (U : TopologicalSpace.Opens M)
    (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (A' : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    {times : Set ℝ} {t : ℝ} (x : U) (v : Fin 2 → TangentSpace I x)
    (hA : HasDerivWithinAt (fun s => A s (x : M) v) (A' (x : M) v) times t) :
    HasDerivWithinAt (fun s => restrictOpen0S (I := I) 2 (V := U) (A s) x v)
      (restrictOpen0S (I := I) 2 (V := U) A' x v) times t := hA

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
