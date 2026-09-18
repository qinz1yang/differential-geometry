import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorCovariantDerivative
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.OpenRestriction

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance tensorLocalityC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance tensorLocalityC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance tensorLocalityRestrictedC1 (U : TopologicalSpace.Opens M) :
    IsManifold I 1 U := IsManifold.of_le (n := ∞) (by decide)
private local instance tensorLocalityRestrictedC2 (U : TopologicalSpace.Opens M) :
    IsManifold I 2 U := IsManifold.of_le (n := ∞) (by decide)

theorem tensor02CovDerivNormWith_eq_of_eventuallyEq
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : M)
    (hAB : ∀ᶠ y in 𝓝 x, A y = B y) :
    tensor02CovDerivNormWith a A gcov gnorm x =
      tensor02CovDerivNormWith a B gcov gnorm x := by
  obtain ⟨V, hV, hopen, hx⟩ := mem_nhds_iff.mp hAB
  let U : TopologicalSpace.Opens M := ⟨V, hopen⟩
  have heq : restrictOpen0S (I := I) 2 (V := U) A =
      restrictOpen0S (I := I) 2 (V := U) B := by
    ext y v
    exact congrArg (fun T => T v) (hV y.property)
  have hA := covDerivOfField_restrictOpen gcov U
    (restrictOpen0S (I := I) 2 (V := U) A) A (fun _ _ => rfl) a ⟨x, hx⟩
  have hB := covDerivOfField_restrictOpen gcov U
    (restrictOpen0S (I := I) 2 (V := U) B) B (fun _ _ => rfl) a ⟨x, hx⟩
  have hderiv : covDerivOfField gcov A a x = covDerivOfField gcov B a x := by
    ext v
    rw [← hA v, ← hB v, heq]
  unfold tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field,
    hderiv]

end DifferentialGeometry.CheegerGromovCompactness
