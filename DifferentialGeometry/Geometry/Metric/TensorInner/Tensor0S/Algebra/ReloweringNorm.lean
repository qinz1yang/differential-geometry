import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Relowering
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.TraceBound
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.TensorProductNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem reLowerPairSq_le (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (x : M) :
    normSq0S (I := I) g x (s + 2) (reLowerPair (I := I) g T K x) ≤
      (Module.finrank Real E : Real) ^ (s + 4) *
        (normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hprod : normSq0S (I := I) g x (s + 1 + 3)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) =
      normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x) :=
    normSq0S_product (I := I) g x basis hinv T K
  have hcongr : normSq0S (I := I) g x (s + 1 + 3)
      (ContinuousMultilinearMap.domDomCongr (reLowerPermutationWithThreeInputs s)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x)) =
      normSq0S (I := I) g x (s + 1 + 3)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv (reLowerPermutationWithThreeInputs s) _
  have htr := traceNormSq_le (I := I) (s := s + 2) g x
    (ContinuousMultilinearMap.domDomCongr (reLowerPermutationWithThreeInputs s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x))
  rw [hcongr, hprod] at htr
  exact htr


end DifferentialGeometry.PDE.RicciFlow
