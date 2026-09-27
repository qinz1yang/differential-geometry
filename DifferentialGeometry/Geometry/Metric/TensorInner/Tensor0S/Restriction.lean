import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem normSq0S_restrictOpen_apply
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (s : Nat) (x : U)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := U) s x) :
    Tensor0SBundle.normSq0S (I := I) (M := U) (g.restrictOpen (I := I) U) x s A =
      Tensor0SBundle.normSq0S (I := I) (M := M) g (x : M) s A := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (M := M) g (x : M)
  have hONU :
      ∀ i j,
        (g.restrictOpen (I := I) U).inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0 := by
    intro i j
    exact hON i j
  have hinvU :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := U)
        (g.restrictOpen (I := I) U) x basis
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' :=
      DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
        (I := I) (M := U) (g.restrictOpen (I := I) U) basis hONU
    change Tensor0SBundle.MetricInverseInBasis (I := I) (M := U)
      (g.restrictOpen (I := I) U) x basis
        (fun a k => if a = k then (1 : Real) else 0)
    exact h'
  have hinvM :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := M)
        g (x : M) basis
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    change Tensor0SBundle.MetricInverseInBasis (I := I) (M := M)
      g (x : M) basis (fun a k => if a = k then (1 : Real) else 0)
    exact h'
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (M := U) (g.restrictOpen (I := I) U) x s basis hinvU A,
    Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (M := M) g (x : M) s basis hinvM A]
  rfl

end FixedManifold

end CheegerGromovCompactness
end DifferentialGeometry
