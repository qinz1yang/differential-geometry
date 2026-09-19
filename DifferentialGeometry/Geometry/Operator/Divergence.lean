import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import DifferentialGeometry.Bundle.Hom.Trace
import DifferentialGeometry.Geometry.Connection.ConnectionForm
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem divergence_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (divergence (I := I) cov X) := by
  apply contMDiff_linearMap_trace (F := E) (V := TangentSpace I)
  rw [← contMDiffOn_univ]
  exact hcov.contMDiff.contMDiff X.contMDiff.contMDiffOn

omit [CompleteSpace E] in
theorem divergence_contMDiffAt_partial [T2Space M]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {X : P → ∀ x : M, TangentSpace I x} {p : P × M} {m : ℕ∞} {n : ℕ∞ω}
    (hX : ContMDiffAt (IP.prod I) I.tangent n
      (fun q => (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)) p)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) :
    ContMDiffAt (IP.prod I) 𝓘(ℝ) m (fun q => divergence cov (X q.1) q.2) p :=
  (hcov.contMDiffAt_partial hX hmn).trace_bundle

theorem leviCivita_divergence_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞
      (divergence (I := I)
        (Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g) X) :=
  divergence_contMDiff
    (Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g)
    (Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
      (I := I) g) X

end Operator
end Geometry
end DifferentialGeometry
