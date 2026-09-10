import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomials
import DifferentialGeometry.Geometry.Metric.Variation.TimeDerivative

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

theorem exists_mixed_curvature_jet_polynomials (n p q : ℕ) :
    ∃ P : (Fin (4 + p) → Fin n) →
        MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ,
      ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [CompleteSpace E]
        {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        [I.Boundaryless]
        {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
        [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn S → ∀ t ∈ D.regular, ∀ x : M,
        ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
          DifferentiableAt ℝ
            (iteratedMetricTimeDerivWithin S.base.metric D.carrier
              (fun s => nablaKRm04Field S s p x) q) t ∧
          ∀ slots : Fin (4 + p) → Fin n,
            component0S (I := I) basis
              (iteratedMetricTimeDerivWithin S.base.metric D.carrier
                (fun s => nablaKRm04Field S s p x) q t) slots =
              MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis)
                (P slots) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
