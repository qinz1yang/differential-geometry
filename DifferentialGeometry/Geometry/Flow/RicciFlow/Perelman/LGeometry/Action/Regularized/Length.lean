import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedDensity_eq_lRegularizedLagrangian_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (s : Real) :
    lRegularizedDensity S T gamma s = lRegularizedLagrangian S T (squareReparametrization gamma) s := by
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_eq_lRegularizedAction_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (tau1 tau2 : Real)
    (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2)
    (hgamma : ∀ s ∈ Set.uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)) :
    lLength S T gamma tau1 tau2 =
      lRegularizedAction S T (squareReparametrization gamma)
        (Real.sqrt tau1) (Real.sqrt tau2) := by
  simpa only [lRegularizedAction, lRegularizedDensity_eq_lRegularizedLagrangian_squareReparametrization] using
    lLength_squareReparametrization (I := I) S T gamma tau1 tau2 htau1 htau2 hgamma

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_eq_lRegularizedAction_squareReparametrization_ae
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (tau1 tau2 : Real)
    (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2) :
    lLength S T gamma tau1 tau2 =
      lRegularizedAction S T (squareReparametrization gamma)
        (Real.sqrt tau1) (Real.sqrt tau2) := by
  simpa only [lRegularizedAction, lRegularizedDensity_eq_lRegularizedLagrangian_squareReparametrization] using
    lLength_squareReparametrization_ae (I := I) S T gamma tau1 tau2 htau1 htau2

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_squareRootReparametrization_eq_lRegularizedAction
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (tau : Real) (htau : 0 ≤ tau) :
    lLength S T (squareRootReparametrization alpha) 0 tau =
      lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
  have hsq := lLength_eq_lRegularizedAction_squareReparametrization_ae (I := I) S T (squareRootReparametrization alpha)
    0 tau (by norm_num) htau
  have hsq' : lLength S T (squareRootReparametrization alpha) 0 tau =
      lRegularizedAction S T (squareReparametrization (squareRootReparametrization alpha)) 0
        (Real.sqrt tau) := by
    simpa only [Real.sqrt_zero] using hsq
  have hEq : Set.EqOn (squareReparametrization (squareRootReparametrization alpha)) alpha
      (Set.uIoo 0 (Real.sqrt tau)) := by
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (Real.sqrt tau) := by
      simpa only [Set.uIoo_of_le (Real.sqrt_nonneg tau)] using hs
    simp only [squareReparametrization, squareRootReparametrization, Real.sqrt_sq hs'.1.le]
  exact hsq'.trans
    (lRegularizedAction_congr (I := I) S T
      (squareReparametrization (squareRootReparametrization alpha)) alpha 0 (Real.sqrt tau) hEq)


end DifferentialGeometry.PDE.RicciFlow.Perelman
