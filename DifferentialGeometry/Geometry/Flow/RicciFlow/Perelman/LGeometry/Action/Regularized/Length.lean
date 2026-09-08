import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
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
theorem lLength_squareRootReparametrization_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lLength S T (squareRootReparametrization alpha) (a ^ 2) (b ^ 2) =
      lRegularizedAction S T alpha a b := by
  have hsq := lLength_eq_lRegularizedAction_squareReparametrization_ae
    (I := I) S T (squareRootReparametrization alpha)
    (a ^ 2) (b ^ 2) (sq_nonneg a) (sq_nonneg b)
  have hEq : Set.EqOn (squareReparametrization (squareRootReparametrization alpha))
      alpha (Set.uIoo a b) := by
    intro s hs
    have hs0 : 0 ≤ s := (le_min ha hb).trans hs.1.le
    simp only [squareReparametrization, squareRootReparametrization, Real.sqrt_sq hs0]
  calc
    _ = lRegularizedAction S T (squareReparametrization (squareRootReparametrization alpha))
        a b := by
      simpa only [Real.sqrt_sq ha, Real.sqrt_sq hb] using hsq
    _ = lRegularizedAction S T alpha a b :=
      lRegularizedAction_congr S T
        (squareReparametrization (squareRootReparametrization alpha)) alpha a b hEq

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_squareRootReparametrization_eq_lRegularizedAction
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (tau : Real) (htau : 0 ≤ tau) :
    lLength S T (squareRootReparametrization alpha) 0 tau =
      lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
  simpa only [zero_pow two_ne_zero, Real.sq_sqrt htau] using
    lLength_squareRootReparametrization_sq S T alpha 0 (Real.sqrt tau)
      le_rfl (Real.sqrt_nonneg tau)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem intervalIntegrable_lDensity_squareRootReparametrization_sq_iff
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (alpha : ℝ → M)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (lDensity S T (squareRootReparametrization alpha)) volume (a ^ 2) (b ^ 2) ↔
      IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b := by
  let gamma := squareRootReparametrization alpha
  have hChange := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := lDensity S T gamma) (f := fun s : ℝ => s ^ 2) (f' := fun s : ℝ => 2 * s)
    (a := a) (b := b) (continuous_id.pow 2).continuousOn
    (by intro s _; simpa using hasDerivAt_pow 2 s)
    (by intro s hs; exact mul_nonneg (by norm_num) ((le_min ha hb).trans hs.1.le))
  have hEq (s : ℝ) (hs : s ∈ uIoc a b) :
      (lDensity S T gamma ∘ fun r : ℝ => r ^ 2) s * (2 * s) =
        lRegularizedLagrangian S T alpha s := by
    have hsPos : 0 < s := (le_min ha hb).trans_lt hs.1
    rw [Function.comp_apply, lDensity_squareReparametrization_of_pos S T gamma s hsPos,
      lRegularizedDensity_eq_lRegularizedLagrangian_squareReparametrization]
    have hev : squareReparametrization gamma =ᶠ[𝓝 s] alpha := by
      filter_upwards [Ioi_mem_nhds hsPos] with r hr
      simp only [squareReparametrization, gamma, squareRootReparametrization, Real.sqrt_sq hr.le]
    have hval : squareReparametrization gamma s = alpha s := hev.self_of_nhds
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I) hev
    have hvel : lVelocity (I := I) (squareReparametrization gamma) s =
        lVelocity (I := I) alpha s := by
      with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
    simp only [lRegularizedLagrangian]
    rw [hval, hvel]
  constructor
  · intro h
    exact (hChange.mpr h).congr hEq
  · intro h
    exact hChange.mp (h.congr (fun s hs => (hEq s hs).symm))

end DifferentialGeometry.PDE.RicciFlow.Perelman
