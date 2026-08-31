import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
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

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegSpeedSq_nonneg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : 0 ≤ lRegSpeedSq S T alpha s := by
  unfold lRegSpeedSq
  by_cases hzero : lVelocity (I := I) alpha s = 0
  · rw [hzero]
    simp
  · exact ((S.base.metric (T - s ^ 2)).pos (alpha s) _ hzero).le

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_add
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b c : Real)
    (hab : IntervalIntegrable (lRegLagrangian S T alpha) volume a b)
    (hbc : IntervalIntegrable (lRegLagrangian S T alpha) volume b c) :
    lRegAction S T alpha a b + lRegAction S T alpha b c =
      lRegAction S T alpha a c := by
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_sum
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) {t : ℕ → Real} {n : ℕ}
    (hint : ∀ k < n,
      IntervalIntegrable (lRegLagrangian S T alpha) volume (t k) (t (k + 1))) :
    (∑ k ∈ Finset.range n, lRegAction S T alpha (t k) (t (k + 1))) =
      lRegAction S T alpha (t 0) (t n) := by
  exact intervalIntegral.sum_integral_adjacent_intervals hint

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_congr
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha beta : Real → M) (a b : Real)
    (h : Set.EqOn alpha beta (Set.uIoo a b)) :
    lRegAction S T alpha a b = lRegAction S T beta a b := by
  unfold lRegAction
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (max a b)]
      with s hsmax hs
  change s ∈ Set.Ioc (min a b) (max a b) at hs
  have hsIoo : s ∈ Set.Ioo (min a b) (max a b) :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hsmax⟩
  have hev : alpha =ᶠ[𝓝 s] beta := by
    filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
    exact h (by simpa only [Set.uIoo] using hr)
  have hval : alpha s = beta s := hev.self_of_nhds
  have hmf :
      mfderiv 𝓘(Real, Real) I alpha s =
        mfderiv 𝓘(Real, Real) I beta s :=
    Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) hev
  have hvel : lVelocity (I := I) alpha s = lVelocity (I := I) beta s := by
    with_unfolding_all exact
      (congrArg (fun L => L (1 : Real)) hmf)
  simp only [lRegLagrangian]
  rw [hval, hvel]


end DifferentialGeometry.PDE.RicciFlow.Perelman
