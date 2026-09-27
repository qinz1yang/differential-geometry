import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.UniformMetricTimeLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

universe u

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]

theorem exists_metricDerivNorm_time_lipschitz_of_curvature_bound_on_open
    (p : ℕ) {T T₂ r K : ℝ} (hT : 0 < T) (hTT : T < T₂) (hr : 0 < r) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
      (g : ℝ → SmoothRiemannianMetric I M),
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed (-(2 * T₂)) 0
          (neg_nonpos.mpr (mul_nonneg zero_le_two (hT.le.trans hTT.le))))) →
      (∀ s ∈ Icc (-(2 * T₂)) 0, ∀ x : M, curvDerivNormSq 0 (g s) x ≤ K ^ 2) →
      ∀ U : Opens M, (∀ x ∈ U, IsCompact (riemannianClosedBallOf (g 0) x r)) →
      ∀ σ ∈ Icc (-T) 0, ∀ σ' ∈ Icc (-T) 0, ∀ x ∈ U, ∀ a ≤ p,
        metricDerivNorm a (g σ) (g σ') (g 0) x ≤ L * |σ - σ'| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let K' := |K| + 1
  have hK' : 0 < K' := by positivity
  let a₀ : ℝ := -(2 * T₂)
  let B : ℕ → ℝ := fun m =>
    shiLocalUniformBound (Module.finrank ℝ E) m (K' * ((0 - a₀) / 4))
      ((r / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K' * (0 - a₀)))) * Real.sqrt K' /
        (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K' * ((0 - a₀) / 4)))) *
      K' / Real.sqrt ((0 - a₀) / 4) ^ m
  obtain ⟨L, hL, hG⟩ :=
    exists_metricDerivNorm_terminal_reference_time_lipschitz_of_curvature_jets.{u} (I := I)
      p hT hTT B
  refine ⟨L, hL, ?_⟩
  intro M _ _ _ _ _ g hS hK U hU σ hσ σ' hσ' x hx a ha
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hKK : K ^ 2 ≤ K' ^ 2 := by
    rw [← sq_abs K]
    exact pow_le_pow_left₀ (abs_nonneg K) (by linarith) 2
  let D₂ := RealTimeInterval.closed (-(2 * T₂)) 0
    (neg_nonpos.mpr (mul_nonneg zero_le_two (hT.le.trans hTT.le)))
  let S₂ : SolutionOn (I := I) (M := M) D₂ := { base.metric := g }
  let D₁ := RealTimeInterval.closed (-T₂) 0 (neg_nonpos.mpr (hT.le.trans hTT.le))
  have hS₁ : IsSolutionOn (S₂.timeRestrict D₁) :=
    isSolutionOn_timeRestrict hS (fun v hv => ⟨by linarith [hv.1], hv.2⟩)
      (fun v hv => ⟨by linarith [hv.1], hv.2⟩)
  have hSU : IsSolutionOn (solutionOnRestrictOpen (S₂.timeRestrict D₁) U) :=
    isSolutionOn_restrictOpen _ hS₁ U
  have hjets : ∀ m ≤ p, ∀ s ∈ Icc (-T) 0, ∀ y : U,
      curvDerivNorm m ((g s).restrictOpen U) y ≤ B m := by
    intro m _ s hs y
    rw [curvDerivNorm_restrictOpen]
    exact shi_curvDerivNorm_on_terminal_ball S₂ hS (a := a₀) (b := 0) (K := K') (R := r)
      (by dsimp only [a₀]; linarith) hK' hr (fun v hv => hv) (fun v hv => hv) (y : M)
      (hU y y.2) (fun t ht z _ => (hK t ht z).trans hKK) m s
      ⟨by dsimp only [a₀]; linarith [hs.1], hs.2⟩ (y : M)
      (by rw [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self]; exact bot_le)
  have h := hG (fun t => (g t).restrictOpen U) hSU hjets σ hσ σ' hσ' ⟨x, hx⟩ a ha
  rwa [metricDerivNorm_restrictOpen] at h

end DifferentialGeometry.PDE.RicciFlow
