import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem kappaNoncollapsedBelowScale_of_kappa_le
    (S : SolutionOn (I := I) (M := M) D) {kappa kappa' rho : Real}
    (hkappa : 0 < kappa) (hle : kappa ≤ kappa')
    (h : KappaNoncollapsedBelowScale S kappa' rho) :
    KappaNoncollapsedBelowScale S kappa rho :=
  ⟨h.1, fun t B hr hB =>
    ⟨hkappa,
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl).trans (h.2 t B hr hB).2⟩⟩

theorem mul_pow_le_volume_toReal_of_kappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) {kappa rho : Real}
    (h : KappaNoncollapsedBelowScale S kappa rho) {t : D.FlowTime}
    (B : FlowMetricBall S t) (hr : B.radius ≤ rho) (hB : B.IsRmControlled)
    (hvol : B.volume ≠ ⊤) :
    kappa * B.radius ^ Module.finrank Real E ≤ (B.volume).toReal := by
  obtain ⟨hkappa, hle⟩ := h.2 t B hr hB
  have hmul : ENNReal.ofReal (kappa * B.radius ^ Module.finrank Real E) ≤ B.volume := by
    rw [ENNReal.ofReal_mul hkappa.le, ENNReal.ofReal_pow B.radius_pos.le]
    exact hle
  have hreal := ENNReal.toReal_mono hvol hmul
  simpa only [ENNReal.toReal_ofReal
    (mul_nonneg hkappa.le (pow_nonneg B.radius_pos.le _))] using hreal

end DifferentialGeometry.PDE.RicciFlow.Perelman
