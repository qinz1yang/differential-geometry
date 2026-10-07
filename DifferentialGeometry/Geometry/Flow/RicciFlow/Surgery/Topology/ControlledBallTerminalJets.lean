import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.LocalPullTerminalBall

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

/-- An actual controlled terminal ball supplies normalized spatial jets,
uniformly before the history, normalization scale and terminal point are chosen. -/
private theorem exists_normalized_terminal_jets_of_controlled_test_ball
    (b : ℝ) (hb : 0 < b) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (H : ObservedHistory.{u}) (s : Icc (0 : ℝ) H.horizon)
        (z : (H.stageAt s).Carrier) (Q : ℝ) (hQ : 0 < Q),
        H.isParabolicallyRmControlledBall s z (b / Real.sqrt Q) →
        ∀ m : ℕ,
          curvDerivNorm m
            (scaleMetric Q hQ (H.stageMetric (H.activeStage s) s)) z ≤ D m := by
  let B (m : ℕ) : ℝ :=
    shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m ((b ^ 2)⁻¹ * (b ^ 2 / 4))
      ((((b / 2) / 2) /
          (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (b ^ 2)⁻¹ * b ^ 2))) *
        Real.sqrt ((b ^ 2)⁻¹) /
          (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
            (b ^ 2)⁻¹ * (b ^ 2 / 4)))) *
      (b ^ 2)⁻¹ / Real.sqrt (b ^ 2 / 4) ^ m
  refine ⟨fun m => max 0 (B m), fun m => le_max_left _ _, ?_⟩
  intro H s z Q hQ htest
  obtain ⟨a, has, ha, U, hU, _f, _hf, _hinj, _hcross, _hlast,
      S, hS, _hmetric, hRm, hterminal, _⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall
      s z (b / Real.sqrt Q) htest
  letI : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hclock : (a : ℝ) = (s : ℝ) - b ^ 2 / Q := by
    simpa only [div_pow, Real.sq_sqrt hQ.le] using ha
  have hcarrier : Icc ((s : ℝ) - b ^ 2 / Q) s ⊆
      (RealTimeInterval.closed (a : ℝ) s has).carrier := by
    change Icc ((s : ℝ) - b ^ 2 / Q) s ⊆ Icc (a : ℝ) s
    rw [hclock]
  have hregular : Ioo ((s : ℝ) - b ^ 2 / Q) s ⊆
      (RealTimeInterval.closed (a : ℝ) s has).regular := by
    change Ioo ((s : ℝ) - b ^ 2 / Q) s ⊆ Ioo (a : ℝ) s
    rw [hclock]
  have hpull : S.base.metric s =
      localPullMetric (H.stageMetric (H.activeStage s) s) (Subtype.val : U → _)
        (isLocalDiffeomorph_subtype_val U) := by
    rw [localPullMetric_subtype_val]
    exact hterminal
  have hcompact : IsCompact (riemannianClosedBallOf
      (H.stageMetric (H.activeStage s) s) z ((b / 2) / Real.sqrt Q)) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
  have hball : riemannianBallOf (H.stageMetric (H.activeStage s) s) z
      ((b / 2) / Real.sqrt Q) ⊆ Set.range (Subtype.val : U → _) := by
    rw [Subtype.range_coe, hU]
    exact riemannianBallOf_mono _ _
      (div_le_div_of_nonneg_right (by linarith : b / 2 ≤ b) (Real.sqrt_nonneg Q))
  have hcurv : ∀ t ∈ Icc ((s : ℝ) - b ^ 2 / Q) s, ∀ x : U,
      (x : (H.stageAt s).Carrier) ∈ riemannianClosedBallOf
        (H.stageMetric (H.activeStage s) s) z ((b / 2) / Real.sqrt Q) →
      curvDerivNormSq 0 (S.base.metric t) x ≤ ((b ^ 2)⁻¹ * Q) ^ 2 := by
    intro t ht x _hx
    have ht' : t ∈ Icc (a : ℝ) s := by simpa only [hclock] using ht
    have hn := hRm t ht' x
    change (b / Real.sqrt Q) ^ 4 * curvDerivNormSq 0 (S.base.metric t) x ≤ 1 at hn
    have hsqrt : Real.sqrt Q ^ 4 = Q ^ 2 := by
      calc
        Real.sqrt Q ^ 4 = (Real.sqrt Q ^ 2) ^ 2 := by ring
        _ = Q ^ 2 := by rw [Real.sq_sqrt hQ.le]
    rw [div_pow, hsqrt, div_mul_eq_mul_div] at hn
    have hmul : b ^ 4 * curvDerivNormSq 0 (S.base.metric t) x ≤ Q ^ 2 := by
      simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos hQ)).mp hn
    calc
      curvDerivNormSq 0 (S.base.metric t) x ≤ Q ^ 2 / b ^ 4 :=
        (le_div_iff₀ (pow_pos hb 4)).mpr (by simpa only [mul_comm] using hmul)
      _ = ((b ^ 2)⁻¹ * Q) ^ 2 := by
        simp [mul_pow, inv_pow, ← pow_mul, div_eq_mul_inv, mul_comm]
  have hshi := shi_curvDerivNorm_scaleMetric_of_localPullMetric_terminal
    S hS (H.stageMetric (H.activeStage s) s) (Subtype.val : U → _)
    (isLocalDiffeomorph_subtype_val U) Subtype.val_injective
    (T := (s : ℝ)) (Q := Q) (θ := b ^ 2) (K := (b ^ 2)⁻¹) (r := b / 2)
    hQ (sq_pos_of_pos hb) (inv_pos.mpr (sq_pos_of_pos hb)) (half_pos hb)
    hcarrier hregular hpull z hcompact hball hcurv
  intro m
  exact (hshi m).trans (le_max_right 0 (B m))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
