import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Adapter
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open private shifted_tame_estimate from DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

abbrev GraphDoubledJetHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) (σ : ℝ) := PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g 0 0 σ)

noncomputable def graphDoubledJetInclusion
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    GraphDoubledJetHs g n 2 →L[ℝ] GraphDoubledJetHs g n 1 :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
    tensorHsInclusion (r := 0) (s := 0) (show (1 : ℝ) ≤ 2 by norm_num))

abbrev GraphDoubledJetState
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (R : ℝ) :=
  {u : GraphDoubledJetHs g n 2 | ‖graphDoubledJetInclusion g u‖ ≤ R}

theorem graphDoubledJet_tame_estimate
    {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {A Y : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]
      [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (m : A →L[ℝ] Y →L[ℝ] Y)
    (Q : GraphDoubledJetHs g n 2 →L[ℝ] Y)
    (D : GraphDoubledJetHs g n 1 →L[ℝ] Y)
    (c : Y) (d : Y →L[ℝ] Y) (q : A)
    (alpha : ℝ → GraphDoubledJetHs g n 1 → A)
    (reaction : ℝ → GraphDoubledJetHs g n 1 → Y)
    {R K L M : ℝ} (t : ℝ)
    (halip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖alpha t z - alpha t w‖ ≤ L * ‖z - w‖)
    (haclose : ∀ z, ‖z‖ ≤ R → ‖alpha t z - q‖ ≤ K * R)
    (hreaction : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖reaction t z - reaction t w‖ ≤ M * ‖z - w‖)
    {u v : GraphDoubledJetState (n := n) g R} :
    let N := fun w : GraphDoubledJetHs g n 2 =>
      m (alpha t (graphDoubledJetInclusion g w) - q) (Q w) +
        m (alpha t (graphDoubledJetInclusion g w)) c +
        reaction t (graphDoubledJetInclusion g w) -
          d (D (graphDoubledJetInclusion g w))
    (‖N u.val - N v.val‖ ≤
      (‖m‖ * K * ‖Q‖) * R * ‖u.val - v.val‖ +
      (‖m‖ * L * ‖c‖ + M + ‖d‖ * ‖D‖) *
        ‖graphDoubledJetInclusion g (u.val - v.val)‖ +
      (‖m‖ * L * ‖Q‖) * (‖u.val‖ + ‖v.val‖) *
        ‖graphDoubledJetInclusion g (u.val - v.val)‖) ∧
      ‖N 0‖ ≤ ‖m‖ * ‖alpha t 0‖ * ‖c‖ + ‖reaction t 0‖ := by
  exact shifted_tame_estimate m Q (graphDoubledJetInclusion g) D c d q alpha reaction t
    halip haclose hreaction u.property v.property

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
