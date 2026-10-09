import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84BlowupCore_O9

/-!
# CH12-O11, Group G2: KL 82.1(1) from the `(t − a)⁻¹` claim (C)

The continuity/blow-up argument of Kleiner–Lott Cor. 45.13 / Lemma 82.1 (Perelman I.11.6(b))
proves the claim (C) of `[FROZEN v2] CH12-O11 kl82_1`:

  `R(q, v) ≤ C₀ r0⁻² + B₀ (v − a)⁻¹` for `a < v ≤ top`, `q ∈ B_{g_v}(X(v), 3 r0 / 8)`.

On the last three quarters of the window, `v − a ≥ τ r0² / 4`, so with `τ ≤ 1` this gives
part (1) of `kl82_1_O11` (the scalar bound `K₀ τ⁻¹ r0⁻²` on the quarter balls) with
`K₀ = C₀ + 4 B₀`.  This file is that reduction, in the exact binder shapes of the frozen v2
statement.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- **G2.** Part (1) of `kl82_1_O11` from the claim (C). -/
theorem kl82_1_part1_of_claim_O11 (H : ObservedHistory.{u})
    {top a : Icc (0 : ℝ) H.horizon} (hat : a ≤ top) {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top) (H.activeStage_mono hat) x0)
    {r0 τ C₀ B₀ : ℝ} (hr0 : 0 < r0) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀)
    (ha : (a : ℝ) = top - τ * r0 ^ 2)
    (hclaim : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (3 * r0 / 8),
        metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
          C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - a)⁻¹) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (r0 / 4),
        metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
          (C₀ + 4 * B₀) * τ⁻¹ * (r0 ^ 2)⁻¹ := by
  intro v hav hvt hv q hq
  have hr2 : 0 < r0 ^ 2 := by positivity
  have hgap : τ * r0 ^ 2 / 4 ≤ (v : ℝ) - a := by rw [ha]; linarith
  have hgap_pos : 0 < (v : ℝ) - a := lt_of_lt_of_le (by positivity) hgap
  have hq' := riemannianBallOf_mono _ _ (show r0 / 4 ≤ 3 * r0 / 8 by linarith) hq
  have hR := hclaim v hav hvt (by linarith) q hq'
  have hτinv : 1 ≤ τ⁻¹ := one_le_inv_iff₀.mpr ⟨hτ, hτ1⟩
  have h1 : C₀ * (r0 ^ 2)⁻¹ ≤ C₀ * τ⁻¹ * (r0 ^ 2)⁻¹ := by
    have hpos : 0 ≤ C₀ * (r0 ^ 2)⁻¹ := by positivity
    calc C₀ * (r0 ^ 2)⁻¹ = 1 * (C₀ * (r0 ^ 2)⁻¹) := by ring
      _ ≤ τ⁻¹ * (C₀ * (r0 ^ 2)⁻¹) := mul_le_mul_of_nonneg_right hτinv hpos
      _ = C₀ * τ⁻¹ * (r0 ^ 2)⁻¹ := by ring
  have h2 : B₀ * ((v : ℝ) - a)⁻¹ ≤ 4 * B₀ * τ⁻¹ * (r0 ^ 2)⁻¹ := by
    have hinv : ((v : ℝ) - a)⁻¹ ≤ (τ * r0 ^ 2 / 4)⁻¹ :=
      inv_anti₀ (by positivity) hgap
    have hval : (τ * r0 ^ 2 / 4)⁻¹ = 4 * τ⁻¹ * (r0 ^ 2)⁻¹ := by
      field_simp
    calc B₀ * ((v : ℝ) - a)⁻¹ ≤ B₀ * (τ * r0 ^ 2 / 4)⁻¹ := mul_le_mul_of_nonneg_left hinv hB₀
      _ = 4 * B₀ * τ⁻¹ * (r0 ^ 2)⁻¹ := by rw [hval]; ring
  calc metricScalarAt (H.stageMetric (H.activeStage v) v) q
      ≤ C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - a)⁻¹ := hR
    _ ≤ C₀ * τ⁻¹ * (r0 ^ 2)⁻¹ + 4 * B₀ * τ⁻¹ * (r0 ^ 2)⁻¹ := add_le_add h1 h2
    _ = (C₀ + 4 * B₀) * τ⁻¹ * (r0 ^ 2)⁻¹ := by ring

end GC.LongTime.Ch12
