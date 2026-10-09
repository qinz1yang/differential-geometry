import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimSelVol_O30

/-!
# CH12-O30, G3c: monotonicity of the window claim (C) in the window start

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5; not a verbatim
transcription.  The claim on `(s, top]` with base `s` implies the claim on `(s', top]` with base
`s'` for `s ≤ s'`, because `(v − s)⁻¹ ≤ (v − s')⁻¹`.  This is the `hmono` input of
`exists_late_bad_start_O30`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- The window claim (C) is monotone in the window start. -/
theorem kl82_good_mono_O30 (H : ObservedHistory.{u}) (top a : Icc (0 : ℝ) H.horizon)
    (hat : a ≤ top) {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
      (H.activeStage_mono hat) x0)
    {r0 C₀ B₀ : ℝ} (hB₀ : 0 ≤ B₀) {s s' : ℝ} (hss : s ≤ s')
    (hs : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), s < (v : ℝ) →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (3 * r0 / 8),
        metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
          C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - s)⁻¹) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), s' < (v : ℝ) →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (3 * r0 / 8),
        metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
          C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - s')⁻¹ := by
  intro v hav hvt hv q hq
  have h1 := hs v hav hvt (lt_of_le_of_lt hss hv) q hq
  have h2 : ((v : ℝ) - s)⁻¹ ≤ ((v : ℝ) - s')⁻¹ :=
    inv_anti₀ (sub_pos.mpr hv) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hB₀
  linarith

end GC.LongTime.Ch12
