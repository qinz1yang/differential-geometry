import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimWindow_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimVolume_O30

/-!
# CH12-O30, G3a: volume at the time of the selected point of claim (C)

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5; not a verbatim
transcription.  The reference PDFs named in AGENTS.md are not on this machine.

If claim (C) holds on the window `(s, top]` with base `s` (the "good" start produced by
`exists_late_bad_start_O30`), the quarter-ball volume at `s` follows from
`kl82_window_volume_O30` applied to the restricted traces (or, when `s = top`, from the local
volume comparison), and `ballVolume_recentre_far_O30` moves it to every point of the
`15r0/32`-ball at every radius `ρ ≤ 17r0/32`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **Volume at the selected time** for a good window start `s`. -/
theorem kl82_selected_volume_O30
    (hboot : ∀ (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
      {p q : (H.stageAt t).Carrier}
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
      (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
      {C ρ R0 : ℝ}, 0 < C → 0 < ρ →
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q < ENNReal.ofReal ρ →
      (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) < ρ / 2 →
      (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) +
          Real.sqrt (3 * ((t : ℝ) - a) / C) < R0 →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
          Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) z)) →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
        ∀ z : (H.stageAt v).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
            ENNReal.ofReal R0 →
          ∀ w : TangentSpace ThreeModel z,
            ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
              C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w) →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        traceEDist_CX11 H (hat := hat) X A v hav hvt ≤
          ENNReal.ofReal ((riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
            16 * Real.sqrt (C / 3) * (Real.sqrt ((t : ℝ) - a) - Real.sqrt ((v : ℝ) - a))))
    (C₀ B₀ : ℝ) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀) :
    ∃ τw : ℝ, 0 < τw ∧ τw ≤ 1 ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K w : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0),
        0 < w → 0 < r0 → 0 < τ → τ ≤ τw → (a : ℝ) = top - τ * r0 ^ 2 →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                    (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
            ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ top),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (s : ℝ) < v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (3 * r0 / 8),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
              C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - s)⁻¹) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
            (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))
            (15 * r0 / 32),
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ 17 * r0 / 32 →
          ENNReal.ofReal (w / 10 * (2 / 17) ^ 3 * ρ ^ 3 / Real.exp (25 / 16)) ≤
            ballVolume (H.stageMetric (H.activeStage s) s) x ρ := by
  obtain ⟨τw, hτw, hτw1, hW⟩ := kl82_window_volume_O30 hboot C₀ B₀ hC₀ hB₀
  refine ⟨τw, hτw, hτw1, ?_⟩
  intro H top x0 r0 τ K w a hat X hw hr0 hτ hτ0 ha hSF hsec hvol s has hst hgood x hx ρ hρ hρr
  have hsecs := hsec s has hst
  have hquarter : ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
      ballVolume (H.stageMetric (H.activeStage s) s)
        (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))
        (r0 / 4) := by
    rcases lt_or_eq_of_le hst with hlt | heq
    · have hlt' : (s : ℝ) < top := hlt
      have has' : (a : ℝ) ≤ s := has
      set τ' : ℝ := ((top : ℝ) - s) / r0 ^ 2 with hτ'
      have hr2 : 0 < r0 ^ 2 := by positivity
      have hτ'pos : 0 < τ' := div_pos (sub_pos.mpr hlt') hr2
      have hτ'le : τ' ≤ τ := by
        rw [hτ', div_le_iff₀ hr2]
        linarith
      have hs' : (s : ℝ) = top - τ' * r0 ^ 2 := by
        rw [hτ', div_mul_cancel₀ _ hr2.ne']
        ring
      refine hW H top x0 r0 τ' K w s hst
        (traceRestrict_O30 X (H.activeStage_mono has) (H.activeStage_mono hst))
        hw hr0 hτ'pos (hτ'le.trans hτ0) hs' ?_
        (fun v hsv hvt q hq => hsec v (has.trans hsv) hvt q hq) hvol
        (fun v hsv hvt hv q hq => hgood v (has.trans hsv) hvt hv q hq)
      intro v hsv hvt q hq
      obtain ⟨A, hA⟩ := hSF v (has.trans hsv) hvt q hq
      exact ⟨traceRestrict_O30 A (H.activeStage_mono has) (H.activeStage_mono hsv),
        isRmBoundedBy_restrict_O30 has hsv A hA⟩
    · subst heq
      have hXtop : X.point (H.activeStage s) (H.activeStage_mono has)
          (H.activeStage_mono hst) = x0 := X.endpoint_eq
      rw [hXtop]
      have hsec0 : ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) x0 r0,
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage s) s) z (-(r0⁻¹ ^ 2)) := by
        intro z hz
        have hz' : z ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
            (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) r0 := by
          rw [hXtop]; exact hz
        simpa only [inv_pow] using hsecs z hz'
      have hc := ballVolume_small_of_sec_component_CX11 (H.stageMetric (H.activeStage s) s)
        (RiemannianMetricComplete.of_compact _) x0 (q := r0⁻¹) (s := r0 / 4) (R := r0)
        (inv_nonneg.mpr hr0.le) (by positivity) (by linarith) hsec0 hvol
      have he : 2 * r0⁻¹ * r0 = (2 : ℝ) := by field_simp
      rw [he] at hc
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hc
      have hexp : Real.exp 2 ≤ 10 := by
        have h1 := Real.exp_one_lt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [h2]
        nlinarith [Real.exp_pos 1]
      have hnum : 0 ≤ w * r0 ^ 3 := by positivity
      rw [div_le_div_iff₀ (by norm_num) (Real.exp_pos 2)]
      have h3 : 0 ≤ w * (r0 / 4) ^ 3 := by positivity
      nlinarith
  exact ballVolume_recentre_far_O30 (H.stageMetric (H.activeStage s) s)
    (RiemannianMetricComplete.of_compact _) _ x hr0 hρ hρr hx hsecs hquarter

end GC.LongTime.Ch12
