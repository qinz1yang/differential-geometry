import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82TracedVolume_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ComponentVolume_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82VolumeMargin_CX11

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The exact v2 quarter-ball volume conclusion from the additive distance
estimate. `hshift` is the still separate G4 input, in extended distance so that
infinite distances cannot be hidden by `ENNReal.toReal`. No volume persistence
or measure-preservation conclusion is assumed. -/
theorem volume_transfer_of_distance_CX11 (C : ℝ) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ ≤ 1 ∧
    ∀ (H : ObservedHistory.{u}) (a t : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
      (p : (H.stageAt t).Carrier)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) p) (w r τ K : ℝ),
      0 < w → 0 < r → 0 < τ → τ ≤ τ₁ → (a : ℝ) = t - τ * r ^ 2 →
      (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
        ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q, A.isRmBoundedBy (hat := hat) K) →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r,
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) →
      (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4),
        ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q +
            ENNReal.ofReal (16 * Real.sqrt (C / 3) * Real.sqrt τ * r)) →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
        ballVolume (H.stageMetric (H.activeStage a) a)
          (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r / 4) := by
  obtain ⟨τ₁, hτ₁, hτ₁1, hmargin⟩ := exists_volume_transfer_margin_CX11 C
  refine ⟨τ₁, hτ₁, hτ₁1, ?_⟩
  intro H a t hat p X w r τ K hw hr hτ hτle ha htr hsec hshift hvol
  have hatlt : a < t := by
    change (a : ℝ) < t
    rw [ha]
    exact sub_lt_self _ (mul_pos hτ (sq_pos_of_pos hr))
  let α : ℝ := 1 / 4 - 16 * Real.sqrt (C / 3) * Real.sqrt τ
  obtain ⟨hα, hmargin'⟩ := hmargin τ hτ.le hτle
  change 0 < α at hα
  have hα4 : α ≤ 1 / 4 := by
    dsimp [α]
    have hh : 0 ≤ 16 * Real.sqrt (C / 3) * Real.sqrt τ := by positivity
    linarith
  have hαr : 0 < α * r := mul_pos hα hr
  have hαrr : α * r ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hα4 hr.le
    linarith
  have hαr4 : α * r ≤ r / 4 := by
    have hh := mul_le_mul_of_nonneg_right hα4 hr.le
    linarith
  let : MeasurableSpace (H.stageAt t).Carrier := borel _
  let : BorelSpace (H.stageAt t).Carrier := ⟨rfl⟩
  let B := riemannianBallOf (H.stageMetric (H.activeStage t) t) p (α * r)
  have hBsmall : B ⊆ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4) :=
    riemannianBallOf_mono _ _ hαr4
  have hBball : B ⊆ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r :=
    riemannianBallOf_mono _ _ hαrr
  have hcapture (q : (H.stageAt t).Carrier) (hq : q ∈ B)
      (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) q)
      (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) ∈
        riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (r / 4) := by
    have hh := (hshift q (hBsmall hq) A v hav hvt).trans_lt
      (ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hq)
    rw [← ENNReal.ofReal_add hαr.le (by positivity)] at hh
    have he : α * r + 16 * Real.sqrt (C / 3) * Real.sqrt τ * r = r / 4 := by
      dsimp [α]
      ring
    rwa [he] at hh
  have hsetvol := traced_set_volume_of_sec_CX11 H hatlt p hr htr B
    (isOpen_riemannianBallOf _ _ _).measurableSet hBball
    (fun q hq A v hav hvt => hsec v hav hvt _
      (riemannianBallOf_mono _ _ (by linarith : r / 4 ≤ r) (hcapture q hq A v hav hvt)))
  have hsmallvol := ballVolume_small_of_sec_component_CX11
    (H.stageMetric (H.activeStage t) t) (RiemannianMetricComplete.of_compact _) p
    (q := r⁻¹) (inv_nonneg.mpr hr.le) hαr hαrr
    (fun z hz => by
      have hh := hsec t hat le_rfl z
      rw [X.endpoint_eq] at hh
      simpa only [inv_pow] using hh hz) hvol
  have hexp : 2 * r⁻¹ * r = (2 : ℝ) := by field_simp
  rw [hexp] at hsmallvol
  have htime : (t : ℝ) - a = τ * r ^ 2 := by rw [ha]; ring
  rw [htime] at hsetvol
  have he : -6 * (τ * r ^ 2) / r ^ 2 = -6 * τ := by field_simp
  rw [he] at hsetvol
  have hnum : w * (r / 4) ^ 3 / 10 ≤
      Real.exp (-6 * τ) * (w * (α * r) ^ 3 / Real.exp 2) := by
    have hh := mul_le_mul_of_nonneg_left hmargin' (mul_pos hw (pow_pos hr 3)).le
    have he : Real.exp (-6 * τ) / Real.exp 2 = Real.exp (-(2 + 6 * τ)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    calc
      w * (r / 4) ^ 3 / 10 = (w * r ^ 3) * ((1 / 4 : ℝ) ^ 3 / 10) := by ring
      _ ≤ (w * r ^ 3) * (Real.exp (-(2 + 6 * τ)) * α ^ 3) := hh
      _ = Real.exp (-6 * τ) * (w * (α * r) ^ 3 / Real.exp 2) := by
        rw [← he]
        ring
  have hcomparison : ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
      ENNReal.ofReal (Real.exp (-6 * τ)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t) B := by
    apply (ENNReal.ofReal_le_ofReal hnum).trans
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' le_rfl hsmallvol
  apply (hcomparison.trans hsetvol).trans
  apply measure_mono
  rintro z ⟨q, hq, A, rfl⟩
  exact hcapture q hq A a le_rfl hat

end GC.LongTime.Ch12
