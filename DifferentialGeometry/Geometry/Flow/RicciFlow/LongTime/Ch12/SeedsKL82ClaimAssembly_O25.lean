import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82VolumeTransfer_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82HistoryDistance_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82Part1_O11
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift

/-!
# CH12-O25, G2: KL82.1 (v2) from claim (C) and the distance bootstrap

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (not a verbatim
transcription; the last-three-quarters window follows from claim (C):
`C₀r0⁻² + B₀(v−a)⁻¹ ≤ (C₀+4B₀)τ⁻¹r0⁻²` for `v−a ≥ τr0²/4`, `τ ≤ 1`).  The reference PDFs
named in AGENTS.md are not on this machine; locators follow the CX11 report and DELIVERIES.

* `ricci_le_inv_time_of_claim_O25`: in dimension three, `sec ≥ -r⁻²` and the claim-(C) scalar
  bound give the endpoint Ricci bound `Ric ≤ (C₀/2 + B₀/2 + 1)/(v−a)` once `v − a ≤ r²`.
* `kl82_1_of_claim_O25`: the frozen v2 statement of KL82.1, from the claim (C) (`hclaim`) and the
  first-exit form of the trace-distance estimate (`hboot`), both in the shapes frozen in
  "[FROZEN] CH12-O25 G2".  Part (1) is `kl82_1_part1_of_claim_O11`; Part (2) is
  `volume_transfer_of_distance_CX11` with its additive-distance input produced from `hboot`
  on the ball `B(X(v), 3r0/8)` where the claim controls Ricci curvature.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature.DimensionThree
  (metricRicciAt_le_of_sectionalBoundedBelowAt)
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Dimension three: `sec ≥ -r⁻²` plus the claim-(C) scalar bound give `Ric ≤ C'/s`. -/
theorem ricci_le_inv_time_of_claim_O25 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (z : M)
    {r s C₀ B₀ : ℝ} (hs : 0 < s) (hsr : s ≤ r ^ 2) (hC₀ : 0 ≤ C₀)
    (hsec : SectionalBoundedBelowAt g z (-(r ^ 2)⁻¹))
    (hR : metricScalarAt g z ≤ C₀ * (r ^ 2)⁻¹ + B₀ * s⁻¹) (w : TangentSpace ThreeModel z) :
    ricciTensor g z w w ≤ (C₀ / 2 + B₀ / 2 + 1) / s * g.inner z w w := by
  have hRic := metricRicciAt_le_of_sectionalBoundedBelowAt finrank_euclideanSpace_fin hsec w
  rw [metricRicciAt_apply_eq_ricciTensor] at hRic
  have hgw : 0 ≤ g.inner z w w := metric_inner_self_nonneg g z w
  have hr2 : (r ^ 2)⁻¹ ≤ s⁻¹ := inv_anti₀ hs hsr
  have hC : C₀ * (r ^ 2)⁻¹ ≤ C₀ * s⁻¹ := mul_le_mul_of_nonneg_left hr2 hC₀
  have hcoef : metricScalarAt g z / 2 + (r ^ 2)⁻¹ ≤ (C₀ / 2 + B₀ / 2 + 1) / s := by
    have hexp : (C₀ / 2 + B₀ / 2 + 1) / s = C₀ * s⁻¹ / 2 + B₀ * s⁻¹ / 2 + s⁻¹ := by ring
    rw [hexp]
    linarith
  exact hRic.trans (mul_le_mul_of_nonneg_right hcoef hgw)

/-- **KL82.1 (frozen v2)** from claim (C) and the distance bootstrap. -/
theorem kl82_1_of_claim_O25
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
    (hclaim : ∀ w : ℝ, 0 < w → ∃ τc C₀ B₀ : ℝ, 0 < τc ∧ 0 ≤ C₀ ∧ 0 ≤ B₀ ∧
          ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
            (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
            (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
              (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
            Perelman.AdmissiblePinchingFunction Phi →
            (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
              curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
                (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
                (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
            0 < r0 → 0 < τ → τ ≤ τc → (a : ℝ) = top - τ * r0 ^ 2 →
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
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (3 * r0 / 8),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
              C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - a)⁻¹) :
    ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
          ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
            (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
            (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
              (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
            Perelman.AdmissiblePinchingFunction Phi →
            (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
              curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
                (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
                (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
            0 < r0 → 0 < τ → τ ≤ τ₀ → (a : ℝ) = top - τ * r0 ^ 2 →
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
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
                  (r0 / 4),
                metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K₀ * τ⁻¹ * (r0 ^ 2)⁻¹) ∧
            ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
              ballVolume (H.stageMetric (H.activeStage a) a)
                (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4) := by
  intro w hw
  obtain ⟨τc, C₀, B₀, hτc, hC₀, hB₀, hcl⟩ := hclaim w hw
  set C' : ℝ := C₀ / 2 + B₀ / 2 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  obtain ⟨τ₁, hτ₁, -, hVT⟩ := volume_transfer_of_distance_CX11.{u} C'
  set τ₂ : ℝ := min (C' / 768) (3 / (65536 * C')) with hτ₂
  have hτ₂pos : 0 < τ₂ := lt_min (by positivity) (by positivity)
  refine ⟨min (min τc τ₁) (min 1 τ₂), C₀ + 4 * B₀ + 1,
    lt_min (lt_min hτc hτ₁) (lt_min one_pos hτ₂pos),
    (min_le_right _ _).trans (min_le_left _ _), by positivity, ?_⟩
  intro H top x0 r0 τ K a hat X Phi hPhi hpinch hr0 hτ hτ0 ha hSF hsec hvol
  have hτc' : τ ≤ τc := hτ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ₁' : τ ≤ τ₁ := hτ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ1 : τ ≤ 1 := hτ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ₂' : τ ≤ τ₂ := hτ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hclv := hcl H top x0 r0 τ K a hat X hPhi hpinch hr0 hτ hτc' ha hSF hsec hvol
  refine ⟨?_, ?_⟩
  · intro v hav hvt hv q hq
    have h1 := kl82_1_part1_of_claim_O11 H hat X hr0 hτ hτ1 hC₀ hB₀ ha hclv v hav hvt hv q hq
    have h2 : 0 ≤ τ⁻¹ * (r0 ^ 2)⁻¹ := by positivity
    calc metricScalarAt (H.stageMetric (H.activeStage v) v) q
        ≤ (C₀ + 4 * B₀) * τ⁻¹ * (r0 ^ 2)⁻¹ := h1
      _ ≤ (C₀ + 4 * B₀ + 1) * τ⁻¹ * (r0 ^ 2)⁻¹ := by nlinarith
  · have hsqrt_ta : Real.sqrt ((top : ℝ) - a) = Real.sqrt τ * r0 := by
      rw [ha, show (top : ℝ) - (top - τ * r0 ^ 2) = τ * r0 ^ 2 by ring,
        Real.sqrt_mul hτ.le, Real.sqrt_sq hr0.le]
    have hsqrt_3 : Real.sqrt (3 * ((top : ℝ) - a) / C') = Real.sqrt (3 * τ / C') * r0 := by
      rw [ha, show 3 * ((top : ℝ) - (top - τ * r0 ^ 2)) / C' = (3 * τ / C') * r0 ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hr0.le]
    have hδ : 16 * Real.sqrt (C' / 3) * Real.sqrt τ ≤ 1 / 16 := by
      have hτa : τ ≤ 3 / (65536 * C') := hτ₂'.trans (min_le_right _ _)
      have hm : C' / 3 * τ ≤ (1 / 256) ^ 2 := by
        calc C' / 3 * τ ≤ C' / 3 * (3 / (65536 * C')) :=
              mul_le_mul_of_nonneg_left hτa (by positivity)
          _ = (1 / 256) ^ 2 := by field_simp; norm_num
      have hs : Real.sqrt (C' / 3) * Real.sqrt τ ≤ 1 / 256 := by
        rw [← Real.sqrt_mul (by positivity)]
        calc Real.sqrt (C' / 3 * τ) ≤ Real.sqrt ((1 / 256) ^ 2) := Real.sqrt_le_sqrt hm
          _ = 1 / 256 := Real.sqrt_sq (by norm_num)
      linarith
    have hε : Real.sqrt (3 * τ / C') ≤ 1 / 16 := by
      have hτb : τ ≤ C' / 768 := hτ₂'.trans (min_le_left _ _)
      have hm : 3 * τ / C' ≤ (1 / 16) ^ 2 := by
        rw [div_le_iff₀ hC'pos]
        linarith
      calc Real.sqrt (3 * τ / C') ≤ Real.sqrt ((1 / 16) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / 16 := Real.sqrt_sq (by norm_num)
    have hδr : 16 * Real.sqrt (C' / 3) * Real.sqrt ((top : ℝ) - a) ≤ r0 / 16 := by
      rw [hsqrt_ta]
      calc 16 * Real.sqrt (C' / 3) * (Real.sqrt τ * r0)
          = (16 * Real.sqrt (C' / 3) * Real.sqrt τ) * r0 := by ring
        _ ≤ 1 / 16 * r0 := mul_le_mul_of_nonneg_right hδ hr0.le
        _ = r0 / 16 := by ring
    have hεr : Real.sqrt (3 * ((top : ℝ) - a) / C') ≤ r0 / 16 := by
      rw [hsqrt_3]
      calc Real.sqrt (3 * τ / C') * r0 ≤ 1 / 16 * r0 := mul_le_mul_of_nonneg_right hε hr0.le
        _ = r0 / 16 := by ring
    have hXtop : X.point (H.activeStage top) (H.activeStage_mono hat)
        (H.activeStage_mono (le_refl top)) = x0 := X.endpoint_eq
    have hSF' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
        ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
          Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) z) := by
      intro v hav hvt z hz
      obtain ⟨A, -⟩ := hSF v hav hvt z hz
      exact ⟨A⟩
    have hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v →
        ∀ z : (H.stageAt v).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
            ENNReal.ofReal (3 * r0 / 8) →
          ∀ w : TangentSpace ThreeModel z,
            ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
              C' / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w := by
      intro v hav hvt hav' z hz w'
      have hs : 0 < (v : ℝ) - a := by linarith
      have hvt' : (v : ℝ) ≤ top := hvt
      have hsr : (v : ℝ) - a ≤ r0 ^ 2 := by
        rw [ha]
        have : τ * r0 ^ 2 ≤ r0 ^ 2 := by nlinarith [sq_nonneg r0]
        linarith
      have hzr0 : z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0 :=
        lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal (by linarith))
      exact ricci_le_inv_time_of_claim_O25 _ z hs hsr hC₀ (hsec v hav hvt z hzr0)
        (hclv v hav hvt hav' z hz) w'
    refine hVT H a top hat x0 X w r0 τ K hw hr0 hτ hτ₁' ha ?_ hsec ?_ hvol
    · intro q hq
      have hq' : q ∈ riemannianBallOf (H.stageMetric (H.activeStage top) top)
          (X.point (H.activeStage top) (H.activeStage_mono hat)
            (H.activeStage_mono (le_refl top))) r0 := by
        rw [hXtop]
        exact hq
      exact hSF top hat (le_refl top) q hq'
    · intro q hq A v hav hvt
      have hd : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
          ENNReal.ofReal (r0 / 4) := hq
      have hne := ne_top_of_lt hd
      have hdlt : (riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal <
          r0 / 4 := ENNReal.toReal_lt_of_lt_ofReal hd
      have hdr0 : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
          ENNReal.ofReal r0 := lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal (by linarith))
      have hb := hboot H hat X A (C := C') (ρ := r0) (R0 := 3 * r0 / 8) hC'pos hr0 hdr0
        (by linarith) (by linarith) hSF' hRic v hav hvt
      rw [traceEDist_at_stage_CX11 H X A v hav hvt (H.activeStage v) rfl
        (H.activeStage_mono hav) (H.activeStage_mono hvt)] at hb
      have hδv : 16 * Real.sqrt (C' / 3) * (Real.sqrt ((top : ℝ) - a) -
          Real.sqrt ((v : ℝ) - a)) ≤ 16 * Real.sqrt (C' / 3) * Real.sqrt τ * r0 := by
        rw [hsqrt_ta]
        have h1 : 0 ≤ Real.sqrt ((v : ℝ) - a) := Real.sqrt_nonneg _
        have h2 : 0 ≤ Real.sqrt (C' / 3) := Real.sqrt_nonneg _
        nlinarith
      refine hb.trans ?_
      calc ENNReal.ofReal
            ((riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal +
              16 * Real.sqrt (C' / 3) * (Real.sqrt ((top : ℝ) - a) - Real.sqrt ((v : ℝ) - a)))
          ≤ ENNReal.ofReal
            ((riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal +
              16 * Real.sqrt (C' / 3) * Real.sqrt τ * r0) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q +
              ENNReal.ofReal (16 * Real.sqrt (C' / 3) * Real.sqrt τ * r0) := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
              ENNReal.ofReal_toReal hne]

end GC.LongTime.Ch12
