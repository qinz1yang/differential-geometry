import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimDatum_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82BlowupLocal_O25

/-!
# CH12-O36, G4c: claim (C) and KL82.1 (frozen v2)

* `kl82_claim_O36`: the `hclaim` input of `kl82_1_of_claim_O25` ("[FROZEN] CH12-O25 G2" (c)),
  verbatim.  Proof by contradiction: for `N = n + 1` take `τc = τw(N)` from
  `kl82_blowup_datum_O36`; a counterexample with `C₀ = B₀ = n + 1` gives a blow-up datum
  `(t_n, y_n, Q_n)` with `Q_n r0_n² ≥ n + 1`; `blowup_core_local_O25` with `K = 8√3`,
  `ε n = (Q_n r0_n²)⁻¹ ≤ 1/(n+1)`, `v = w/10·(2/17)³·e^{-25/16}` gives `False`.
  (D-R4-6 constants; the pinching hypothesis of the frozen shape is not used.)
* `kl82_1_O36`: `kl82_1_of_claim_O25 dist_trace_boot_S68 kl82_claim_O36` (frozen v2 KL82.1).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

/-- **Claim (C)** (`hclaim` of `kl82_1_of_claim_O25`, verbatim). -/
theorem kl82_claim_O36 :
    ∀ w : ℝ, 0 < w → ∃ τc C₀ B₀ : ℝ, 0 < τc ∧ 0 ≤ C₀ ∧ 0 ≤ B₀ ∧
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
              C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - a)⁻¹ := by
  intro w hw
  by_contra hcon
  have hD := fun n : ℕ => kl82_blowup_datum_O36.{u} ((n : ℝ) + 1)
    (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  choose τw hτw _hτw1 hdat using hD
  have hneg : ∀ n : ℕ, ∃ (H : ObservedHistory.{u}) (ts : Icc (0 : ℝ) H.horizon)
      (y : (H.stageAt ts).Carrier) (Q r0 : ℝ),
      0 < Q ∧ metricScalarAt (H.stageMetric (H.activeStage ts) ts) y = Q ∧
      (n : ℝ) + 1 ≤ Q * r0 ^ 2 ∧ 0 < r0 ∧
      (∀ Aa T : ℝ, 0 < Aa → 0 < T → 8192 * (Aa + 16 * T + 1) ^ 2 < (n : ℝ) + 1 →
        2 * T ≤ (n : ℝ) + 1 →
        H.isTracedRegion ts y (Aa / Real.sqrt Q) (T / Q) (8 * Real.sqrt 3 * Q) ∧
        ∀ (a'' : Icc (0 : ℝ) H.horizon) (ha'' : a'' ≤ ts), (a'' : ℝ) = ts - T / Q →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage ts) ts) y (Aa / Real.sqrt Q),
          ∀ Y : BackwardPointTrace H (H.activeStage a'') (H.activeStage ts)
              (H.activeStage_mono ha'') q,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a'' ≤ v) (hvt : v ≤ ts),
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v)
              (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (-(r0 ^ 2)⁻¹)) ∧
      ∀ (D : ℝ) (hQ : 0 < Q), 0 < D → 1024 * D ^ 2 ≤ (n : ℝ) + 1 →
        ∀ x ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts)) y D,
        ∀ s : ℝ, 0 < s → s ≤ D →
          ENNReal.ofReal (w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16) * s ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt ts).Carrier
              (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts))
              (riemannianBallOf (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts)) x s) := by
    intro n
    by_contra hno
    apply hcon
    refine ⟨τw n, (n : ℝ) + 1, (n : ℝ) + 1, hτw n, by positivity, by positivity, ?_⟩
    intro H top x0 r0 τ K a hat X Phi _hPhi _hpinch hr0 hτ hττ ha hSF hsec hvol v hav hvt hav'
      q hq
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ts, y, Q, hQ, hRy, hNQ, htr, hvl⟩ :=
      hdat n w H top x0 r0 τ K a hat X hw hr0 hτ hττ ha hSF hsec hvol
        ⟨v, hav, hvt, hav', q, hq, hlt⟩
    exact hno ⟨H, ts, y, Q, r0, hQ, hRy, hNQ, hr0, htr, hvl⟩
  choose H ts y Q r0 hQ hRy hNQ hr0 htr hvl using hneg
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlarge : ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, M < (n : ℝ) + 1 := by
    intro M
    refine eventually_atTop.2 ⟨⌈M⌉₊, fun n hn => ?_⟩
    have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    have h2 : ((⌈M⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let ε : ℕ → ℝ := fun n => (Q n * r0 n ^ 2)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => inv_pos.mpr (mul_pos (hQ n) (pow_pos (hr0 n) 2))
  have hεle : ∀ n, ε n ≤ 1 / ((n : ℝ) + 1) := fun n => by
    rw [one_div]; exact inv_anti₀ (hn1 n) (hNQ n)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hε n).le) hεle
  have hεQ : ∀ n, ε n * Q n = (r0 n ^ 2)⁻¹ := fun n => by
    have h1 := (hQ n).ne'
    have h2 := (hr0 n).ne'
    simp only [ε]
    field_simp
  refine blowup_core_local_O25 H ts y Q hQ hRy (K := 8 * Real.sqrt 3) ?_ ε hε hεlim ?_
    (v := w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16))
    (div_pos (mul_pos (div_pos hw (by norm_num)) (by norm_num)) (Real.exp_pos _)) ?_
  · intro A T hA hT
    filter_upwards [hlarge (8192 * (A + 16 * T + 1) ^ 2), hlarge (2 * T)] with n h1 h2
    exact (htr n A T hA hT h1 h2.le).1
  · intro A T hA hT
    filter_upwards [hlarge (8192 * (A + 16 * T + 1) ^ 2), hlarge (2 * T)] with n h1 h2
    intro a hat ha q hq X v hav hvt
    rw [hεQ n]
    exact (htr n A T hA hT h1 h2.le).2 a hat ha q hq X v hav hvt
  · intro D hD
    filter_upwards [hlarge (1024 * D ^ 2)] with n h1
    exact hvl n D (hQ n) hD h1.le

/-- **KL82.1 (frozen v2)**, unconditional. -/
theorem kl82_1_O36 :
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
                (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4) :=
  kl82_1_of_claim_O25.{u} dist_trace_boot_S68.{u} kl82_claim_O36.{u}

end GC.LongTime.Ch12
