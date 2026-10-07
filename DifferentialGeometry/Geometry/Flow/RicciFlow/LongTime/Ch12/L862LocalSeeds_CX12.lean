import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TraceFamily_CX12

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable (hKL82 : ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
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
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4))

include hKL82

/-- Local G2d conversion, with constants chosen before the history and its
radius. This uses the frozen v2 KL82 input and an actual traced family;
it does not assume a global G2c supplier. The uniform seed can be fed to
KL84.1(c) when extending the Sublemma 86.6 window. -/
theorem seeds_of_traced_family_CX12 {w K τ₁ τ₂ : ℝ}
    (hw : 0 < w) (hK : 0 < K) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    ∃ α c c₁ : ℝ, 0 < α ∧ 2 * α ^ 2 < c ∧ 0 < c₁ ∧ c ≤ τ₁ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon)
        (x : (H.stageAt top).Carrier) (r : ℝ)
        (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x) {Phi : ℝ → ℝ},
        Perelman.AdmissiblePinchingFunction Phi →
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ z,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) z
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) z)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) z))) →
        0 < r →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          H.isTracedRegion v (X.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) (r / 8) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)) →
        (∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ENNReal.ofReal (w * ρ ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage top) top) x ρ) →
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - c * r ^ 2 ≤ v →
          hasSmallParabolicCurvature H v
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (α * r) ∧
          ENNReal.ofReal (c₁ * (α * r) ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (α * r) := by
  obtain ⟨τ₀, K₀, hτ₀, _, _, hkl⟩ := hKL82 w hw
  obtain ⟨csd, hcsd, hsd⟩ := seed_scale_down_S21.{u}
  set κ : ℝ := min (1 / 8) (min τ₂ (1 / (K + 1))) with hκdef
  have hκ : 0 < κ := lt_min (by norm_num) (lt_min hτ₂ (by positivity))
  have hκ8 : κ ≤ 1 / 8 := min_le_left _ _
  have hκτ₂ : κ ≤ τ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hκK1 : κ ≤ 1 / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hκK : κ * K ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right hκK1 (by linarith : (0 : ℝ) ≤ K + 1)
    rw [one_div, inv_mul_cancel₀ (by linarith : (K + 1) ≠ 0)] at h1
    have h2 := mul_le_mul_of_nonneg_left (by linarith : K ≤ K + 1) hκ.le
    linarith
  have hκ1 : κ ≤ 1 := by linarith
  have hκ2K : κ ^ 2 * K ≤ 1 := by
    calc κ ^ 2 * K = κ * (κ * K) := by ring
      _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hκK hκ.le
      _ ≤ 1 := by linarith
  have hκ2τ : κ ^ 2 ≤ τ₂ := by
    calc κ ^ 2 = κ * κ := sq κ
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hκ1 hκ.le
      _ ≤ τ₂ := by linarith
  have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le hκ1
  set m : ℝ := min τ₀ (min τ₁ τ₂) with hmdef
  have hm : 0 < m := lt_min hτ₀ (lt_min hτ₁ hτ₂)
  have hmτ₀ : m ≤ τ₀ := min_le_left _ _
  have hmτ₁ : m ≤ τ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hmτ₂ : m ≤ τ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hκm1 : κ ^ 2 * m ≤ τ₁ := by
    have := mul_le_mul_of_nonneg_right hκ2 hm.le
    linarith
  have hκm2 : κ ^ 2 * m ≤ τ₂ := by
    have := mul_le_mul_of_nonneg_right hκ2 hm.le
    linarith
  set σ : ℝ := min (1 / 4) (m / 4) with hσdef
  have hσ : 0 < σ := lt_min (by norm_num) (by positivity)
  have hσ4 : σ ≤ 1 / 4 := min_le_left _ _
  have hσ2 : σ ≤ 1 / 2 := by linarith
  have hσm : σ ≤ m / 4 := min_le_right _ _
  have hσ2m : σ ^ 2 ≤ m / 8 := by
    calc σ ^ 2 = σ * σ := sq σ
      _ ≤ (1 / 2) * σ := mul_le_mul_of_nonneg_right hσ2 hσ.le
      _ ≤ m / 8 := by linarith
  have hσsq : σ ^ 2 ≤ 1 / 4 := by
    calc σ ^ 2 = σ * σ := sq σ
      _ ≤ (1 / 2) * (1 / 2) := mul_le_mul hσ2 hσ2 hσ.le (by norm_num)
      _ = 1 / 4 := by norm_num
  have hσκ : σ * κ ≤ 1 / 16 := by
    have := mul_le_mul hσ2 hκ8 hκ.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hσκτ : σ ^ 2 * κ ^ 2 ≤ τ₂ := by
    have := mul_le_mul_of_nonneg_right hσsq (sq_nonneg κ)
    linarith
  have h3σκK : 3 * σ ^ 2 * (κ ^ 2 * K) ≤ 1 := by
    have := mul_le_mul hσsq hκ2K (by positivity) (by norm_num)
    linarith
  let c₁ := min (csd * (w / 10)) w
  have hc₁ : 0 < c₁ := lt_min (by positivity) hw
  have hc₁sd : c₁ ≤ csd * (w / 10) := min_le_left _ _
  have hc₁w : c₁ ≤ w := min_le_right _ _
  refine ⟨σ * κ, κ ^ 2 * m, c₁, by positivity, ?_, hc₁, hκm1, ?_⟩
  · have hk2 : 0 < κ ^ 2 := by positivity
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hσ2m hk2.le, mul_pos hm hk2]
  intro H top x r a hat X Phi hPhi hpin hr hTF hvol v hav hvt hv
  have hK0 : 0 ≤ K * (r ^ 2)⁻¹ := by positivity
  have hTFv := hTF v hav hvt
  have hr2 : 0 < r ^ 2 := by positivity
  constructor
  · refine hasSmall_of_traced_S23 hTFv (by positivity) ?_ ?_ hK0 ?_
    · have := mul_le_mul_of_nonneg_right hσκ hr.le
      linarith
    · calc (σ * κ * r) ^ 2 = (σ ^ 2 * κ ^ 2) * r ^ 2 := by ring
        _ ≤ τ₂ * r ^ 2 := mul_le_mul_of_nonneg_right hσκτ hr2.le
    · refine le_inv_of_mul_le_one_O12 (by positivity) ?_
      have he : K * (r ^ 2)⁻¹ * (Real.sqrt 3 * (σ * κ * r)) ^ 2 =
          3 * σ ^ 2 * (κ ^ 2 * K) := by
        rw [show (Real.sqrt 3 * (σ * κ * r)) ^ 2 = 3 * (σ * κ * r) ^ 2 by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]]
        field_simp
      rwa [he]
  · by_cases heq : v = top
    · subst heq
      rw [X.endpoint_eq]
      refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc₁w (by positivity))).trans
        (hvol (σ * κ * r) (by positivity) ?_)
      have := mul_le_mul_of_nonneg_right hσκ hr.le
      linarith
    · have hlt : (v : ℝ) < top := lt_of_le_of_ne hvt (fun h => heq (Subtype.ext h))
      have hkr : 0 < κ * r := by positivity
      have hkr2 : 0 < (κ * r) ^ 2 := by positivity
      have hτpos : 0 < ((top : ℝ) - v) / (κ * r) ^ 2 := div_pos (by linarith) hkr2
      have hτle : ((top : ℝ) - v) / (κ * r) ^ 2 ≤ τ₀ := by
        rw [div_le_iff₀ hkr2]
        have he : κ ^ 2 * m * r ^ 2 = m * (κ * r) ^ 2 := by ring
        rw [he] at hv
        linarith [mul_le_mul_of_nonneg_right hmτ₀ hkr2.le]
      have hKr : K * (r ^ 2)⁻¹ ≤ ((κ * r) ^ 2)⁻¹ := by
        refine le_inv_of_mul_le_one_O12 hkr2 ?_
        have he : K * (r ^ 2)⁻¹ * (κ * r) ^ 2 = κ ^ 2 * K := by field_simp
        rwa [he]
      have hkr_le : κ * r ≤ r / 8 := by nlinarith
      have hwin : (top : ℝ) - τ₂ * r ^ 2 ≤ v := by
        linarith [mul_le_mul_of_nonneg_right hκm2 hr2.le]
      have hinputs := kl82_inputs_of_traced_family_O12 (hat := hat) X hK0 hkr_le hKr
        hTF v hav hvt hwin
      obtain ⟨_, hvolv⟩ := hkl H top x (κ * r) (((top : ℝ) - v) / (κ * r) ^ 2)
        (K * (r ^ 2)⁻¹) v hvt
        (X.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)) hPhi hpin
        hkr hτpos hτle (by field_simp; ring)
        (fun u hvu hut q hq => (hinputs u hvu hut q hq).1)
        (fun u hvu hut q hq => (hinputs u hvu hut q hq).2)
        (hvol (κ * r) hkr (by nlinarith))
      have hsecv : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (κ * r / 4),
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-((κ * r / 4) ^ 2)⁻¹) := by
        intro q hq
        refine (sectional_of_traced_O12 hTFv hK0 q
          (riemannianBallOf_mono _ _ (by linarith) hq)).mono ?_
        have hsmall : ((κ * r) ^ 2)⁻¹ ≤ ((κ * r / 4) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (by rw [div_pow]; linarith)
        linarith
      have har : σ * κ * r ≤ κ * r / 4 := by
        have := mul_le_mul_of_nonneg_right hσ4 hkr.le
        linarith
      obtain ⟨_, hvol'⟩ := hsd _ (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
        (w / 10) (κ * r / 4) (σ * κ * r) (by positivity) (by positivity) har hsecv (by
          rw [show w / 10 * (κ * r / 4) ^ 3 = w * (κ * r / 4) ^ 3 / 10 by ring]
          exact hvolv)
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hc₁sd (by positivity))).trans hvol'

end GC.LongTime.Ch12
