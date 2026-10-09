import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Glue_O12

/-!
# CH12-S96, group 1: the seed family from KL82.1 and a traced family at the centre

The hG2-glue core of `hG2_of_kl82_v3_O22` (CH12-O22) factored out of its slice/ball-selection frame:
for ANY observed history `H`, time `top`, centre `y` with a backward traced family `X` (radius `r0/40`,
the shape of `hG2c v2`) and volume `w ρ'³` at the top for `ρ' ≤ r0`, KL82.1 (`hKL82`) at every `v` of a
window `[top - c r0², top]` yields the per-time seeds of `traced_of_seeds_*`
(small parabolic curvature at scale `a r0`, volume `c₁ (a r0)³`, and the trace of `y`).
Constants `a = σκ`, `c = κ² m`, `c₁` depend only on `w`, `K τ₁ τ₂` and `hKL82`.
-/

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

theorem seeds_core_S96
    (hKL82 : ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
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
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {w K τ₁ τ₂ : ℝ} (hw : 0 < w) (hK : 0 < K) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    ∃ a c c₁ : ℝ, 0 < a ∧ 2 * a ^ 2 < c ∧ 0 < c₁ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon),
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
        ∀ (y : (H.stageAt top).Carrier) (r0 : ℝ), 0 < r0 →
        ∀ (a' : Icc (0 : ℝ) H.horizon) (hat : a' ≤ top)
          (X : BackwardPointTrace H (H.activeStage a') (H.activeStage top)
            (H.activeStage_mono hat) y),
          (a' : ℝ) = top - τ₁ * r0 ^ 2 →
          (∀ (u : Icc (0 : ℝ) H.horizon) (hau : a' ≤ u) (hut : u ≤ top),
            H.isTracedRegion u
              (X.point (H.activeStage u) (H.activeStage_mono hau) (H.activeStage_mono hut))
              (r0 / 40) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) →
          (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ r0 →
            ENNReal.ofReal (w * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage top) top) y ρ') →
          ∀ (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ top), (top : ℝ) - c * r0 ^ 2 ≤ v.val →
            ∃ yv : (H.stageAt v).Carrier,
              (v.val = top → HEq yv y) ∧
              hasSmallParabolicCurvature H v yv (a * r0) ∧
              ENNReal.ofReal (c₁ * (a * r0) ^ 3) ≤
                ballVolume (H.stageMetric (H.activeStage v) v) yv (a * r0) ∧
              ∃ A : BackwardPointTrace H (H.activeStage v) (H.activeStage top)
                  (H.activeStage_mono hvt) y,
                A.point (H.activeStage v) le_rfl
                  (H.activeStage_mono hvt) = yv := by
  obtain ⟨τ₀, K₀, hτ₀, _, _, hkl⟩ := hKL82 w hw
  obtain ⟨csd, hcsd, hsd⟩ := seed_scale_down_S21.{u}
  set κ : ℝ := min (1 / 40) (min τ₂ (1 / (K + 1))) with hκdef
  have hκ : 0 < κ := lt_min (by norm_num) (lt_min hτ₂ (by positivity))
  have hκ40 : κ ≤ 1 / 40 := min_le_left _ _
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
  have hσκ : σ * κ ≤ 1 / 80 := by
    have := mul_le_mul hσ2 hκ40 hκ.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hκ2τ : κ ^ 2 ≤ τ₂ := by
    calc κ ^ 2 = κ * κ := sq κ
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hκ1 hκ.le
      _ ≤ τ₂ := by linarith
  have hσκτ : σ ^ 2 * κ ^ 2 ≤ τ₂ := by
    have := mul_le_mul_of_nonneg_right hσsq (sq_nonneg κ)
    linarith
  have h3σκK : 3 * σ ^ 2 * (κ ^ 2 * K) ≤ 1 := by
    have := mul_le_mul hσsq hκ2K (by positivity) (by norm_num)
    linarith
  set c₁ : ℝ := min (csd * (w / 10)) w with hc₁def
  have hc₁ : 0 < c₁ := lt_min (by positivity) hw
  have hc₁sd : c₁ ≤ csd * (w / 10) := min_le_left _ _
  have hc₁w : c₁ ≤ w := min_le_right _ _
  refine ⟨σ * κ, κ ^ 2 * m, c₁, by positivity, ?_, hc₁, ?_⟩
  · have hkt : 0 < κ ^ 2 := by positivity
    have e : 2 * (σ * κ) ^ 2 = 2 * σ ^ 2 * κ ^ 2 := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hσ2m hkt.le
    have h2 := mul_pos hm hkt
    nlinarith [h1, h2]
  intro H top hpin y r0 hr0 a' hat X haeq hTF hyvol v hvt hv
  have hvR : (v : ℝ) ≤ top := hvt
  have hr0sq : 0 < r0 ^ 2 := by positivity
  have hav : a' ≤ v := by
    change (a' : ℝ) ≤ v
    rw [haeq]
    linarith [mul_le_mul_of_nonneg_right hκm1 hr0sq.le]
  have hTFv := hTF v hav hvt
  have hK0 : 0 ≤ K * (r0 ^ 2)⁻¹ := by positivity
  refine ⟨X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt), ?_, ?_, ?_,
    X.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt), rfl⟩
  · intro hvt'
    have hveq : v = top := Subtype.ext hvt'
    subst hveq
    exact heq_of_eq X.endpoint_eq
  · refine hasSmall_of_traced_S23 hTFv (by positivity) ?_ ?_ hK0 ?_
    · have := mul_le_mul_of_nonneg_right hσκ hr0.le
      linarith
    · calc (σ * κ * r0) ^ 2 = (σ ^ 2 * κ ^ 2) * r0 ^ 2 := by ring
        _ ≤ τ₂ * r0 ^ 2 := mul_le_mul_of_nonneg_right hσκτ hr0sq.le
    · refine le_inv_of_mul_le_one_O12 (by positivity) ?_
      have e : K * (r0 ^ 2)⁻¹ * (Real.sqrt 3 * (σ * κ * r0)) ^ 2 =
          3 * σ ^ 2 * (κ ^ 2 * K) := by
        rw [show (Real.sqrt 3 * (σ * κ * r0)) ^ 2 = 3 * (σ * κ * r0) ^ 2 by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]]
        field_simp
      rw [e]
      exact h3σκK
  · by_cases hvt' : (v : ℝ) = top
    · have hveq : v = top := Subtype.ext hvt'
      subst hveq
      have he : X.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt) = y := X.endpoint_eq
      rw [he]
      refine (ENNReal.ofReal_le_ofReal ?_).trans
        (hyvol (σ * κ * r0) (by positivity) ?_)
      · have h3 : 0 ≤ (σ * κ * r0) ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_right hc₁w h3
        exact this
      · have := mul_le_mul_of_nonneg_right hσκ hr0.le
        linarith
    · have hvlt : (v : ℝ) < top := lt_of_le_of_ne hvR hvt'
      have hr1 : 0 < κ * r0 := by positivity
      have hr1sq : 0 < (κ * r0) ^ 2 := by positivity
      have hτpos : 0 < (top - v) / (κ * r0) ^ 2 := div_pos (by linarith) hr1sq
      have hτle : (top - v) / (κ * r0) ^ 2 ≤ τ₀ := by
        rw [div_le_iff₀ hr1sq]
        have e : κ ^ 2 * m * r0 ^ 2 = m * (κ * r0) ^ 2 := by ring
        linarith [mul_le_mul_of_nonneg_right hmτ₀ hr1sq.le]
      have hKr1 : K * (r0 ^ 2)⁻¹ ≤ ((κ * r0) ^ 2)⁻¹ := by
        refine le_inv_of_mul_le_one_O12 hr1sq ?_
        have e : K * (r0 ^ 2)⁻¹ * (κ * r0) ^ 2 = κ ^ 2 * K := by
          field_simp
        rw [e]
        exact hκ2K
      have hr1le : κ * r0 ≤ 1 / 40 * r0 := mul_le_mul_of_nonneg_right hκ40 hr0.le
      have hr1ρ : κ * r0 ≤ r0 / 40 := by linarith
      have hwin : ((top : Icc (0 : ℝ) H.horizon) : ℝ) - τ₂ * r0 ^ 2 ≤ v := by
        linarith [mul_le_mul_of_nonneg_right hκm2 hr0sq.le]
      have hinputs := kl82_inputs_of_traced_family_O12 (hat := hat) X hK0 hr1ρ hKr1 hTF v hav hvt hwin
      have htopvol : ENNReal.ofReal (w * (κ * r0) ^ 3) ≤ ballVolume
          (H.stageMetric (H.activeStage top) top) y (κ * r0) :=
        hyvol (κ * r0) hr1 (by linarith)
      obtain ⟨_, hvolv⟩ := hkl H top y (κ * r0)
        ((top - v) / (κ * r0) ^ 2) (K * (r0 ^ 2)⁻¹) v hvt
        (X.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt))
        hPhi hpin hr1 hτpos hτle (by
          field_simp
          ring) (fun u hvu hut q hq => (hinputs u hvu hut q hq).1)
        (fun u hvu hut q hq => (hinputs u hvu hut q hq).2) htopvol
      have hsecv : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) (κ * r0 / 4),
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q
            (-((κ * r0 / 4) ^ 2)⁻¹) := by
        intro q hq
        refine (sectional_of_traced_O12 hTFv hK0 q
          (riemannianBallOf_mono _ _ (by linarith) hq)).mono ?_
        have h1 : ((κ * r0) ^ 2)⁻¹ ≤ ((κ * r0 / 4) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (by rw [div_pow]; linarith)
        linarith
      have har : σ * κ * r0 ≤ κ * r0 / 4 := by
        have := mul_le_mul_of_nonneg_right hσ4 hr1.le
        linarith
      obtain ⟨_, hvol'⟩ := hsd _ (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))
        (w / 10) (κ * r0 / 4) (σ * κ * r0) (by positivity) (by positivity)
        har hsecv (by
          rw [show w / 10 * (κ * r0 / 4) ^ 3 = w * (κ * r0 / 4) ^ 3 / 10 by ring]
          exact hvolv)
      refine (ENNReal.ofReal_le_ofReal ?_).trans hvol'
      have h3 : 0 ≤ (σ * κ * r0) ^ 3 := by positivity
      linarith [mul_le_mul_of_nonneg_right hc₁sd h3]

end GC.LongTime.Ch12
