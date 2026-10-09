import DifferentialGeometry.Geometry.Neck.ScalarControl
import DifferentialGeometry.Geometry.Neck.PointwiseMetric
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Function DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped ENNReal Manifold ContDiff
universe u v w
namespace DifferentialGeometry.Geometry.Neck
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem pointwise_scaled_error_bound {η c : ℝ} (hη : 0 < η)
    (hsmall : η ≤ 1 / 40000) (he : |c - 1| ≤ 4323 * η) :
    0 < c ∧ c * η + |c - 1| * Real.sqrt 3 < 20000 * η := by
  have hc := abs_le.mp he
  have hroot : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hcorr := mul_le_mul_of_nonneg_left hroot (abs_nonneg (c - 1))
  constructor
  · linarith
  · have hcη : c * η ≤ 2 * η :=
      mul_le_mul_of_nonneg_right (by linarith : c ≤ 2) hη.le
    nlinarith

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem pointwise_original_local {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (hm : ∀ x, Injective (mfderiv IC I Φ x)) :
    IsLocalDiffeomorph IC I ∞ Φ :=
  isLocalDiffeomorph_of_injective_mfderiv Φ hΦ hm (by
    rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp)

variable {L B d η : ℝ} {k : ℕ}
  (g : SmoothRiemannianMetric I M) (Φ : openCylinder L → M)
  (hΦ : ContMDiff IC I ∞ Φ) (hinj : Injective Φ)
  (hm : ∀ x, Injective (mfderiv IC I Φ x))
  (q : ℝ) (hq : 0 < q) (hk : 2 ≤ k)
  (hη : 0 < η) (hηsmall : η ≤ 1 / 40000)
  (herr : metricDerivENormSupOn {x : openCylinder L | x.val.2 ∈ Icc (-B) B} k
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ
      (pointwise_original_local Φ hΦ hm) hinj)
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L)) < ENNReal.ofReal η)
  (p : openCylinder L) (hd : 0 < d) (hd1 : d < 1)
  (hfit : |p.val.2| + d⁻¹ + 1 ≤ B) (hBL : B < L) (hηd : 20000 * η < d)

include hΦ hinj hm hq hk hηsmall herr hd hfit in
private theorem pointwise_scalar_ratio_bound :
    |metricScalarAt g (Φ p) / q - 1| ≤ 4323 * η := by
  apply abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt
    (openCylinder L) g Φ (pointwise_original_local Φ hΦ hm) hinj q hq
    {x : openCylinder L | x.val.2 ∈ Icc (-B) B} k hk η (by linarith only [hηsmall]) herr p
  change -B ≤ p.val.2 ∧ p.val.2 ≤ B
  have hi := inv_pos.mpr hd
  constructor <;> linarith only [hfit, hi, neg_abs_le p.val.2, le_abs_self p.val.2]

def pointwiseNormalizedDatum (e : E3 ≃ₗᵢ[ℝ] E3)
    (he : sphereDiffeo (n := 2) e spherePoint = p.val.1) :
    normalizedDatum g (Φ p) d k := by
  have hratio := pointwise_scalar_ratio_bound g Φ hΦ hinj hm q hq hk hηsmall herr p hd hfit
  have hb := pointwise_scaled_error_bound hη hηsmall hratio
  have hQ : 0 < metricScalarAt g (Φ p) := (div_pos_iff_of_pos_right hq).mp hb.1
  have hnew := pointwiseMetric_error_lt e p.val.2 hfit hBL
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ
      (pointwise_original_local Φ hΦ hm) hinj) k herr
  have heNorm := metricDerivENormSupOn_scaleMetric_left_lt (controlledCylinder d) k
    (metricScalarAt g (Φ p) / q) (div_pos hQ hq)
    (pointwiseMetric e p.val.2 hfit hBL
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ
        (pointwise_original_local Φ hΦ hm) hinj)) (referenceMetric d) hnew
  rw [scale_pointwiseMetric_eq_pullback g Φ hΦ hinj hm e p.val.2 hfit hBL q hq
    (metricScalarAt g (Φ p)) hQ] at heNorm
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ) = 3 := by norm_num
  rw [hdim] at heNorm
  refine
    { precision_pos := hd
      precision_lt_one := hd1
      map := pointwiseChart Φ e p.val.2 hfit hBL
      smooth := contMDiff_pointwiseChart Φ hΦ e p.val.2 hfit hBL
      injective := injective_pointwiseChart Φ hinj e p.val.2 hfit hBL
      immersion := immersion_pointwiseChart Φ hΦ hm e p.val.2 hfit hBL
      center_eq := ?_
      scalar_pos := hQ
      error_lt := heNorm.trans ((ENNReal.ofReal_lt_ofReal_iff hd).mpr (hb.2.trans hηd))
      retainedSide := true }
  convert pointwiseChart_center Φ e p.val.1 he p.val.2 hd hfit hBL using 1

theorem pointwiseNormalizedDatum_map (e : E3 ≃ₗᵢ[ℝ] E3)
    (he : sphereDiffeo (n := 2) e spherePoint = p.val.1) :
    (pointwiseNormalizedDatum g Φ hΦ hinj hm q hq hk hη hηsmall herr p hd hd1
      hfit hBL hηd e he).map = pointwiseChart Φ e p.val.2 hfit hBL := rfl

theorem pointwiseNormalizedDatum_retainedSide (e : E3 ≃ₗᵢ[ℝ] E3)
    (he : sphereDiffeo (n := 2) e spherePoint = p.val.1) :
    (pointwiseNormalizedDatum g Φ hΦ hinj hm q hq hk hη hηsmall herr p hd hd1
      hfit hBL hηd e he).retainedSide = true := rfl

include hΦ hinj hm hq hk hη hηsmall herr hd hfit in
theorem pointwiseNormalizedDatum_scalar_ratio :
    |metricScalarAt g (Φ p) / q - 1| ≤ 20000 * η := by
  have h := pointwise_scalar_ratio_bound g Φ hΦ hinj hm q hq hk hηsmall herr p hd hfit
  nlinarith only [h, hη]

end DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Geometry.Neck

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_pointwise_recentering :
    ∃ c ηpt : ℝ, 4 ≤ c ∧ 0 < ηpt ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        (H : Type v) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type w) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (L B : ℝ) (g : SmoothRiemannianMetric I M) (Φ : openCylinder L → M)
        (hΦ : ContMDiff IC I ∞ Φ) (hinj : Injective Φ)
        (hm : ∀ x, Injective (mfderiv IC I Φ x)) (q : ℝ) (hq : 0 < q)
        (k : ℕ), 2 ≤ k → ∀ η : ℝ, 0 < η → η ≤ ηpt →
        metricDerivENormSupOn {x : openCylinder L | x.val.2 ∈ Icc (-B) B} k
          (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ
            (pointwise_original_local Φ hΦ hm) hinj)
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L))
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L)) <
            ENNReal.ofReal η →
        ∀ (p : openCylinder L) (d : ℝ), 0 < d → d < 1 →
        ∀ (hfit : |p.val.2| + d⁻¹ + 1 ≤ B) (hBL : B < L), c * η < d →
          ∃ e : E3 ≃ₗᵢ[ℝ] E3, LinearMap.det e.toLinearMap = 1 ∧
            sphereDiffeo (n := 2) e spherePoint = p.val.1 ∧
            ∃ D : normalizedDatum g (Φ p) d k,
              D.map = pointwiseChart Φ e p.val.2 hfit hBL ∧ D.retainedSide = true ∧
              |metricScalarAt g (Φ p) / q - 1| ≤ c * η := by
  refine ⟨20000, 1 / 40000, by norm_num, by norm_num, ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ L B g Φ hΦ hinj hm q hq k hk η hη hηsmall herr
    p d hd hd1 hfit hBL hηd
  obtain ⟨e, hdet, he⟩ := exists_sphereDiffeo_det_one (n := 2) (by norm_num) spherePoint p.val.1
  exact ⟨e, hdet, he,
    pointwiseNormalizedDatum g Φ hΦ hinj hm q hq hk hη hηsmall herr p hd hd1 hfit hBL hηd e he,
    pointwiseNormalizedDatum_map g Φ hΦ hinj hm q hq hk hη hηsmall herr p hd hd1 hfit hBL hηd e he,
    pointwiseNormalizedDatum_retainedSide g Φ hΦ hinj hm q hq hk hη hηsmall herr p hd hd1
      hfit hBL hηd e he,
    pointwiseNormalizedDatum_scalar_ratio g Φ hΦ hinj hm q hq hk hη hηsmall herr p hd hfit⟩

end DifferentialGeometry.Geometry.Neck
