import DifferentialGeometry.Geometry.Neck.ScalarControl
import DifferentialGeometry.Geometry.Neck.RecenteringMetric
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

set_option autoImplicit false
noncomputable section
open Set Function DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped ENNReal Manifold ContDiff
universe u v w
namespace DifferentialGeometry.Geometry.Neck

private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

private theorem recentering_precision_bounds {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / 40000) :
    0 < 20000 * δ ∧ 20000 * δ < 1 ∧
      (20000 * δ)⁻¹ + 1 ≤ δ⁻¹ ∧ δ ≤ 1 / 2 ∧ 4323 * δ < 1 := by
  have hprod : 0 < 20000 * δ := by positivity
  refine ⟨hprod, by linarith, ?_, by linarith, by linarith⟩
  rw [mul_inv_rev]
  apply (mul_le_mul_iff_right₀ hδ).mp
  field_simp
  linarith

private theorem recentering_scaled_error_bound {δ c : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / 40000) (he : |c - 1| ≤ 4323 * δ) :
    0 < c ∧ c * δ + |c - 1| * Real.sqrt 3 < 20000 * δ := by
  have hc := abs_le.mp he
  have hroot : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hcorr := mul_le_mul_of_nonneg_left hroot (abs_nonneg (c - 1))
  constructor
  · linarith
  · have hcδ : c * δ ≤ 2 * δ :=
      mul_le_mul_of_nonneg_right (by linarith : c ≤ 2) hδ.le
    nlinarith

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum
variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

def offsetPoint (d : normalizedDatum g x₀ δ k) {σ : ℝ} (hσ : σ ^ 2 = 1) : M :=
  d.map ⟨(spherePoint, σ), offset_mem_bufferedCylinder d.precision_pos hσ spherePoint⟩

private theorem offset_mem_controlled (d : normalizedDatum g x₀ δ k) {σ : ℝ}
    (hσ : σ ^ 2 = 1) :
    (⟨(spherePoint, σ), offset_mem_bufferedCylinder d.precision_pos hσ spherePoint⟩ :
      bufferedCylinder δ) ∈ controlledCylinder δ := by
  change -δ⁻¹ ≤ σ ∧ σ ≤ δ⁻¹
  have hi := (one_le_inv₀ d.precision_pos).mpr d.precision_lt_one.le
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> constructor <;> linarith

def recentered (d : normalizedDatum g x₀ δ k) (hk : 2 ≤ k)
    (hsmall : δ ≤ 1 / 40000) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    normalizedDatum g (d.offsetPoint hσ) (20000 * δ) k := by
  have hb := recentering_precision_bounds d.precision_pos hsmall
  have hε := hb.1
  have hε1 := hb.2.1
  have hfit := hb.2.2.1
  have hδhalf := hb.2.2.2.1
  have herr := hb.2.2.2.2
  have hq : 0 < metricScalarAt g (d.offsetPoint hσ) :=
    d.scalar_pos_of_controlled hk herr _ (d.offset_mem_controlled hσ)
  have hratio : |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤
      4323 * δ := d.abs_scalar_ratio_sub_one_le hk hδhalf _ (d.offset_mem_controlled hσ)
  have hbound := recentering_scaled_error_bound d.precision_pos hsmall hratio
  have he := metricDerivENormSupOn_scaleMetric_left_lt (controlledCylinder (20000 * δ)) k
    (metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀)
    (div_pos hq d.scalar_pos) (recenteringMetric hσ hfit d.normalizedMetric)
    (referenceMetric (20000 * δ)) (d.recenteringMetric_error_lt hσ hfit)
  rw [d.scale_recenteringMetric_eq_pullback hσ hfit (metricScalarAt g (d.offsetPoint hσ)) hq] at he
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ) = 3 := by norm_num
  rw [hdim] at he
  refine
    { precision_pos := hε
      precision_lt_one := hε1
      map := d.recenteringMap hσ hfit
      smooth := d.contMDiff_recenteringMap hσ hfit
      injective := d.injective_recenteringMap hσ hfit
      immersion := d.immersion_recenteringMap hσ hfit
      center_eq := d.recenteringMap_center hε hσ hfit
      scalar_pos := hq
      retainedSide := true
      error_lt := ?_ }
  exact he.trans ((ENNReal.ofReal_lt_ofReal_iff hε).mpr hbound.2)

theorem recentered_map (d : normalizedDatum g x₀ δ k) (hk : 2 ≤ k)
    (hsmall : δ ≤ 1 / 40000) {σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : (20000 * δ)⁻¹ + 1 ≤ δ⁻¹) :
    (d.recentered hk hsmall hσ).map = d.recenteringMap hσ hfit := rfl

theorem recentered_retainedSide (d : normalizedDatum g x₀ δ k) (hk : 2 ≤ k)
    (hsmall : δ ≤ 1 / 40000) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    (d.recentered hk hsmall hσ).retainedSide = true := rfl

theorem recentered_scalar_ratio (d : normalizedDatum g x₀ δ k) (hk : 2 ≤ k)
    (hsmall : δ ≤ 1 / 40000) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ 20000 * δ := by
  have hhalf : δ ≤ 1 / 2 := by linarith
  have he := d.abs_scalar_ratio_sub_one_le hk hhalf _ (d.offset_mem_controlled hσ)
  change |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ 4323 * δ at he
  nlinarith [d.precision_pos]

end normalizedDatum
end DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Geometry.Neck

theorem exists_fixed_offset_recentering :
    ∃ c δrec : ℝ, 4 ≤ c ∧ 0 < δrec ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        (H : Type v) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type w) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I M) (x₀ : M) (δ : ℝ) (k : ℕ)
        (d : normalizedDatum g x₀ δ k), 2 ≤ k → δ ≤ δrec →
        ∀ (σ : ℝ) (hσ : σ ^ 2 = 1),
          ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
            ∃ d' : normalizedDatum g (d.offsetPoint hσ) (c * δ) k,
              d'.map = d.recenteringMap hσ hfit ∧ d'.retainedSide = true ∧
              |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ c * δ := by
  refine ⟨20000, 1 / 40000, by norm_num, by norm_num, ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ g x₀ δ k d hk hsmall σ hσ
  have hfit := (recentering_precision_bounds d.precision_pos hsmall).2.2.1
  exact ⟨hfit, d.recentered hk hsmall hσ, d.recentered_map hk hsmall hσ hfit,
    d.recentered_retainedSide hk hsmall hσ, d.recentered_scalar_ratio hk hsmall hσ⟩

end DifferentialGeometry.Geometry.Neck
