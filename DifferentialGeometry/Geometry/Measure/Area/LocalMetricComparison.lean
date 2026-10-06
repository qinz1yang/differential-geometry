import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz

/-! # Area comparison from metric bounds along the image

Quadratic-form bounds are needed only at points visited by the parametrization.
In dimension two the area multiplier is the quadratic-form multiplier itself.
-/

noncomputable section

open Bundle Manifold DifferentialGeometry Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

section Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianAreaDensity_metric_upper_at
    (g h : SmoothRiemannianMetric I M) {u : ℂ → M} {z : ℂ} {c : ℝ}
    (hc : 0 < c)
    (hgh : ∀ v : TangentSpace I (u z), h.inner (u z) v v ≤ c * g.inner (u z) v v) :
    riemannianAreaDensity h u z ≤ c * riemannianAreaDensity g u z := by
  rw [← riemannianAreaDensity_scaleMetric g c hc]
  exact tangentTwoJacobian_mono h (scaleMetric c hc g)
    (fun v => by simpa only [scaleMetric_inner] using hgh v) _ _

theorem riemannianAreaDensity_metric_lower_at
    (g h : SmoothRiemannianMetric I M) {u : ℂ → M} {z : ℂ} {c : ℝ}
    (hc : 0 < c)
    (hgh : ∀ v : TangentSpace I (u z), c * g.inner (u z) v v ≤ h.inner (u z) v v) :
    c * riemannianAreaDensity g u z ≤ riemannianAreaDensity h u z := by
  rw [← riemannianAreaDensity_scaleMetric g c hc]
  exact tangentTwoJacobian_mono (scaleMetric c hc g) h
    (fun v => by simpa only [scaleMetric_inner] using hgh v) _ _

theorem riemannianAreaDensity_metric_relative_error_at
    (g h : SmoothRiemannianMetric I M) {u : ℂ → M} {z : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hgh : ∀ v : TangentSpace I (u z),
      |h.inner (u z) v v - g.inner (u z) v v| ≤ δ * g.inner (u z) v v) :
    |riemannianAreaDensity h u z - riemannianAreaDensity g u z| ≤
      δ * riemannianAreaDensity g u z := by
  have hup := riemannianAreaDensity_metric_upper_at g h (u := u) (z := z)
    (by linarith : 0 < 1 + δ)
    (fun v => by have hv := (abs_le.mp (hgh v)).2; linarith)
  have hlo : (1 - δ) * riemannianAreaDensity g u z ≤ riemannianAreaDensity h u z := by
    by_cases hd : δ < 1
    · exact riemannianAreaDensity_metric_lower_at g h (by linarith : 0 < 1 - δ)
        (fun v => by have hv := (abs_le.mp (hgh v)).1; linarith)
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (riemannianAreaDensity_nonneg g u z)).trans (riemannianAreaDensity_nonneg h u z)
  rw [abs_le]
  constructor <;> linarith

end Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem integrableOn_riemannianAreaDensity_of_metric_upper_on
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u)
    {s : Set ℂ} (hs : MeasurableSet s)
    (hi : IntegrableOn (riemannianAreaDensity g u) s) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ z ∈ s, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      h.inner (u z) v v ≤ c * g.inner (u z) v v) :
    IntegrableOn (riemannianAreaDensity h u) s := by
  apply Integrable.mono' (hi.const_mul c) (measurable_riemannianAreaDensity h hu).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (riemannianAreaDensity_nonneg h u z)]
  exact riemannianAreaDensity_metric_upper_at g h hc (hgh z hz)

theorem riemannianArea_metric_upper_on
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u)
    {s : Set ℂ} (hs : MeasurableSet s)
    (hi : IntegrableOn (riemannianAreaDensity g u) s) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ z ∈ s, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      h.inner (u z) v v ≤ c * g.inner (u z) v v) :
    riemannianArea h u s ≤ c * riemannianArea g u s := by
  have hih := integrableOn_riemannianAreaDensity_of_metric_upper_on g h hu hs hi hc hgh
  have hb := setIntegral_mono_on hih (hi.const_mul c) hs
    (fun z hz => riemannianAreaDensity_metric_upper_at g h hc (hgh z hz))
  simpa only [riemannianArea, integral_const_mul] using hb

theorem riemannianArea_metric_bounds_on
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u)
    {s : Set ℂ} (hs : MeasurableSet s)
    (hi : IntegrableOn (riemannianAreaDensity g u) s) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ z ∈ s, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      a * g.inner (u z) v v ≤ h.inner (u z) v v)
    (hhi : ∀ z ∈ s, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      h.inner (u z) v v ≤ b * g.inner (u z) v v) :
    a * riemannianArea g u s ≤ riemannianArea h u s ∧
      riemannianArea h u s ≤ b * riemannianArea g u s := by
  refine ⟨?_, riemannianArea_metric_upper_on g h hu hs hi hb hhi⟩
  have hih := integrableOn_riemannianAreaDensity_of_metric_upper_on g h hu hs hi hb hhi
  have hl := setIntegral_mono_on (hi.const_mul a) hih hs
    (fun z hz => riemannianAreaDensity_metric_lower_at g h ha (hlo z hz))
  simpa only [riemannianArea, integral_const_mul] using hl

theorem riemannianArea_metric_relative_error_on
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u)
    {s : Set ℂ} (hs : MeasurableSet s)
    (hi : IntegrableOn (riemannianAreaDensity g u) s) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgh : ∀ z ∈ s, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      |h.inner (u z) v v - g.inner (u z) v v| ≤ δ * g.inner (u z) v v) :
    |riemannianArea h u s - riemannianArea g u s| ≤ δ * riemannianArea g u s := by
  have hih := integrableOn_riemannianAreaDensity_of_metric_upper_on g h hu hs hi
    (by linarith : 0 < 1 + δ)
    (fun z hz v => by have hv := (abs_le.mp (hgh z hz v)).2; linarith)
  have herr := norm_integral_le_of_norm_le (hi.const_mul δ) (f := fun z =>
    riemannianAreaDensity h u z - riemannianAreaDensity g u z) (by
      filter_upwards [ae_restrict_mem hs] with z hz
      rw [Real.norm_eq_abs]
      exact riemannianAreaDensity_metric_relative_error_at g h hδ (hgh z hz))
  simpa only [integral_sub hih hi, integral_const_mul, Real.norm_eq_abs, riemannianArea] using herr

variable [T3Space M]

theorem riemannianDiskArea_metric_bounds_on_image
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ z : closedDisk, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      a * g.inner (u z) v v ≤ h.inner (u z) v v)
    (hhi : ∀ z : closedDisk, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      h.inner (u z) v v ≤ b * g.inner (u z) v v) :
    a * riemannianDiskArea g u ≤ riemannianDiskArea h u ∧
      riemannianDiskArea h u ≤ b * riemannianDiskArea g u :=
  riemannianArea_metric_bounds_on g h
    (continuous_of_riemannian_lipschitz g (diskExtension_riemannian_lipschitz g hu))
    measurableSet_closedBall (integrable_riemannianDiskAreaDensity g hu) ha hb
    (fun z _ => hlo (diskRetraction z)) (fun z _ => hhi (diskRetraction z))

theorem riemannianDiskArea_metric_relative_error_on_image
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hgh : ∀ z : closedDisk, ∀ v : TangentSpace 𝓘(ℝ, E) (u z),
      |h.inner (u z) v v - g.inner (u z) v v| ≤ δ * g.inner (u z) v v) :
    |riemannianDiskArea h u - riemannianDiskArea g u| ≤ δ * riemannianDiskArea g u :=
  riemannianArea_metric_relative_error_on g h
    (continuous_of_riemannian_lipschitz g (diskExtension_riemannian_lipschitz g hu))
    measurableSet_closedBall (integrable_riemannianDiskAreaDensity g hu) hδ
    (fun z _ => hgh (diskRetraction z))

end DifferentialGeometry.Geometry
