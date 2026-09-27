import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz



noncomputable section

open Bundle Manifold DifferentialGeometry Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem integrableOn_riemannianAreaDensity_of_metric_upper
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u)
    {s : Set ℂ} (hi : IntegrableOn (riemannianAreaDensity g u) s) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ c * g.inner x v v) :
    IntegrableOn (riemannianAreaDensity h u) s := by
  apply Integrable.mono' (hi.const_mul c) (measurable_riemannianAreaDensity h hu).aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (riemannianAreaDensity_nonneg h u z)]
    exact riemannianAreaDensity_metric_upper g h hc hgh u z)

variable [T3Space M]


theorem riemannianArea_metric_bounds
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), a ^ 2 * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ b ^ 2 * g.inner x v v)
    (s : Set ℂ) [IsFiniteMeasure (volume.restrict s)] :
    a ^ 2 * riemannianArea g u s ≤ riemannianArea h u s ∧
      riemannianArea h u s ≤ b ^ 2 * riemannianArea g u s := by
  have hig := integrableOn_riemannianAreaDensity_of_lipschitz g hu s
  have hih := integrableOn_riemannianAreaDensity_of_metric_upper g h
    (continuous_of_riemannian_lipschitz g hu) hig (sq_pos_of_pos hb) hhi
  constructor
  · have hi := integral_mono (hig.const_mul (a ^ 2)) hih
      (riemannianAreaDensity_metric_lower g h (sq_pos_of_pos ha) hlo u)
    simpa only [integral_const_mul, riemannianArea] using hi
  · have hi := integral_mono hih (hig.const_mul (b ^ 2))
      (riemannianAreaDensity_metric_upper g h (sq_pos_of_pos hb) hhi u)
    simpa only [integral_const_mul, riemannianArea] using hi

local instance : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
  isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne

theorem riemannianDiskArea_metric_bounds
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), a ^ 2 * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ b ^ 2 * g.inner x v v) :
    a ^ 2 * riemannianDiskArea g u ≤ riemannianDiskArea h u ∧
      riemannianDiskArea h u ≤ b ^ 2 * riemannianDiskArea g u :=
  riemannianArea_metric_bounds g h (diskExtension_riemannian_lipschitz g hu) ha hb hlo hhi _

end DifferentialGeometry.Geometry
