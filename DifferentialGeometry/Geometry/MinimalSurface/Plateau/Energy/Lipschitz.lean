import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Directional
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E]

theorem measurable_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} (hu : Continuous u) :
    Measurable (diskMapEnergyDensity g u) := by
  have h1 := measurable_diskMapDirectionalEnergyDensity g hu
    (V := fun _ => (1 : ℂ)) measurable_const
  have hI := measurable_diskMapDirectionalEnergyDensity g hu
    (V := fun _ => Complex.I) measurable_const
  exact (h1.add hI).div_const 2

variable [T3Space M]

set_option backward.isDefEq.respectTransparency false in
theorem diskMapEnergyDensity_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (z : ℂ) : diskMapEnergyDensity g u z ≤ (C : ℝ) ^ 2 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := (Module.finrank_zero_iff).mp hdim
    let : Subsingleton (TangentSpace 𝓘(ℝ, E) (u z)) := ‹Subsingleton E›
    have hzero : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z = 0 := by ext; exact Subsingleton.elim _ _
    simp [diskMapEnergyDensity, diskMapPartial, hzero, zero_apply, map_zero]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z
    · have h₁ := sqrt_metric_mfderiv_le g hu hd (1 : ℂ)
      have hI := sqrt_metric_mfderiv_le g hu hd Complex.I
      simp only [norm_one, Complex.norm_I, mul_one] at h₁ hI
      have h₁sq := sq_le_sq₀ (Real.sqrt_nonneg _) C.coe_nonneg |>.mpr h₁
      have hIsq := sq_le_sq₀ (Real.sqrt_nonneg _) C.coe_nonneg |>.mpr hI
      rw [Real.sq_sqrt (metric_inner_self_nonneg g (u z) _)] at h₁sq hIsq
      unfold diskMapEnergyDensity diskMapPartial
      linarith
    · simp [diskMapEnergyDensity, diskMapPartial, mfderiv_zero_of_not_mdifferentiableAt hd,
          zero_apply, map_zero]

theorem integrableOn_diskMapEnergyDensity_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (s : Set ℂ) {μ : Measure ℂ} [IsFiniteMeasure (μ.restrict s)] :
    IntegrableOn (diskMapEnergyDensity g u) s μ := by
  have hm := measurable_diskMapEnergyDensity g (continuous_of_riemannian_lipschitz g hu)
  apply Integrable.mono' (integrable_const ((C : ℝ) ^ 2)) hm.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    have hn : 0 ≤ diskMapEnergyDensity g u z :=
      div_nonneg (add_nonneg (metric_inner_self_nonneg g (u z) _)
        (metric_inner_self_nonneg g (u z) _)) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact diskMapEnergyDensity_le_of_lipschitz g hu z)

theorem integrable_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1) := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  exact integrableOn_diskMapEnergyDensity_of_lipschitz g (diskExtension_riemannian_lipschitz g hu) _


theorem integral_diskMapEnergyDensity_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (s : Set ℂ) {μ : Measure ℂ} [IsFiniteMeasure (μ.restrict s)] :
    ∫ z in s, diskMapEnergyDensity g u z ∂μ ≤ (C : ℝ) ^ 2 * μ.real s := by
  have hi := integral_mono (integrableOn_diskMapEnergyDensity_of_lipschitz g hu s (μ := μ))
    (integrable_const ((C : ℝ) ^ 2)) (diskMapEnergyDensity_le_of_lipschitz g hu)
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_comm,
    Measure.real] using hi

theorem spanningDiskCompetitor_integrable_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨_, L, hL⟩ := hu
  exact integrable_diskMapEnergyDensity g hL

end DifferentialGeometry.Geometry
