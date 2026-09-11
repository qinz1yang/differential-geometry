import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance
import DifferentialGeometry.Bundle.FiberBundleHausdorff











noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
theorem continuous_of_riemannian_lipschitz {X : Type*} [PseudoEMetricSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : X → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    Continuous u := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hl : LipschitzWith C u := hu
  exact hl.continuous

set_option backward.isDefEq.respectTransparency false in

theorem sqrt_metric_mfderiv_le [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {z : ℂ} (hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z) (w : ℂ) :
    Real.sqrt (g.inner (u z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z w)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z w)) ≤ C * ‖w‖ := by
  let : NeZero (Module.finrank ℝ ℂ) := ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := ℂ))⟩
  have h := metric_differential_le_of_edist_le (standardEuclideanMetric ℂ) g
    (u := id) (v := u) mdifferentiableAt_id hd (fun y => by
      simpa only [id_eq, riemannianEDistOf_standardEuclideanMetric] using hu z y) w
  have hs : Real.sqrt ((standardEuclideanMetric ℂ).inner z
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : ℂ → ℂ) z w)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : ℂ → ℂ) z w)) = ‖w‖ := by
    rw [mfderiv_id]
    change Real.sqrt (inner ℝ w w) = ‖w‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  exact h.trans_eq (congrArg (fun r : ℝ => (C : ℝ) * r) hs)

set_option backward.isDefEq.respectTransparency false in


theorem riemannianAreaDensity_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (z : ℂ) : riemannianAreaDensity g u z ≤ (C : ℝ) ^ 2 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := (Module.finrank_zero_iff).mp hdim
    let : Subsingleton (TangentSpace 𝓘(ℝ, E) (u z)) := ‹Subsingleton E›
    have hzero : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z = 0 := by ext; exact Subsingleton.elim _ _
    simp only [riemannianAreaDensity, hzero, zero_apply,
      tangentTwoJacobian, map_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
      Real.sqrt_zero]
    exact sq_nonneg _
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z
    · have h₁ := sqrt_metric_mfderiv_le g hu hd (1 : ℂ)
      have hI := sqrt_metric_mfderiv_le g hu hd Complex.I
      simp only [norm_one, Complex.norm_I, mul_one] at h₁ hI
      exact (tangentTwoJacobian_le g _ _).trans
        ((mul_le_mul h₁ hI (Real.sqrt_nonneg _) C.coe_nonneg).trans_eq (pow_two _).symm)
    · rw [riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hd]
      exact sq_nonneg _

theorem integrableOn_riemannianAreaDensity_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (s : Set ℂ) [IsFiniteMeasure (volume.restrict s)] :
    IntegrableOn (riemannianAreaDensity g u) s := by
  have hm := measurable_riemannianAreaDensity g (continuous_of_riemannian_lipschitz g hu)
  apply Integrable.mono' (integrable_const ((C : ℝ) ^ 2)) hm.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (riemannianAreaDensity_nonneg g u z)]
    exact riemannianAreaDensity_le_of_lipschitz g hu z)

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem diskExtension_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (x y : ℂ) : riemannianEDistOf g (diskExtension u x) (diskExtension u y) ≤
      (C : ℝ≥0∞) * edist x y := by
  apply (hu (diskRetraction x) (diskRetraction y)).trans
  have hd : edist (diskRetraction x) (diskRetraction y) ≤ edist x y := by
    simpa only [ENNReal.coe_one, one_mul] using diskRetraction_lipschitz x y
  gcongr

local instance : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
  isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne


theorem integrable_riemannianDiskAreaDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  integrableOn_riemannianAreaDensity_of_lipschitz g (diskExtension_riemannian_lipschitz g hu) _

theorem riemannianArea_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (s : Set ℂ) [IsFiniteMeasure (volume.restrict s)] :
    riemannianArea g u s ≤ (C : ℝ) ^ 2 * volume.real s := by
  have hi := integral_mono (integrableOn_riemannianAreaDensity_of_lipschitz g hu s)
    (integrable_const ((C : ℝ) ^ 2)) (riemannianAreaDensity_le_of_lipschitz g hu)
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_comm,
    Measure.real, riemannianArea] using hi

theorem riemannianDiskArea_le_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    riemannianDiskArea g u ≤ (C : ℝ) ^ 2 * volume.real (Metric.closedBall (0 : ℂ) 1) :=
  riemannianArea_le_of_lipschitz g (diskExtension_riemannian_lipschitz g hu) _

end DifferentialGeometry.Geometry
