import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher

section

noncomputable section

open Manifold Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_sq_le_two_mul_norm_one_sq_add_norm_I_sq (A : ℂ →L[ℝ] F) :
    ‖A‖ ^ 2 ≤ 2 * (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) := by
  have hA : ‖A‖ ≤ ‖A 1‖ + ‖A Complex.I‖ := by
    refine A.opNorm_le_bound (by positivity) fun z => ?_
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    have hAz := congrArg A hz
    simp only [map_add, map_smul] at hAz
    calc
      ‖A z‖ ≤ |z.re| * ‖A 1‖ + |z.im| * ‖A Complex.I‖ := by
        rw [hAz]
        simpa only [norm_smul, Real.norm_eq_abs] using
          norm_add_le (z.re • A 1) (z.im • A Complex.I)
      _ ≤ ‖z‖ * ‖A 1‖ + ‖z‖ * ‖A Complex.I‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
      _ = (‖A 1‖ + ‖A Complex.I‖) * ‖z‖ := by ring
  have hsq := mul_self_le_mul_self (norm_nonneg A) hA
  nlinarith [sq_nonneg (‖A 1‖ - ‖A Complex.I‖)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem norm_fderiv_comp_sq_le_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} {C : ℝ≥0}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    (hC : ∀ p (v : TangentSpace 𝓘(ℝ, E) p),
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ p v : F)‖ ≤ C * Real.sqrt (g.inner p v v))
    {u : ℂ → M} {z : ℂ} (hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z) :
    ‖fderiv ℝ (Φ ∘ u) z‖ ^ 2 ≤ 4 * (C : ℝ) ^ 2 * diskMapEnergyDensity g u z := by
  have hchain : fderiv ℝ (Φ ∘ u) z =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ (u z)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z) := by
    have h := mfderiv_comp z (hΦ.mdifferentiableAt one_ne_zero) hu
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (Φ (u z))
      (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v))) h
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using! hv
  have hdir (v : ℂ) : ‖fderiv ℝ (Φ ∘ u) z v‖ ^ 2 ≤
      (C : ℝ) ^ 2 * g.inner (u z) (diskMapPartial u z v) (diskMapPartial u z v) := by
    rw [hchain]
    change ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ (u z)) (diskMapPartial u z v)‖ ^ 2 ≤ _
    have h := hC (u z) (diskMapPartial u z v)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg C.coe_nonneg (Real.sqrt_nonneg _))).mpr h
    simpa only [mul_pow, Real.sq_sqrt (metric_inner_self_nonneg g (u z) _)] using hs
  have hnorm := norm_sq_le_two_mul_norm_one_sq_add_norm_I_sq (fderiv ℝ (Φ ∘ u) z)
  have h₁ := hdir 1
  have hI := hdir Complex.I
  unfold diskMapEnergyDensity
  nlinarith

variable [T2Space M] [CompactSpace M]

theorem exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : ℂ → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      LipschitzWith (C * K) (Φ ∘ u) ∧
        ∀ᵐ z ∂volume,
          ‖fderiv ℝ (Φ ∘ u) z‖ ^ 2 ≤ 4 * (C : ℝ) ^ 2 * diskMapEnergyDensity g u z := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound g hΦ
  let C : ℝ≥0 := B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ p (v : TangentSpace 𝓘(ℝ, E) p),
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ p v : F)‖ ≤ C * Real.sqrt (g.inner p v v) := by
    intro p v
    exact (hB p v).trans (mul_le_mul_of_nonneg_right (by simp [C]) (Real.sqrt_nonneg _))
  have hdist := edist_map_le_of_metric_mfderiv_bound g hC hΦ hbound
  refine ⟨C, hC, fun u K hu => ⟨?_, ?_⟩⟩
  · intro x y
    apply (hdist (u x) (u y)).trans
    calc
      (C : ℝ≥0∞) * riemannianEDistOf g (u x) (u y) ≤
          (C : ℝ≥0∞) * ((K : ℝ≥0∞) * edist x y) := by gcongr; exact hu x y
      _ = (↑(C * K) : ℝ≥0∞) * edist x y := by simp only [ENNReal.coe_mul, mul_assoc]
  · filter_upwards [ae_mdifferentiableAt_of_riemannian_lipschitz g hu] with z hz
    exact norm_fderiv_comp_sq_le_diskMapEnergyDensity g hΦ hbound hz

variable [CompleteSpace F]

theorem exists_integral_norm_fderiv_comp_diskExtension_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : closedDisk → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      LipschitzWith (C * K) (Φ ∘ diskExtension u) ∧
        IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2)
          (Metric.closedBall (0 : ℂ) 1) ∧
        (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) ≤
          4 * (C : ℝ) ^ 2 *
            ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  obtain ⟨C, hC, hbound⟩ := exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le g hΦ
  refine ⟨C, hC, fun u K hu => ?_⟩
  obtain ⟨hL, hpoint⟩ := hbound (diskExtension u) K (diskExtension_riemannian_lipschitz g hu)
  have he := integrable_diskMapEnergyDensity g hu
  have hpoint' := ae_restrict_of_ae (s := Metric.closedBall (0 : ℂ) 1) hpoint
  have hi : IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2)
      (Metric.closedBall (0 : ℂ) 1) := by
    apply Integrable.mono' (he.const_mul (4 * (C : ℝ) ^ 2))
      (((measurable_fderiv ℝ (Φ ∘ diskExtension u)).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [hpoint'] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hL, hi, ?_⟩
  simpa only [integral_const_mul] using
    integral_mono_ae hi (he.const_mul (4 * (C : ℝ) ^ 2)) hpoint'

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ F] [T2Space M]

theorem integrableOn_norm_fderiv_comp_of_hasCompactSupport_of_disk_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) (hΦs : HasCompactSupport Φ)
    {u : ℂ → M} (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 u (Metric.ball (0 : ℂ) 1))
    (hE : IntegrableOn (diskMapEnergyDensity g u) (Metric.ball (0 : ℂ) 1)) :
    IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ u) z‖ ^ 2) (Metric.ball (0 : ℂ) 1) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  obtain ⟨C, hC⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g hΦ hΦs
  apply Integrable.mono' (hE.const_mul (4 * (C : ℝ) ^ 2))
    ((measurable_fderiv ℝ (Φ ∘ u)).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact norm_fderiv_comp_sq_le_diskMapEnergyDensity g hΦ hC
    ((hu.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt one_ne_zero)

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Manifold Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable [T3Space M]

theorem exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le_of_hasCompactSupport
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : ℂ → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      LipschitzWith (C * K) (Φ ∘ u) ∧
        ∀ᵐ z ∂volume,
          ‖fderiv ℝ (Φ ∘ u) z‖ ^ 2 ≤ 4 * (C : ℝ) ^ 2 * diskMapEnergyDensity g u z := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g hΦ hΦc
  let C : ℝ≥0 := B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ p (v : TangentSpace 𝓘(ℝ, E) p),
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ p v : F)‖ ≤ C * Real.sqrt (g.inner p v v) := by
    intro p v
    exact (hB p v).trans (mul_le_mul_of_nonneg_right (by simp [C]) (Real.sqrt_nonneg _))
  have hdist := edist_map_le_of_metric_mfderiv_bound g hC hΦ hbound
  refine ⟨C, hC, fun u K hu => ⟨?_, ?_⟩⟩
  · intro x y
    apply (hdist (u x) (u y)).trans
    calc
      (C : ℝ≥0∞) * riemannianEDistOf g (u x) (u y) ≤
          (C : ℝ≥0∞) * ((K : ℝ≥0∞) * edist x y) := by gcongr; exact hu x y
      _ = (↑(C * K) : ℝ≥0∞) * edist x y := by simp only [ENNReal.coe_mul, mul_assoc]
  · filter_upwards [ae_mdifferentiableAt_of_metric_lipschitz g hu] with z hz
    exact norm_fderiv_comp_sq_le_diskMapEnergyDensity g hΦ hbound hz

variable [CompleteSpace F]

theorem exists_integral_norm_fderiv_comp_diskExtension_sq_le_of_hasCompactSupport
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : closedDisk → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      LipschitzWith (C * K) (Φ ∘ diskExtension u) ∧
        IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2)
          (Metric.closedBall (0 : ℂ) 1) ∧
        (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) ≤
          4 * (C : ℝ) ^ 2 *
            ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le_of_hasCompactSupport g hΦ hΦc
  refine ⟨C, hC, fun u K hu => ?_⟩
  obtain ⟨hL, hpoint⟩ := hbound (diskExtension u) K (diskExtension_riemannian_lipschitz g hu)
  have he := integrable_diskMapEnergyDensity g hu
  have hpoint' := ae_restrict_of_ae (s := Metric.closedBall (0 : ℂ) 1) hpoint
  have hi : IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2)
      (Metric.closedBall (0 : ℂ) 1) := by
    apply Integrable.mono' (he.const_mul (4 * (C : ℝ) ^ 2))
      (((measurable_fderiv ℝ (Φ ∘ diskExtension u)).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [hpoint'] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hL, hi, ?_⟩
  simpa only [integral_const_mul] using
    integral_mono_ae hi (he.const_mul (4 * (C : ℝ) ^ 2)) hpoint'

end DifferentialGeometry.Geometry

end

end
