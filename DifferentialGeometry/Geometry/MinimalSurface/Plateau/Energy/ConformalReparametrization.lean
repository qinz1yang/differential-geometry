import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher
import DifferentialGeometry.Analysis.Integration.Measure.LipschitzChangeOfVariables
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskReflectionDifferential
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialStationarity

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskMapPartial_comp_of_hasDerivAt {U : ℂ → M} {φ : ℂ → ℂ} {a z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (φ z)) (hφ : HasDerivAt φ a z) (v : ℂ) :
    diskMapPartial (E := E) (U ∘ φ) z v = diskMapPartial (E := E) U (φ z) (a * v) := by
  unfold diskMapPartial
  rw [mfderiv_comp z hU hφ.complexToReal_fderiv.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hφ.complexToReal_fderiv.fderiv]
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem quadratic_sum_complex_mul (B : E →L[ℝ] E →L[ℝ] ℝ) (L : ℂ →L[ℝ] E) (a : ℂ) :
    B (L a) (L a) + B (L (a * Complex.I)) (L (a * Complex.I)) =
      ‖a‖ ^ 2 * (B (L 1) (L 1) + B (L Complex.I) (L Complex.I)) := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im a).symm
  have haI : a * Complex.I = -a.im • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hnorm : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hL := congrArg L ha
  have hLI := congrArg L haI
  simp only [map_add, map_smul] at hL hLI
  rw [hL, hLI, hnorm]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

theorem diskMapEnergyDensity_comp_of_hasDerivAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {φ : ℂ → ℂ} {a z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (φ z)) (hφ : HasDerivAt φ a z) :
    diskMapEnergyDensity g (U ∘ φ) z = ‖a‖ ^ 2 * diskMapEnergyDensity g U (φ z) := by
  unfold diskMapEnergyDensity
  simp only [Function.comp_apply, diskMapPartial_comp_of_hasDerivAt hU hφ, mul_one]
  have h := quadratic_sum_complex_mul (g.inner (U (φ z)) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (φ z) : ℂ →L[ℝ] E) a
  simpa only [diskMapPartial, mul_div_assoc] using! congrArg (fun t : ℝ => t / 2) h

theorem diskMapEnergyDensity_comp_of_differentiableAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {φ : ℂ → ℂ} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (φ z)) (hφ : DifferentiableAt ℂ φ z) :
    diskMapEnergyDensity g (U ∘ φ) z =
      ‖deriv φ z‖ ^ 2 * diskMapEnergyDensity g U (φ z) :=
  diskMapEnergyDensity_comp_of_hasDerivAt g hU hφ.hasDerivAt

private theorem abs_det_complex_deriv (a : ℂ) :
    |(a • (1 : ℂ →L[ℝ] ℂ)).toLinearMap.det| = ‖a‖ ^ 2 := by
  have heq : (a • (1 : ℂ →L[ℝ] ℂ)).toLinearMap =
      ((a • (1 : ℂ →L[ℂ] ℂ)).toLinearMap).restrictScalars ℝ := by
    ext z
    rfl
  rw [heq, LinearMap.det_restrictScalars]
  have hd : ((a • (1 : ℂ →L[ℂ] ℂ)).toLinearMap).det = a := by
    change (a • (1 : ℂ →ₗ[ℂ] ℂ)).det = a
    simp
  rw [hd, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

theorem integral_diskMapEnergyDensity_comp_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {φ ψ : ℂ → ℂ} {s : Set ℂ}
    {K L : ℝ≥0} (hφ : LipschitzWith K φ) (hψ : LipschitzWith L ψ)
    (hs : MeasurableSet s) (hi : ∀ z ∈ s, ψ (φ z) = z)
    (hφhol : ∀ᵐ z ∂volume.restrict s, DifferentiableAt ℂ φ z)
    (hU : ∀ᵐ w ∂volume, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U w) :
    ∫ z in s, diskMapEnergyDensity g (U ∘ φ) z =
      ∫ w in φ '' s, diskMapEnergyDensity g U w := by
  have hinj : InjOn φ s := fun x hx y hy he => by
    simpa only [hi x hx, hi y hy] using congrArg ψ he
  rw [DifferentialGeometry.Analysis.integral_image_eq_integral_abs_det_of_lipschitz hφ hs hinj]
  have hUa := DifferentialGeometry.Analysis.ae_comp_of_lipschitz_leftInverse_on hψ hi hU
  apply integral_congr_ae
  filter_upwards [hφhol, ae_restrict_of_ae hUa, ae_restrict_mem hs] with z hz hUz hzs
  rw [diskMapEnergyDensity_comp_of_differentiableAt g (hUz hzs) hz,
    hz.hasDerivAt.complexToReal_fderiv.fderiv, abs_det_complex_deriv, smul_eq_mul]

variable [FiniteDimensional ℝ E] [T2Space M]

theorem integral_diskMapEnergyDensity_reparametrize
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (φ : closedDisk ≃ₜ closedDisk) (hφ : LipschitzWith K φ)
    (hψ : LipschitzWith L φ.symm)
    (hhol : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (diskExtension (fun w => (φ w : ℂ))) z) :
    ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension (u ∘ φ)) z =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : T3Space M := inferInstance
  let Φ : ℂ → ℂ := diskExtension (fun z => (φ z : ℂ))
  let Ψ : ℂ → ℂ := diskExtension (fun z => (φ.symm z : ℂ))
  have hΦ : LipschitzWith K Φ := diskExtension_lipschitz (fun x y => hφ x y)
  have hΨ : LipschitzWith L Ψ := diskExtension_lipschitz (fun x y => hψ x y)
  have hΦcoe (z : closedDisk) : Φ z = φ z := diskExtension_coe _ z
  have hΨcoe (z : closedDisk) : Ψ z = φ.symm z := diskExtension_coe _ z
  have hi (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) : Ψ (Φ z) = z := by
    rw [hΦcoe ⟨z, hz⟩, hΨcoe (φ ⟨z, hz⟩), φ.symm_apply_apply]
  have himage : Φ '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hΦcoe ⟨z, hz⟩]
      exact (φ ⟨z, hz⟩).property
    · intro z hz
      refine ⟨φ.symm ⟨z, hz⟩, (φ.symm ⟨z, hz⟩).property, ?_⟩
      rw [hΦcoe, φ.apply_symm_apply]
  have hext : diskExtension (u ∘ φ) = diskExtension u ∘ Φ := by
    funext z
    change u (φ (diskRetraction z)) = diskExtension u (φ (diskRetraction z))
    exact (diskExtension_coe u (φ (diskRetraction z))).symm
  have hΦhol : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
      DifferentiableAt ℂ Φ z := by
    filter_upwards [ae_disk_interior] with z hz
    exact hhol z hz
  rw [hext, integral_diskMapEnergyDensity_comp_of_lipschitz g hΦ hΨ
    measurableSet_closedBall hi hΦhol
    (ae_mdifferentiableAt_of_riemannian_lipschitz g (diskExtension_riemannian_lipschitz g hu)),
    himage]

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapEnergyDensity_comp_conj
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) :
    diskMapEnergyDensity g (U ∘ conj) z = diskMapEnergyDensity g U (conj z) := by
  unfold diskMapEnergyDensity
  simp only [Function.comp_apply, diskMapPartial_comp_conj_one,
    diskMapPartial_comp_conj_I, map_neg, _root_.neg_apply, neg_neg]

theorem integral_diskMapEnergyDensity_comp_conj_preimage
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (s : Set ℂ) :
    (∫ z in (conj : ℂ → ℂ) ⁻¹' s, diskMapEnergyDensity g (U ∘ conj) z) =
      ∫ z in s, diskMapEnergyDensity g U z := by
  simp_rw [diskMapEnergyDensity_comp_conj]
  exact Complex.conjLIE.measurePreserving.setIntegral_preimage_emb
    Complex.conjLIE.toMeasurableEquiv.measurableEmbedding (diskMapEnergyDensity g U) s

theorem integral_diskMapEnergyDensity_comp_conj
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (U ∘ conj) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g U z := by
  have hs : (conj : ℂ → ℂ) ⁻¹' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, Complex.norm_conj]
  simpa only [hs] using integral_diskMapEnergyDensity_comp_conj_preimage g U
    (Metric.closedBall (0 : ℂ) 1)

theorem integral_diskMapEnergyDensity_diskReflection
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u ∘ diskReflection)) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  rw [← integral_diskMapEnergyDensity_comp_conj g (diskExtension u)]
  apply integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  have hext : diskExtension (u ∘ diskReflection) =ᶠ[𝓝 z] diskExtension u ∘ conj := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    have hwc : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
    have hcw : conj w ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hwc
    rw [diskExtension_coe _ ⟨w, hwc⟩]
    change u (diskReflection ⟨w, hwc⟩) = diskExtension u (conj w)
    rw [diskExtension_coe _ ⟨conj w, hcw⟩]
    rfl
  unfold diskMapEnergyDensity diskMapPartial
  rw [hext.eq_of_nhds, hext.mfderiv_eq]
  rw [hext.eq_of_nhds]
  rfl

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem mem_weaklyMonotoneDiskCompetitors_comp_diskReflection
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ) :
    u.comp ⟨diskReflection, diskReflection.continuous⟩ ∈ weaklyMonotoneDiskCompetitors g γ ∧
      diskTrace (u.comp ⟨diskReflection, diskReflection.continuous⟩) =
        (diskTrace u).comp ⟨fun θ => -θ, continuous_neg⟩ ∧
      riemannianDiskEnergy g (u.comp ⟨diskReflection, diskReflection.continuous⟩) =
        riemannianDiskEnergy g u := by
  have hδ : IsWeaklyMonotoneOnce (⟨fun θ : loopCircle => -θ, continuous_neg⟩ :
      C(loopCircle, loopCircle)) := by
    refine ⟨fun t : ℝ => -t, continuous_neg, fun _ => rfl, Or.inr ⟨?_, ?_⟩⟩
    · intro x y hxy
      exact neg_le_neg hxy
    · intro t
      ring
  have hmem := mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization g hu
    ⟨diskReflection, diskReflection.continuous⟩ diskReflection_lipschitz
    ⟨fun θ => -θ, continuous_neg⟩ hδ diskReflection_diskBoundary
  exact ⟨hmem.1, hmem.2, integral_diskMapEnergyDensity_diskReflection g⟩

variable [FiniteDimensional ℝ E] [T2Space M]

theorem mem_weaklyMonotoneDiskCompetitors_comp_holomorphic
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    (φ : closedDisk ≃ₜ closedDisk) {K L : ℝ≥0} (hφ : LipschitzWith K φ)
    (hψ : LipschitzWith L φ.symm)
    (hhol : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (diskExtension (fun w => (φ w : ℂ))) z)
    (δ : C(loopCircle, loopCircle)) (hδ : IsWeaklyMonotoneOnce δ)
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) :
    u.comp ⟨φ, φ.continuous⟩ ∈ weaklyMonotoneDiskCompetitors g γ ∧
      diskTrace (u.comp ⟨φ, φ.continuous⟩) = (diskTrace u).comp δ ∧
      riemannianDiskEnergy g (u.comp ⟨φ, φ.continuous⟩) = riemannianDiskEnergy g u := by
  have hmem := mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization g hu
    ⟨φ, φ.continuous⟩ hφ δ hδ hboundary
  obtain ⟨C, hC⟩ := hu.2
  exact ⟨hmem.1, hmem.2, integral_diskMapEnergyDensity_reparametrize g hC φ hφ hψ hhol⟩

theorem integral_diskMapEnergyDensity_reparametrize_antiholomorphic
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (φ : closedDisk ≃ₜ closedDisk) (hφ : LipschitzWith K φ)
    (hψ : LipschitzWith L φ.symm)
    (hanti : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (fun z => conj (diskExtension (fun w => (φ w : ℂ)) z)) z) :
    ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension (u ∘ φ)) z =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  let χ := φ.trans diskReflection
  have hχ : LipschitzWith K χ := by
    intro x y
    exact (diskReflection_lipschitz (φ x) (φ y)).trans (by
      simpa only [ENNReal.coe_one, one_mul] using hφ x y)
  have hχi : LipschitzWith L χ.symm := by
    intro x y
    exact (hψ (diskReflection x) (diskReflection y)).trans (by
      gcongr
      simpa only [ENNReal.coe_one, one_mul] using diskReflection_lipschitz x y)
  have hhol : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (diskExtension (fun w => (χ w : ℂ))) z := by
    intro z hz
    exact hanti z hz
  have href : ∀ x y, riemannianEDistOf g ((u ∘ diskReflection) x) ((u ∘ diskReflection) y) ≤
      (C : ℝ≥0∞) * edist x y := by
    intro x y
    apply (hu (diskReflection x) (diskReflection y)).trans
    gcongr
    simpa only [ENNReal.coe_one, one_mul] using diskReflection_lipschitz x y
  have hmain := integral_diskMapEnergyDensity_reparametrize g href χ hχ hχi hhol
  have heq : (u ∘ diskReflection) ∘ χ = u ∘ φ := by
    funext z
    change u (diskReflection (diskReflection (φ z))) = u (φ z)
    exact congrArg u (diskReflection.symm_apply_apply (φ z))
  rw [heq, integral_diskMapEnergyDensity_diskReflection] at hmain
  exact hmain

theorem mem_weaklyMonotoneDiskCompetitors_comp_antiholomorphic
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    (φ : closedDisk ≃ₜ closedDisk) {K L : ℝ≥0} (hφ : LipschitzWith K φ)
    (hψ : LipschitzWith L φ.symm)
    (hanti : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℂ (fun z => conj (diskExtension (fun w => (φ w : ℂ)) z)) z)
    (δ : C(loopCircle, loopCircle)) (hδ : IsWeaklyMonotoneOnce δ)
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) :
    u.comp ⟨φ, φ.continuous⟩ ∈ weaklyMonotoneDiskCompetitors g γ ∧
      diskTrace (u.comp ⟨φ, φ.continuous⟩) = (diskTrace u).comp δ ∧
      riemannianDiskEnergy g (u.comp ⟨φ, φ.continuous⟩) = riemannianDiskEnergy g u := by
  have hmem := mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization g hu
    ⟨φ, φ.continuous⟩ hφ δ hδ hboundary
  obtain ⟨C, hC⟩ := hu.2
  exact ⟨hmem.1, hmem.2, integral_diskMapEnergyDensity_reparametrize_antiholomorphic
    g hC φ hφ hψ hanti⟩

end DifferentialGeometry.Geometry

end
