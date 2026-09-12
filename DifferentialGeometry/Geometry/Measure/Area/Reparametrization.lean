import DifferentialGeometry.Analysis.Integration.Measure.LipschitzChangeOfVariables
import DifferentialGeometry.Geometry.Measure.Area.ChangeOfFrame
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher










noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

open scoped ComplexConjugate


def diskReflection : closedDisk ≃ₜ closedDisk where
  toFun z := ⟨conj (z : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using z.property⟩
  invFun z := ⟨conj (z : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using z.property⟩
  left_inv z := Subtype.ext (by simp)
  right_inv z := Subtype.ext (by simp)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_conj.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_conj.comp continuous_subtype_val

theorem diskReflection_lipschitz : LipschitzWith 1 diskReflection := by
  intro x y
  change edist (conj (x : ℂ)) (conj (y : ℂ)) ≤ (1 : ℝ≥0∞) * edist (x : ℂ) (y : ℂ)
  rw [Complex.isometry_conj.edist_eq, one_mul]

@[simp] theorem diskReflection_symm : diskReflection.symm = diskReflection := rfl

private theorem diskReflection_coe (z : closedDisk) :
    ((diskReflection z : closedDisk) : ℂ) = starRingEnd ℂ (z : ℂ) := rfl

private theorem diskBoundary_coe_circle (θ : loopCircle) :
    ((diskBoundary θ : closedDisk) : ℂ) = ((AddCircle.toCircle θ : Circle) : ℂ) := rfl

theorem diskReflection_diskBoundary (θ : loopCircle) :
    diskReflection (diskBoundary θ) = diskBoundary (-θ) := by
  refine Subtype.ext ?_
  rw [diskReflection_coe, diskBoundary_coe_circle, diskBoundary_coe_circle,
    AddCircle.toCircle_neg, Circle.coe_inv]
  exact (Complex.inv_eq_conj (Circle.norm_coe (AddCircle.toCircle θ))).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]



theorem riemannianArea_precomp (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {φ ψ : ℂ → ℂ} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hφ : LipschitzWith K φ) (hψ : LipschitzWith L ψ) {s : Set ℂ}
    (hs : MeasurableSet s) (hi : ∀ z ∈ s, ψ (φ z) = z) :
    riemannianArea g (u ∘ φ) s = riemannianArea g u (φ '' s) := by
  have hinj : InjOn φ s := fun x hx y hy he => by
    simpa only [hi x hx, hi y hy] using congrArg ψ he
  rw [riemannianArea, riemannianArea,
    integral_image_eq_integral_abs_det_of_lipschitz hφ hs hinj]
  apply integral_congr_ae
  have ha := ae_comp_of_lipschitz_leftInverse_on hψ hi
    (ae_mdifferentiableAt_of_riemannian_lipschitz g hu)
  filter_upwards [ae_restrict_of_ae ha,
    ae_restrict_of_ae (hφ.ae_differentiableAt (μ := volume)),
    ae_restrict_mem hs] with z hz hzd hzs
  exact riemannianAreaDensity_precomp g (hz hzs) hzd



theorem riemannianDiskArea_reparametrize (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : closedDisk → M} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (φ : closedDisk ≃ₜ closedDisk) (hφ : LipschitzWith K φ)
    (hψ : LipschitzWith L φ.symm) :
    riemannianDiskArea g (u ∘ φ) = riemannianDiskArea g u := by
  let Φ : ℂ → ℂ := diskExtension (fun z => (φ z : ℂ))
  let Ψ : ℂ → ℂ := diskExtension (fun z => (φ.symm z : ℂ))
  have hΦ : LipschitzWith K Φ := diskExtension_lipschitz (by
    intro x y
    exact hφ x y)
  have hΨ : LipschitzWith L Ψ := diskExtension_lipschitz (by
    intro x y
    exact hψ x y)
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
  rw [riemannianDiskArea_eq_of_extension g (u ∘ φ) (diskExtension u ∘ Φ)
    (fun z => by simp only [Function.comp_apply, hΦcoe, diskExtension_coe])]
  rw [riemannianArea_precomp g (diskExtension_riemannian_lipschitz g hu)
    hΦ hΨ measurableSet_closedBall hi, himage]
  rfl

theorem riemannianDiskArea_diskReflection (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y) :
    riemannianDiskArea g (u ∘ diskReflection) = riemannianDiskArea g u :=
  riemannianDiskArea_reparametrize g hu diskReflection diskReflection_lipschitz
    (by simpa using diskReflection_lipschitz)

omit [FiniteDimensional ℝ E] [T3Space M] [CompactSpace M] in
theorem riemannianArea_comp_conj_of_contMDiffOn (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {N : Set ℂ} (hN : IsOpen N) (hDN : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U N) :
    riemannianArea g (U ∘ conj) (Metric.closedBall (0 : ℂ) 1) =
      riemannianArea g U (Metric.closedBall (0 : ℂ) 1) := by
  have hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (conj z) :=
    fun z hz => (hU.contMDiffAt (hN.mem_nhds (hDN (by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz)))).mdifferentiableAt
      (by simp)
  have hL : LipschitzWith (1 : ℝ≥0) (conj : ℂ → ℂ) := by
    intro x y
    rw [Complex.isometry_conj.edist_eq]
    simp
  have himage : (conj : ℂ → ℂ) '' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
    · intro z hz
      exact ⟨conj z, by
        simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz, by simp⟩
  have hinj : Set.InjOn (conj : ℂ → ℂ) (Metric.closedBall (0 : ℂ) 1) :=
    fun x _ y _ hxy => by simpa using congrArg (conj : ℂ → ℂ) hxy
  have hstep : riemannianArea g (U ∘ conj) (Metric.closedBall (0 : ℂ) 1) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        |(fderiv ℝ (conj : ℂ → ℂ) z).toLinearMap.det| • riemannianAreaDensity g U (conj z) := by
    rw [riemannianArea]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    rw [riemannianAreaDensity_precomp g (hdiff z hz) (by
      exact Complex.differentiable_conj.differentiableAt)]
    rfl
  rw [hstep, ← integral_image_eq_integral_abs_det_of_lipschitz hL measurableSet_closedBall hinj
    (riemannianAreaDensity g U), himage, ← riemannianArea]

end DifferentialGeometry.Geometry
