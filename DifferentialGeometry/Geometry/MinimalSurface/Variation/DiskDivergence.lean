import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskConormal
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.LocalGreenIdentity



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Analysis
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapSectionDivergence (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)) (z : ℂ) : ℝ :=
  g.inner (U z) (sourceSectionCovariantDerivative g U W z 1) (diskMapPartial U z 1) +
    g.inner (U z) (sourceSectionCovariantDerivative g U W z Complex.I) (diskMapPartial U z Complex.I)




theorem complexDivergence_diskMapSectionPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s)
    {z : ℂ} (hz : z ∈ s) :
    complexDivergence (fun q => g.inner (U q) (W q) (diskMapPartial U q 1))
      (fun q => g.inner (U q) (W q) (diskMapPartial U q Complex.I)) z =
      diskMapSectionDivergence g U W z + g.inner (U z) (W z) (diskMapTension g U z) := by
  unfold complexDivergence
  erw [fderiv_sourceSectionPairing g hs hU hW (contMDiffOn_source_partial hs hU (by simp) 1) hz,
    fderiv_sourceSectionPairing g hs hU hW (contMDiffOn_source_partial hs hU (by simp) Complex.I) hz]
  unfold diskMapSectionDivergence diskMapTension
  rw [map_add]
  simp only [diskMapCovariantPartial, sourceSectionCovariantDerivative, diskMapPartial]
  exact add_add_add_comm _ _ _ _



theorem diskMapSectionDivergence_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)) {z : ℂ}
    (hconf : DiskMapConformalAt g U z) (ha : diskMapConformalCoefficient g U z = 0) :
    diskMapSectionDivergence g U W z = 0 := by
  have hd := hconf.coefficient_eq_zero_iff.mp ha
  unfold diskMapSectionDivergence diskMapPartial
  rw [hd]
  change g.inner (U z) _ (0 : TangentSpace 𝓘(ℝ, E) (U z)) + g.inner (U z) _ 0 = 0
  rw [map_zero, map_zero, add_zero]



theorem integrableOn_diskMapSectionDivergence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension g U z = 0)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s) :
    IntegrableOn (diskMapSectionDivergence g U W) (Metric.closedBall 0 1) := by
  have hF := contDiffOn_sourceSectionPairing g hU hW (contMDiffOn_source_partial hs hU (by simp) 1)
  have hG := contDiffOn_sourceSectionPairing g hU hW (contMDiffOn_source_partial hs hU (by simp) Complex.I)
  apply (((contDiffOn_complexDivergence hs hF hG).continuousOn.mono hDs).integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).congr
  filter_upwards [ae_disk_interior] with z hz
  erw [complexDivergence_diskMapSectionPairing g hs hU hW
    (hDs (Metric.ball_subset_closedBall hz)), hharm z hz, map_zero, add_zero]




theorem integral_diskMapSectionDivergence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ z ∈ Metric.closedBall 0 1, DiskMapConformalAt g U z)
    (hharm : ∀ z ∈ Metric.ball 0 1, diskMapTension g U z = 0)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapSectionDivergence g U W z) =
      -(∫ θ in -Real.pi..Real.pi,
        g.inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
          (diskMapInwardConormal g U (circleMap 0 1 θ)) *
            Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ))) := by
  let F : ℂ → ℝ := fun q => g.inner (U q) (W q) (diskMapPartial U q 1)
  let G : ℂ → ℝ := fun q => g.inner (U q) (W q) (diskMapPartial U q Complex.I)
  have hF := contDiffOn_sourceSectionPairing g hU hW (contMDiffOn_source_partial hs hU (by simp) 1)
  have hG := contDiffOn_sourceSectionPairing g hU hW (contMDiffOn_source_partial hs hU (by simp) Complex.I)
  have hgreen := integral_complexDivergence_closedBall_of_open hs hF hG (by norm_num : (0 : ℝ) < 1) hDs
  have hdiv : diskMapSectionDivergence g U W =ᵐ[volume.restrict (Metric.closedBall 0 1)]
      complexDivergence F G := by
    filter_upwards [ae_disk_interior] with z hz
    rw [complexDivergence_diskMapSectionPairing g hs hU hW
      (hDs (Metric.ball_subset_closedBall hz)), hharm z hz, map_zero, add_zero]
  rw [integral_congr_ae hdiv]
  erw [hgreen]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  have hz : circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
  have hcircle : Complex.polarCoord.symm (1, θ) = circleMap 0 1 θ := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  have hv : circleMap 0 1 θ = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    simp [circleMap, Complex.exp_mul_I, Complex.real_smul]
  dsimp only
  rw [hcircle, (hconf _ hz).inwardConormal_flux, neg_neg]
  change 1 * (g.inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapPartial U (circleMap 0 1 θ) 1) * Real.cos θ +
    g.inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapPartial U (circleMap 0 1 θ) Complex.I) * Real.sin θ) =
    g.inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapPartial U (circleMap 0 1 θ) (circleMap 0 1 θ))
  have hpartial : diskMapPartial (E := E) U (circleMap 0 1 θ) (circleMap 0 1 θ) =
      Real.cos θ • diskMapPartial U (circleMap 0 1 θ) 1 +
      Real.sin θ • diskMapPartial U (circleMap 0 1 θ) Complex.I := by
    calc
      _ = diskMapPartial U (circleMap 0 1 θ) (Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I) :=
        congrArg (diskMapPartial (E := E) U (circleMap 0 1 θ)) hv
      _ = _ := by
        unfold diskMapPartial
        erw [map_add, map_smul, map_smul]
  rw [hpartial]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
theorem continuous_diskMapSectionInwardFlux
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.sphere 0 1 ⊆ s)
    (hconf : ∀ z ∈ Metric.sphere 0 1, DiskMapConformalAt g U z)
    {W : ∀ z, TangentSpace 𝓘(ℝ, E) (U z)}
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (W z)) s) :
    Continuous (fun θ : ℝ => g.inner (U (circleMap 0 1 θ)) (W (circleMap 0 1 θ))
      (diskMapInwardConormal g U (circleMap 0 1 θ)) *
        Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ))) := by
  have hR : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (diskMapPartial U z z)) s :=
    (contMDiffOn_source_tangentMap hs hU (m := ∞) (by simp)).comp
      (contMDiff_id.prodMk contMDiff_id).contMDiffOn (fun z hz => ⟨hz, mem_univ z⟩)
  have hcircle (θ : ℝ) : circleMap 0 1 θ ∈ Metric.sphere (0 : ℂ) 1 := by
    simp
  have hp := (contDiffOn_sourceSectionPairing g hU hW hR).continuousOn
  have hc := (hp.comp_continuous (continuous_circleMap 0 1) (fun θ => hDs (hcircle θ))).neg
  apply hc.congr
  intro θ
  exact ((hconf _ (hcircle θ)).inwardConormal_flux _).symm

end DifferentialGeometry.Geometry
