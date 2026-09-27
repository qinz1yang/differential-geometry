import DifferentialGeometry.Geometry.Curvature.DiskTraceCurvature



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




def diskMapTraceBoundaryDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (γ : ℝ → M) (φ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  let z := circleMap 0 1 θ
  g.inner (U z) (riemannianCurveCurvature g γ (φ θ) : E) (diskMapInwardConormal g U z) *
    Real.sqrt (diskMapConformalCoefficient g U z)



theorem diskMapTraceBoundaryDensity_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (γ : ℝ → M) (φ : ℝ → ℝ)
    {θ : ℝ} (hz : diskMapConformalCoefficient g U (circleMap 0 1 θ) = 0) :
    diskMapTraceBoundaryDensity g U γ φ θ = 0 := by
  simp [diskMapTraceBoundaryDensity, hz]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contDiff_diskMapTraceBoundaryDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (htrace : U ∘ circleMap 0 1 = γ ∘ φ) :
    ContDiff ℝ ∞ (diskMapTraceBoundaryDensity g U γ φ) := by
  let c := circleMap 0 1
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ c := (contDiff_circleMap 0 1).contMDiff
  have hz (θ : ℝ) : c θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [c, Metric.mem_closedBall, dist_zero_right]
  have hbase := contMDiff_diskMapBoundary hs hU hDs
  have hH : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun θ => TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) (U (c θ))
        (riemannianCurveCurvature g γ (φ θ) : E)) := by
    convert (contMDiff_riemannianCurveCurvature g hγ hi).comp hφ.contMDiff using 1
    funext θ
    congr 1
    exact congrFun htrace θ
  have hR : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun θ => TotalSpace.mk' E (U (c θ)) (diskMapPartial (E := E) U (c θ) (c θ))) := by
    apply contMDiffOn_univ.mp
    exact (contMDiffOn_source_tangentMap hs hU (by simp)).comp
      (hc.prodMk hc).contMDiffOn (fun θ _ => ⟨hDs (hz θ), mem_univ _⟩)
  have hpair : ContDiff ℝ ∞ (fun θ => g.inner (U (c θ))
      (riemannianCurveCurvature g γ (φ θ) : E) (diskMapPartial U (c θ) (c θ))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
        (fun r => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U (c r))
          (g.inner (U (c r)) (riemannianCurveCurvature g γ (φ r) : E)
            (diskMapPartial U (c r) (c r)))) θ := by
      apply ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
      · exact g.contMDiff.contMDiffAt.comp θ hbase.contMDiffAt
      · exact hH.contMDiffAt
      · exact hR.contMDiffAt
    exact (contMDiffAt_totalSpace.mp hp).2.contDiffAt
  convert hpair.neg using 1
  funext θ
  exact (hconf _ (hz θ)).inwardConormal_flux _



theorem intervalIntegrable_diskMapTraceBoundaryDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (htrace : U ∘ circleMap 0 1 = γ ∘ φ) (a b : ℝ) :
    IntervalIntegrable (diskMapTraceBoundaryDensity g U γ φ) volume a b :=
  (contDiff_diskMapTraceBoundaryDensity g hs hU hDs hconf hγ hi hφ htrace).continuous.intervalIntegrable a b

end DifferentialGeometry.Geometry
