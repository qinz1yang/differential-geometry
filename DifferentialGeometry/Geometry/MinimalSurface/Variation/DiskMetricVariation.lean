import DifferentialGeometry.Geometry.Measure.Area.ConformalMetricDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import DifferentialGeometry.Geometry.Metric.ParameterDerivative



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




def diskMapMetricVariationDensity (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (t : ℝ) (U : ℂ → M) (z : ℂ) : ℝ :=
  (deriv (fun r => (G r).inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)) t +
    deriv (fun r => (G r).inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) t) / 2



theorem contDiffOn_metricFamilyDiskPairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {T : Set ℝ} (hT : IsOpen T) (hTD : T ⊆ D.regular)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (v w : ℂ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℂ =>
      (G q.1).inner (U q.2) (diskMapPartial U q.2 v) (diskMapPartial U q.2 w)) (T ×ˢ s) := by
  intro q hq
  have hUz := (hU q.2 hq.2).contMDiffAt (hs.mem_nhds hq.2)
  have hV (a : ℂ) := ((contMDiffOn_source_partial hs hU (m := ∞) (by simp) a) q.2 hq.2).contMDiffAt
    (hs.mem_nhds hq.2)
  have h := contMDiffAt_metricFamilySectionPairing hG contMDiffAt_fst
    (hUz.comp q contMDiffAt_snd) (Filter.mem_of_superset (hT.mem_nhds hq.1) hTD)
    ((hV v).comp q contMDiffAt_snd) ((hV w).comp q contMDiffAt_snd)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt.contDiffWithinAt




theorem hasDerivAt_diskMapAreaDensity_metric
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : ℂ → M} {z : ℂ} (hconf : DiskMapConformalAt (G t) U z) :
    HasDerivAt (fun r => riemannianAreaDensity (G r) U z) (diskMapMetricVariationDensity G t U z) t := by
  have hpair (v w : TangentSpace 𝓘(ℝ, E) (U z)) :=
    (((hG.coeff (U z) v w).contDiffAt ht).differentiableAt (by simp)).hasDerivAt
  exact hasDerivAt_tangentTwoJacobian_at_conformal (hpair _ _) (hpair _ _) (hpair _ _) hconf.1 hconf.2



theorem contDiffOn_diskMapMetricVariationDensity
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (diskMapMetricVariationDensity G t U) s := by
  intro z hz
  have hp (v w : ℂ) : ContDiffAt ℝ ∞
      (fun q : ℝ × ℂ => (G q.1).inner (U q.2) (diskMapPartial U q.2 v) (diskMapPartial U q.2 w)) (t, z) :=
    ((contDiffOn_metricFamilyDiskPairing hG D.regular_isOpen Subset.rfl hs hU v w)
      (t, z) ⟨mem_of_mem_nhds ht, hz⟩).contDiffAt
        ((D.regular_isOpen.prod hs).mem_nhds ⟨mem_of_mem_nhds ht, hz⟩)
  have hd (v w : ℂ) := (contDiffAt_deriv_fst (hp v w)).comp z
    (contDiffAt_const.prodMk contDiffAt_id)
  exact ((hd 1 1).add (hd Complex.I Complex.I)).div_const 2 |>.contDiffWithinAt

end DifferentialGeometry.Geometry
