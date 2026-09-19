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

end

section

noncomputable section

open Set Bundle Manifold DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def diskMapMetricVariationWithinDensity (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (T : Set ℝ) (t : ℝ) (U : ℂ → M) (z : ℂ) : ℝ :=
  (derivWithin (fun r => (G r).inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)) T t +
    derivWithin (fun r => (G r).inner (U z) (diskMapPartial U z Complex.I)
      (diskMapPartial U z Complex.I)) T t) / 2

theorem contDiffOn_diskMapMetricVariationWithinDensity
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (Icc a b ×ˢ univ))
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (diskMapMetricVariationWithinDensity G (Icc a b) t₀ U) s := by
  have hd := contMDiffOn_derivWithin_fst (uniqueDiffOn_Icc hab) hG
  have hpair (v : ℂ) : ContDiffOn ℝ ∞
      (fun z => derivWithin (fun r => (G r).inner (U z) (diskMapPartial U z v)
        (diskMapPartial U z v)) (Icc a b) t₀) s := by
    have hm : ContMDiffOn 𝓘(ℝ, ℂ)
        (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) ∞
        (fun z : ℂ => (t₀, TotalSpace.mk' E (U z) (diskMapPartial U z v))) s :=
      contMDiffOn_const.prodMk (contMDiffOn_source_partial hs hU (m := ∞) (by simp) v)
    have h := hd.comp (f := fun z : ℂ => (t₀, TotalSpace.mk' E (U z) (diskMapPartial U z v)))
      hm (fun _ _ => ⟨ht₀, mem_univ _⟩)
    exact h.contDiffOn
  exact ((hpair 1).add (hpair Complex.I)).div_const 2


private theorem differentiableWithinAt_metric_inner_of_quadratic
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {T : Set ℝ} {t₀ : ℝ}
    {x : M} (hdiag : ∀ v : TangentSpace 𝓘(ℝ, E) x,
      DifferentiableWithinAt ℝ (fun t => (G t).inner x v v) T t₀)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    DifferentiableWithinAt ℝ (fun t => (G t).inner x v w) T t₀ := by
  have hpolar : (fun t => (G t).inner x v w) =
      (fun t => (1 / 4 : ℝ) *
        ((G t).inner x (v + w) (v + w) - (G t).inner x (v - w) (v - w))) := by
    funext t
    simp only [map_add, map_sub, add_apply, sub_apply,
      (G t).symm x w v]
    ring
  rw [hpolar]
  exact (hdiag (v + w)).sub (hdiag (v - w)) |>.const_mul (1 / 4 : ℝ)


theorem hasDerivWithinAt_diskMapAreaDensity_metric_on_Icc
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (Icc a b ×ˢ univ))
    {U : ℂ → M} {z : ℂ} (hconf : DiskMapConformalAt (G t₀) U z) :
    HasDerivWithinAt (fun r => riemannianAreaDensity (G r) U z)
      (diskMapMetricVariationWithinDensity G (Icc a b) t₀ U z) (Icc a b) t₀ := by
  have hdiag (v : TangentSpace 𝓘(ℝ, E) (U z)) :
      DifferentiableWithinAt ℝ (fun t => (G t).inner (U z) v v) (Icc a b) t₀ := by
    have hc := (hG (t₀, TotalSpace.mk' E (U z) v) ⟨ht₀, mem_univ _⟩).comp
      (f := fun r : ℝ => (r, TotalSpace.mk' E (U z) v)) t₀
      (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
      (fun r hr => ⟨hr, mem_univ _⟩)
    exact hc.contDiffWithinAt.differentiableWithinAt (by simp)
  have hpair (v w : TangentSpace 𝓘(ℝ, E) (U z)) :=
    (differentiableWithinAt_metric_inner_of_quadratic hdiag v w).hasDerivWithinAt
  exact hasDerivWithinAt_tangentTwoJacobian_at_conformal (uniqueDiffOn_Icc hab t₀ ht₀)
    (hpair _ _) (hpair _ _) (hpair _ _) hconf.1 hconf.2


end DifferentialGeometry.Geometry

end

end
