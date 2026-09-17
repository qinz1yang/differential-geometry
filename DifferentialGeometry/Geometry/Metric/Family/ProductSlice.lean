import DifferentialGeometry.Geometry.Metric.ProductSlice
import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Geometry.Metric.Product

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Filter Set
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [T2Space N]

omit [T2Space N] in
set_option backward.isDefEq.respectTransparency false in
theorem MetricFamilySmoothOn.sliceFst
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric (I.prod J) (M × N)}
    (hg : MetricFamilySmoothOn D g) (y : N) :
    MetricFamilySmoothOn D (fun t => (g t).sliceFst y) := by
  apply hg.of_pullback (fun t => (g t).sliceFst y) (fun x : M => (x, y))
    (contMDiff_id.prodMk contMDiff_const)
  intro t x v w
  rw [mfderiv_prod_left]
  exact SmoothRiemannianMetric.sliceFst_inner (g t) y x v w

set_option backward.isDefEq.respectTransparency false in
theorem MetricFamilySmoothOn.eq_sliceFst_prod_at_terminal_of_lt
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric (I.prod J) (M × N)}
    (hg : MetricFamilySmoothOn D g) {b : ℝ} (hcarrier : Iic b ⊆ D.carrier)
    (h : SmoothRiemannianMetric J N) (y : N)
    (hprod : ∀ t < b, g t = ((g t).sliceFst y).prod h) :
    g b = ((g b).sliceFst y).prod h := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.sliceFst_inner]
  have hA : ContinuousWithinAt (fun t : ℝ => (g t).inner z v w) (Iic b) b := by
    have hc := (hg.coeff_cont z v w).mono hcarrier
    exact hc.continuousWithinAt (by simp only [mem_Iic, le_refl])
  have hB : ContinuousWithinAt
      (fun t : ℝ => (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2)
      (Iic b) b := by
    have hc := (hg.coeff_cont (z.1, y) (v.1, 0) (w.1, 0)).mono hcarrier
    exact (hc.continuousWithinAt (by simp only [mem_Iic, le_refl])).add
      continuousWithinAt_const
  have heq : (fun t : ℝ => (g t).inner z v w) =ᶠ[𝓝[Iio b] b]
      (fun t : ℝ => (g t).inner (z.1, y) (v.1, 0) (w.1, 0) + h.inner z.2 v.2 w.2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := congrArg (fun q => q.inner z v w) (hprod t ht)
    simpa only [SmoothRiemannianMetric.prod_inner, SmoothRiemannianMetric.sliceFst_inner]
      using h
  exact tendsto_nhds_unique (hA.mono_left (nhdsWithin_mono b Iio_subset_Iic_self))
    ((hB.mono_left (nhdsWithin_mono b Iio_subset_Iic_self)).congr' heq.symm)

end DifferentialGeometry.Geometry.Curvature
