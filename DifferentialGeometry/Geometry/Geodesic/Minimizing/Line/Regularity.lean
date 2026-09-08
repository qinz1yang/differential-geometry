import DifferentialGeometry.Geometry.Geodesic.Minimizing.Line.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Geodesic.Chart.Regularity

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.riemannianEDist_eq_ofReal_abs_sub
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) (s t : ℝ) :
    riemannianEDist I (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  rcases le_total s t with hst | hts
  · rw [show |s - t| = t - s by
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]; ring]
    exact hγ.edist_eq hst
  · rw [riemannianEDist_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
    exact hγ.edist_eq hts

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.isometry
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) : Isometry γ := by
  intro s t
  rw [IsRiemannianManifold.out (I := I) (γ s) (γ t), edist_dist, Real.dist_eq]
  exact hγ.riemannianEDist_eq_ofReal_abs_sub s t

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.continuous
    [T2Space M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) : Continuous γ := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let _ : RegularSpace M := inferInstance
  rw [continuous_iff_continuousAt]
  intro t
  have hd : Filter.Tendsto (fun u => riemannianEDist I (γ t) (γ u)) (nhds t) (nhds 0) := by
    simp only [hγ.riemannianEDist_eq_ofReal_abs_sub]
    have hc : Continuous (fun u : ℝ => ENNReal.ofReal |t - u|) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.sub continuous_id).abs)
    simpa only [sub_self, abs_zero, ENNReal.ofReal_zero] using
      hc.tendsto t
  rw [ContinuousAt, tendsto_nhds]
  intro s hs ht
  obtain ⟨c, hc, hsub⟩ := setOfPred_riemannianEDist_lt_subset_nhds' I (hs.mem_nhds ht)
  exact Filter.mem_of_superset (hd (Iio_mem_nhds hc)) (fun _ hu => hsub hu)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.contMDiff
    [I.Boundaryless] [T2Space M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
  apply contMDiffOn_univ.mp
  exact Geodesic.isGeodesicOn_contMDiffOn_infty g isOpen_univ
    (hγ.isGeodesic.isGeodesicOn Set.univ) hγ.continuous.continuousOn

end DifferentialGeometry.Geometry.Riemannian
