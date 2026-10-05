import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryRayDomain
import DifferentialGeometry.Geometry.Comparison.Volume.RadialComparison
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.NoConjugatePoints
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

/-!
Actual ambient intrinsic rays have a uniform initial minimizing prefix. A longer minimizing
prefix excludes conjugate points at every alive time, supplying actual Jacobi comparison data.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientDimension : NeZero (Module.finrank ℝ E)]
  {H : Type*} [ambientModelTopology : TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [ambientModelBoundary : J.Boundaryless] {N : Type*}
  [ambientTopology : TopologicalSpace N] [ambientCharts : ChartedSpace H N]
  [ambientSmooth : IsManifold J ∞ N] [ambientT2 : T2Space N]
  [ambientSigma : SigmaCompactSpace N] [ambientTangentT2 : T2Space (TangentBundle J N)]
  [ambientBundle : RiemannianBundle (fun x : N => TangentSpace J x)]
  [ambientDistance : PseudoEMetricSpace N] [ambientComplete : CompleteSpace N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_boundary_ambient_alive_radius [ambientRiemannian : IsRiemannianManifold J N]
    [ambientMetricContinuous : IsContinuousRiemannianBundle E (fun x : N => TangentSpace J x)]
    (g : SmoothRiemannianMetric J N) (hEnorm : IsMetricNorm g) (p : N) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : TangentSpace J p, g.inner p u u = 1 →
      ∀ t ∈ Ioo (0 : ℝ) r,
        t ∈ boundaryRayDomain g p (intrinsicGeodesic g hEnorm p u) := by
  obtain ⟨r, hr, hdist⟩ := radial_riemannianEDist_eq_of_small g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro u hu t ht
  let T : ℝ := (t + r) / 2
  have htT : t < T := by dsimp only [T]; linarith only [ht.2]
  have hTr : T < r := by dsimp only [T]; linarith only [ht.2]
  refine ⟨ht.1, T, htT, ?_⟩
  intro s hs
  refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
  have hh := hdist hu hs.1.le (hs.2.trans_lt hTr)
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul] at hh
  exact hh

omit ambientTangentT2 in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundary_ambient_ray_no_conjugate [ambientRiemannian : IsRiemannianManifold J N]
    [ambientMetricContinuous : IsContinuousRiemannianBundle E (fun x : N => TangentSpace J x)]
    (g : SmoothRiemannianMetric J N) (hEnorm : IsMetricNorm g) (p : N)
    (u : TangentSpace J p) (hunit : g.inner p u u = 1) (t : ℝ)
    (ht : t ∈ boundaryRayDomain g p (intrinsicGeodesic g hEnorm p u)) :
    ¬ IsConjVec g hEnorm p ((t • u : TangentSpace J p) : E) := by
  obtain ⟨htpos, T, htT, hprefix⟩ := ht
  have hT : 0 < T := htpos.trans htT
  have hlength : riemannianEDist J p (intrinsicGeodesic g hEnorm p u T) =
      ENNReal.ofReal T := by
    rw [← riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact (hprefix T ⟨hT, le_rfl⟩).2
  have hsegment : (T • u : TangentSpace J p) ∈ SegmentDom g hEnorm p := by
    rw [mem_segmentDom, expMapIntrinsic_def, intrinsicGeodesic_smul, hlength,
      ENNReal.toReal_ofReal hT.le, gInner_smul_self, hunit, mul_one, Real.sqrt_sq_eq_abs,
      abs_of_pos hT]
  have hu : u ≠ 0 := by
    intro hz
    have hzero : g.inner p (0 : TangentSpace J p) (0 : TangentSpace J p) = 0 :=
      congrArg (fun B : TangentSpace J p →L[ℝ] ℝ => B 0) ((g.inner p).map_zero)
    rw [hz] at hunit
    exact zero_ne_one (hzero.symm.trans hunit)
  have hTu : (T • u : TangentSpace J p) ≠ 0 := smul_ne_zero hT.ne' hu
  have hno := segmentDom_no_conj g hEnorm hsegment hTu (t / T)
    ⟨div_pos htpos hT, (div_lt_one hT).mpr htT⟩
  simpa only [smul_smul, div_mul_cancel₀ t hT.ne'] using hno

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
