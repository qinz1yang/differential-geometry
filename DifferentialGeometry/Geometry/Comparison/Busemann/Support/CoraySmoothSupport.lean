import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedCoray
import DifferentialGeometry.Geometry.Comparison.Distance.SegmentSmoothness

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_open_smooth_dist_from_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)))
    (s : ℝ) (hs : 0 < s) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) U := by
  apply exists_open_smooth_dist_of_minimizing_intrinsic_segment g hEnorm p u hu s hs
  have h := hiso.dist_eq 0 ⟨2 * s, by positivity⟩
  change dist (intrinsicGeodesic g hEnorm p u 0)
    (intrinsicGeodesic g hEnorm p u (2 * s)) = |(0 : ℝ) - 2 * s| at h
  simpa only [intrinsicGeodesic_zero, zero_sub, abs_neg, abs_of_pos (by positivity : 0 < 2 * s)]
    using h

theorem contMDiffAt_dist_from_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)))
    (s : ℝ) (hs : 0 < s) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) p := by
  obtain ⟨U, hU, hp, hf⟩ := exists_open_smooth_dist_from_intrinsic_ray
    (I := I) g hEnorm p u hu hiso s hs
  exact (hf p hp).contMDiffAt (hU.mem_nhds hp)

theorem exists_smooth_intrinsic_coray_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun s : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (s : ℝ)) ∧
      (∀ s : ℝ, 0 ≤ s → busemann c (intrinsicGeodesic (I := I) g hEnorm p u s) =
        busemann c p + s) ∧
      ∀ s : ℝ, 0 < s →
        ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x : M => busemann c p + s -
          dist x (intrinsicGeodesic (I := I) g hEnorm p u s)) U ∧
        (∀ x : M, busemann c p + s -
          dist x (intrinsicGeodesic (I := I) g hEnorm p u s) ≤ busemann c x) ∧
        busemann c p + s - dist p (intrinsicGeodesic (I := I) g hEnorm p u s) =
          busemann c p := by
  obtain ⟨u, hu, hiso, hcal⟩ := exists_calibrated_intrinsic_ray (I := I) g hEnorm c hc p
  refine ⟨u, hu, hiso, hcal, fun s hs => ?_⟩
  obtain ⟨U, hU, hp, hd⟩ := exists_open_smooth_dist_from_intrinsic_ray
    (I := I) g hEnorm p u hu hiso s hs
  refine ⟨U, hU, hp, contMDiffOn_const.sub hd, fun x => ?_, ?_⟩
  · have h := (lipschitzWith_busemann hc).dist_le_mul
      (intrinsicGeodesic (I := I) g hEnorm p u s) x
    rw [NNReal.coe_one, one_mul, Real.dist_eq, hcal s hs.le, dist_comm] at h
    have hle := (abs_le.mp h).2
    linarith
  · have h := hiso.dist_eq 0 ⟨s, hs.le⟩
    change dist (intrinsicGeodesic (I := I) g hEnorm p u 0)
      (intrinsicGeodesic (I := I) g hEnorm p u s) = |(0 : ℝ) - s| at h
    rw [intrinsicGeodesic_zero (I := I) g hEnorm p u,
      zero_sub, abs_neg, abs_of_nonneg hs.le] at h
    rw [h]
    ring

end DifferentialGeometry.Geometry.Topology

end
