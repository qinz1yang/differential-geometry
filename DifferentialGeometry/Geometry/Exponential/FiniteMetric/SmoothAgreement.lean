import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity

/-!
# The ported exponential map of a smooth metric is the smooth exponential map

For a smooth metric `g`:

* `mem_expDomain_iff_mem_smooth_expDomain`, `expMap_eq_smooth_expMap`: the finite-order
  `g.expDomain`/`g.expMap` agree with the smooth API's `Exponential.expDomain`/`Exponential.expMap`;
* if `M` is complete for the Riemannian distance and the bundle norm is the norm of `g`
  (`IsMetricNorm g`): `geodesicFlow_eq_intrinsicVelocityLift` (the flow is defined for all times and
  is the velocity lift of `intrinsicGeodesic`), `geodesicFlowDomain_eq_univ_of_isMetricNorm`,
  `proj_geodesicFlow_eq_intrinsicGeodesic`, `expMap_smul_eq_intrinsicGeodesic`,
  `expMapIntrinsic_eq_expMap`.

So every result about the ported flow applies to the chapter-13 consumers of `intrinsicGeodesic`
and `expMapIntrinsic`, and conversely. Lane CM-H (package CM, row 3), 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

open DifferentialGeometry.Geometry.Riemannian.Exponential
  (intrinsicGeodesic expMapIntrinsic intrinsicVelocityLift)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The finite-order exponential domain of a smooth metric is the smooth one. -/
theorem mem_expDomain_iff_mem_smooth_expDomain
    {g : DifferentialGeometry.SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    (⟨p, v⟩ : TangentBundle I M) ∈ g.expDomain ↔
      v ∈ DifferentialGeometry.Geometry.Riemannian.Exponential.expDomain g p :=
  mem_geodesicFlowDomain_iff_mem_maximalGeodesicInterval (g := g) (t := 1)

/-- On its domain, the finite-order exponential map of a smooth metric is the smooth one. -/
theorem expMap_eq_smooth_expMap
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hv : (⟨p, v⟩ : TangentBundle I M) ∈ g.expDomain) :
    g.expMap (⟨p, v⟩ : TangentBundle I M) =
      DifferentialGeometry.Geometry.Riemannian.Exponential.expMap g p v :=
  proj_geodesicFlow_eq_maximalGeodesic g p v hv

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Agreement with the intrinsic geodesic (complete smooth metric).** The ported flow of a
smooth metric whose bundle norm is the metric norm is defined at every time, and its orbit is the
velocity lift of the smooth API's complete geodesic `intrinsicGeodesic`. -/
theorem geodesicFlow_eq_intrinsicVelocityLift
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (p : M)
    (v : TangentSpace I p) (t : ℝ) :
    ((⟨p, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ∧
      g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) t = intrinsicVelocityLift g hEnorm p v t := by
  have hcurve :=
    DifferentialGeometry.Geometry.Riemannian.Exponential.lift_isIntegral g hEnorm p v
  rw [← geodesicSpray_eq_geodesicVectorField_fun g] at hcurve
  have h0 := DifferentialGeometry.Geometry.Riemannian.Exponential.velocityLift_zero g hEnorm p v
  have hon := hcurve.isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))
  have h0mem : (0 : ℝ) ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
  have htmem : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  exact ⟨hon.subset_maximalIntegralCurveInterval h0mem h0 htmem,
    hon.eqOn_maximalIntegralCurve
      ((g.contMDiff_geodesicSpray (r := ⊤)).of_le (by exact_mod_cast le_top)) h0mem h0 htmem⟩

/-- The ported flow of a complete smooth metric is complete. -/
theorem geodesicFlowDomain_eq_univ_of_isMetricNorm
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) :
    g.geodesicFlowDomain = univ := by
  refine eq_univ_of_forall fun q => ?_
  obtain ⟨⟨p, v⟩, t⟩ := q
  exact (geodesicFlow_eq_intrinsicVelocityLift g hEnorm p v t).1

/-- The projected ported flow of a complete smooth metric is `intrinsicGeodesic`. -/
theorem proj_geodesicFlow_eq_intrinsicGeodesic
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (p : M)
    (v : TangentSpace I p) (t : ℝ) :
    (g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) t).proj = intrinsicGeodesic g hEnorm p v t :=
  congrArg TotalSpace.proj (geodesicFlow_eq_intrinsicVelocityLift g hEnorm p v t).2

/-- Radial form: `exp_p (t v) = γ_v(t)` with the smooth API's complete geodesic. -/
theorem expMap_smul_eq_intrinsicGeodesic
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (p : M)
    (v : TangentSpace I p) (t : ℝ) :
    g.expMap (⟨p, t • v⟩ : TangentBundle I M) = intrinsicGeodesic g hEnorm p v t := by
  rw [← DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_smul g hEnorm p v t]
  exact proj_geodesicFlow_eq_intrinsicGeodesic g hEnorm p (t • v) 1

/-- The smooth API's `expMapIntrinsic` is the ported exponential map. -/
theorem expMapIntrinsic_eq_expMap
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (p : M)
    (v : TangentSpace I p) :
    expMapIntrinsic g hEnorm p v = g.expMap (⟨p, v⟩ : TangentBundle I M) :=
  (proj_geodesicFlow_eq_intrinsicGeodesic g hEnorm p v 1).symm

/-- Consumer: through the agreement, the ported regularity theorem makes the smooth API's
exponential map smooth on the whole tangent bundle of a complete smooth metric. -/
theorem contMDiff_expMapIntrinsic_tangentBundle
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) :
    ContMDiff I.tangent I ∞ (fun q : TangentBundle I M => expMapIntrinsic g hEnorm q.proj q.snd) := by
  have hdom : g.expDomain = univ := by
    rw [expDomain, geodesicFlowDomain_eq_univ_of_isMetricNorm g hEnorm, preimage_univ]
  have h : ContMDiffOn I.tangent I ∞ g.expMap g.expDomain := g.contMDiffOn_expMap (r := ⊤) le_top
  rw [hdom, contMDiffOn_univ] at h
  refine h.congr fun q => ?_
  exact expMapIntrinsic_eq_expMap g hEnorm q.proj q.snd

end Bundle.ContMDiffRiemannianMetric
