import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianLineLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceLineScalarFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance staticSurfaceLineC1 {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

section ScalarNormalization

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance staticSurfaceLimitTopology : TopologicalSpace L.M := L.topology
private local instance staticSurfaceLimitCharted : ChartedSpace H L.M := L.charted
private local instance staticSurfaceLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance staticSurfaceLimitT2 : T2Space L.M := L.t2


theorem staticScalarNormalized_limit_scalar_one
    (g : SmoothRiemannianMetric I M) (x : ℕ → M)
    (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      (spatialRescaledPointedSeq g x (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i))) L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) :
    metricScalarAt (I := I) L.metric L.basepoint = 1 := by
  apply pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
  intro k
  change metricScalarAt (I := I)
    (scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x (subseq k))) ^ 2)
      (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ (subseq k)))) g) (x (subseq k)) = 1
  rw [metricScalarAt_scaleMetric, Real.sq_sqrt (hQ (subseq k)).le]
  exact inv_mul_cancel₀ (hQ (subseq k)).ne'

end ScalarNormalization


theorem false_of_static_surface_scalar_normalized_compactness
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)) *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    (P : MetricCompactLimit (I := I)
      (spatialRescaledPointedSeq g x (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i))))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hconnected : @ConnectedSpace P.limit.M P.limit.topology) : False := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let L := P.limit
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : ConnectedSpace L.M := hconnected
  have hD : P.convergence.metrics.domain =
      CanonicalMetricCompactness.canonicalSourceData P.maps := funext hcanonical
  have hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) P.maps
        (CanonicalMetricCompactness.canonicalSourceData P.maps) K 2 := by
    intro K hK
    have h := P.convergence.metrics.converges K hK 2
    rw [hD] at h
    exact h
  have hRic : ∀ y : L.M, ∀ v : TangentSpace I y,
      0 ≤ ricciTensor (I := I) L.metric y v v := by
    apply ricci_nonnegative_of_pointed_canonical_convergence hconv
    apply Filter.Eventually.of_forall
    intro k y _hy
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) _ (P.maps.map k y)).mpr
    intro v w
    change metricRm04StandardAt (I := I)
      (scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x (P.subseq k))) ^ 2)
        (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ (P.subseq k)))) g)
      (P.maps.map k y) v w w v ≥ 0
    rw [metricRmStandard_scale]
    exact mul_nonneg (sq_nonneg _)
      (((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
        (I := I) g (P.maps.map k y)).mp (hsec (P.maps.map k y))) v w)
  have hscalar : metricScalarAt (I := I) L.metric L.basepoint = 1 :=
    staticScalarNormalized_limit_scalar_one g x hQ P.maps P.convergence.metrics hcanonical
  have hreference : ∀ k, (P.convergence.metrics.domain k).referenceMetric =
      (P.convergence.metrics.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    rfl
  obtain ⟨gamma, _hgamma, _hbase, hline⟩ :=
    exists_riemannian_line_of_rescaled_pointed_convergence g hg hsec p x
      (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
      (fun i => Real.sqrt_pos.mpr (hQ i)) hescape hscaled P.strictMono
      P.maps P.convergence.metrics hreference P.limit_complete hconnected
  have hcompleteLimit : RiemannianMetricComplete (I := I) L.metric :=
    ⟨MetricComplete.complete L P.limit_complete⟩
  have hpos : 0 < metricScalarAt (I := I) L.metric L.basepoint := by
    rw [hscalar]
    exact zero_lt_one
  exact not_intrinsic_line_of_surface_scalar_pos L.metric hcompleteLimit hdim hRic
    L.basepoint hpos ⟨gamma, hline⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
