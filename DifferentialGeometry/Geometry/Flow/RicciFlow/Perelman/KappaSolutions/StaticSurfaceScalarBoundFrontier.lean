import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaticSurfaceLocalCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseCompactnessReduction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [CompleteSpace E] in
theorem MetricCompactSeed.hasInjRadiusAt_mu
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X) (k : ℕ) (x : (X.obj k).M) :
    HasInjRadiusAt (I := I) (X.obj k) x
      (b.decay.mu (b.decay.dist k x (X.obj k).basepoint)) :=
  b.decay.decay k x

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance scalarBoundFrontierC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance scalarBoundFrontierMeasurable : MeasurableSpace M := borel M
private local instance scalarBoundFrontierBorel : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M)
  (hjets : ∀ A : ℝ, 0 < A → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : M) (r : ℝ) (hQ : 0 < metricScalarAt (I := I) g q),
      (∀ z, (riemannianEDistOf (I := I) g z q).toReal < r →
        metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g q) →
      A + 1 / 2 < r * Real.sqrt (metricScalarAt (I := I) g q) →
      ∀ y : M,
        riemannianEDistOf (I := I) (scaleMetric (metricScalarAt (I := I) g q) hQ g)
          q y ≤ ENNReal.ofReal A →
        curvDerivNorm (I := I) m (scaleMetric (metricScalarAt (I := I) g q) hQ g) y ≤ C)

include hjets

theorem exists_staticScalarNormalized_metric_compactness_of_seedFrontier
    (hg : RiemannianMetricComplete (I := I) g)
    (x : ℕ → M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i))
    (hseed : LocalCurvatureJetSeedFrontier (I := I)
      (spatialRescaledPointedSeq g x
        (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i))))
    (hlocal : ∀ i z, (riemannianEDistOf (I := I) g z (x i)).toReal < r i →
      metricScalarAt (I := I) g z ≤ 4 * metricScalarAt (I := I) g (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (metricScalarAt (I := I) g (x i)))
      atTop atTop)
    (hinj : BaseInjBound (I := I)
      (spatialRescaledPointedSeq g x
        (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i)))) :
    ∃ P : MetricCompactLimit (I := I)
      (spatialRescaledPointedSeq g x
        (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
        (fun i => Real.sqrt_pos.mpr (hQ i))),
      (∀ k, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  let lam := fun i => Real.sqrt (metricScalarAt (I := I) g (x i))
  let hlam : ∀ i, 0 < lam i := fun i => Real.sqrt_pos.mpr (hQ i)
  let X := spatialRescaledPointedSeq g x lam hlam
  have hcomplete : SeqMetricComplete (I := I) X :=
    spatialRescaledPointedSeq_complete g hg x lam hlam
  have hlocalJets : LocalCurvatureJetBound (I := I) X := by
    intro A hA m
    obtain ⟨C, hC, hbound⟩ := hjets A hA m
    refine ⟨C, hC, ?_⟩
    filter_upwards [hexpand.eventually_gt_atTop (A + 1 / 2)] with i hi
    refine fun y hy => ?_
    have hmetric : (X.obj i).metric = scaleMetric (metricScalarAt (I := I) g (x i))
        (hQ i) g := by
      change scaleMetric (Real.sqrt (metricScalarAt (I := I) g (x i)) ^ 2)
        (sq_pos_of_pos (Real.sqrt_pos.mpr (hQ i))) g = _
      congr 1
      exact Real.sq_sqrt (hQ i).le
    rw [hmetric] at hy ⊢
    exact hbound (x i) (r i) (hQ i) (hlocal i) hi y hy
  obtain ⟨P, hcanonical, _hreference, hconnected⟩ :=
    exists_local_pointed_metric_compactness_of_localCurvatureJetSeedFrontier (I := I) X
      hcomplete (spatialRescaledPointedSeq_connected g x lam hlam) hinj hlocalJets
      (show LocalCurvatureJetSeedFrontier (I := I) X from hseed)
  exact ⟨P, hcanonical, hconnected⟩

theorem static_surface_scalar_bddAbove_of_local_normalized_jets_and_seedFrontier
    (hseed : ∀ (x : ℕ → M) (hQ : ∀ i, 0 < metricScalarAt (I := I) g (x i)),
      LocalCurvatureJetSeedFrontier (I := I)
        (spatialRescaledPointedSeq g x
          (fun i => Real.sqrt (metricScalarAt (I := I) g (x i)))
          (fun i => Real.sqrt_pos.mpr (hQ i))))
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 2)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (hsec : ∀ z, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hnc : ∀ (p : M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) g p rho,
        rho ^ 4 * Tensor0SBundle.normSq0S (I := I) g z 4
          (metricRm04At (I := I) g z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf (I := I) g p rho)) :
    BddAbove (Set.range (metricScalarAt (I := I) g)) := by
  classical
  by_contra hunbounded
  let p : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨x, r, hQ, _hr, _hQescape, hexpand, hdist, hscaled, hlocal, ⟨hinj⟩, _hbase⟩ :=
    exists_static_surface_blowup_with_baseInjBound g hg hdim hnonneg hsec
      kappa hkappa hnc hunbounded p
  obtain ⟨P, hcanonical, hconnected⟩ :=
    exists_staticScalarNormalized_metric_compactness_of_seedFrontier g hjets hg
      x r hQ (hseed x hQ) hlocal hexpand hinj
  exact false_of_static_surface_scalar_normalized_compactness g hg hdim hsec
    p x hQ hdist hscaled P hcanonical hconnected

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
