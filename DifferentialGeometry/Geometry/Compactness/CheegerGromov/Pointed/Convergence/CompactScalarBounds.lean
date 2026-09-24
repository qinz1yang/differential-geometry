import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactGlobalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}

theorem exists_eventually_scalar_lower_bound_of_compact_positive_limit
    (F : PointedRiemannianConvergenceMaps X L subseq)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    [CompactSpace L.M] (hconn : ∀ i, PreconnectedSpace (X.obj (subseq i)).M)
    (hpositive : ∀ x : L.M, 0 < metricScalarAt L.metric x) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, ∀ x : (X.obj (subseq i)).M,
      c ≤ metricScalarAt (X.obj (subseq i)).metric x := by
  obtain ⟨p, hp, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨L.basepoint, mem_univ _⟩ (metricScalar_smooth L.metric).continuous.continuousOn
  let c := metricScalarAt L.metric p / 2
  have hc : 0 < c := half_pos (hpositive p)
  obtain ⟨N, hN⟩ := pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical univ isCompact_univ c hc
  refine ⟨c, hc, ?_⟩
  have hconnected (i : ℕ) : ConnectedSpace (X.obj (subseq i)).M := by
    let _ : PreconnectedSpace (X.obj (subseq i)).M := hconn i
    let _ : Nonempty (X.obj (subseq i)).M := ⟨(X.obj (subseq i)).basepoint⟩
    exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  obtain ⟨N0, hN0⟩ := compactLimit_eventually_globalizes F inferInstance hconnected
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop N] with i hi hNi
  obtain ⟨_, _, e, he, _, _, _⟩ := hN0 i hi
  intro x
  obtain ⟨y, hy⟩ := e.surjective x
  have hmap : F.map i y = x := (he y).symm.trans hy
  rw [← hmap]
  have herr := (abs_lt.mp ((hN i hNi).2 y (mem_univ _))).1
  have hlow : metricScalarAt L.metric p ≤ metricScalarAt L.metric y := hmin (mem_univ y)
  dsimp only [c] at herr ⊢
  linarith

theorem not_compact_space_of_positive_scalar_limit_of_source_scalar_tendsto_zero
    (F : PointedRiemannianConvergenceMaps X L subseq)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hconn : ∀ i, PreconnectedSpace (X.obj (subseq i)).M)
    (hpositive : ∀ x : L.M, 0 < metricScalarAt L.metric x)
    (x : ∀ i, (X.obj (subseq i)).M)
    (hzero : Tendsto (fun i => metricScalarAt (X.obj (subseq i)).metric (x i))
      atTop (𝓝 0)) :
    ¬ CompactSpace L.M := by
  intro hcompact
  let _ : CompactSpace L.M := hcompact
  obtain ⟨c, hc, hbound⟩ := exists_eventually_scalar_lower_bound_of_compact_positive_limit
    F C hcanonical hconn hpositive
  have hsmall : ∀ᶠ i in atTop, metricScalarAt (X.obj (subseq i)).metric (x i) < c :=
    hzero.eventually (Iio_mem_nhds hc)
  obtain ⟨i, hi, hsmalli⟩ := (hbound.and hsmall).exists
  exact not_lt_of_ge (hi (x i)) hsmalli

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}

theorem exists_eventually_scalar_bounds_and_bounded_radius_of_compact_positive_limit
    (F : PointedRiemannianConvergenceMaps X L subseq)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    [CompactSpace L.M] [PreconnectedSpace L.M]
    (hconn : ∀ i, PreconnectedSpace (X.obj (subseq i)).M)
    (hpositive : ∀ x : L.M, 0 < metricScalarAt L.metric x) :
    ∃ r c B : ℝ, 0 < r ∧ 0 < c ∧ 0 < B ∧ ∀ᶠ i in atTop,
      CompactSpace (X.obj (subseq i)).M ∧
      ∀ x : (X.obj (subseq i)).M,
        x ∈ riemannianClosedBallOf (X.obj (subseq i)).metric
          (X.obj (subseq i)).basepoint r ∧
        c ≤ metricScalarAt (X.obj (subseq i)).metric x ∧
        metricScalarAt (X.obj (subseq i)).metric x ≤ B := by
  have hcomplete : MetricComplete L := by
    unfold MetricComplete
    infer_instance
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    intro hzero
    have hz := metricScalarAt_eq_zero_of_finrank_eq_zero L.metric hzero L.basepoint
    exact (ne_of_gt (hpositive L.basepoint)) hz⟩
  have hconnected (i : ℕ) : ConnectedSpace (X.obj (subseq i)).M := by
    let _ : PreconnectedSpace (X.obj (subseq i)).M := hconn i
    exact { toPreconnectedSpace := inferInstance, toNonempty := ⟨(X.obj (subseq i)).basepoint⟩ }
  obtain ⟨N, hN⟩ := compactLimit_eventually_globalizes F inferInstance hconnected
  obtain ⟨c, hc, hlow⟩ := exists_eventually_scalar_lower_bound_of_compact_positive_limit
    F C hcanonical hconn hpositive
  obtain ⟨B, hB, hup⟩ := exists_pointed_scalar_bound_on_compact C hcanonical univ isCompact_univ
  have href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric F i
  obtain ⟨r, hr, hcapture⟩ := F.exists_eventually_image_compact_subset_ball
    C href hcomplete (K := univ) isCompact_univ
  refine ⟨r, c, B, hr, hc, hB, ?_⟩
  filter_upwards [eventually_ge_atTop N, hlow, hup, hcapture] with i hi hl hu hcap
  obtain ⟨_, _, e, he, _, _, hcompact⟩ := hN i hi
  refine ⟨hcompact, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := e.surjective x
  have hxy : F.map i y = x := (he y).symm.trans hy
  refine ⟨?_, hl x, ?_⟩
  · exact hxy ▸ hcap.2 ⟨y, mem_univ y, rfl⟩
  · rw [← hxy]
    exact (le_abs_self _).trans (hu.2 y (mem_univ y))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
