import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactGlobalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

set_option autoImplicit false

noncomputable section
namespace DifferentialGeometry.CheegerGromovCompactness
open Filter Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianConvergenceMaps.noncompact_of_escaping_points
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hconnected : ∀ i, ConnectedSpace (X.obj (f i)).M)
    (x : ∀ i, (X.obj (f i)).M)
    (hescape : Tendsto (fun i =>
      (riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (x i)).toReal)
      atTop atTop) : NoncompactSpace P.M := by
  constructor
  intro hc
  let : CompactSpace P.M := ⟨hc⟩
  obtain ⟨N, hN⟩ := compactLimit_eventually_globalizes F ‹CompactSpace P.M› hconnected
  obtain ⟨_, _, e, _, _, _, _⟩ := hN N le_rfl
  let : ConnectedSpace (X.obj (f N)).M := hconnected N
  let : ConnectedSpace P.M := e.symm.surjective.connectedSpace e.symm.continuous
  obtain ⟨R, hR, hmaps⟩ := F.exists_eventually_image_compact_subset_ball C href
    (RiemannianMetricComplete.of_compact P.metric).complete (K := univ) hc
  obtain ⟨i, hi, hiN, hiR⟩ := (hmaps.and ((eventually_ge_atTop N).and
    (hescape.eventually_gt_atTop R))).exists
  obtain ⟨_, _, ei, hei, _, _, _⟩ := hN i hiN
  obtain ⟨z, hz⟩ := ei.surjective (x i)
  have hx : x i ∈ F.map i '' (univ : Set P.M) :=
    ⟨z, mem_univ z, (hei z).symm.trans hz⟩
  exact (not_le.mpr hiR) (ENNReal.toReal_le_of_le_ofReal hR.le (hi.2 hx))

end DifferentialGeometry.CheegerGromovCompactness
