import DifferentialGeometry.Geometry.Neck.UnboundedComponent
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.RemoteLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import DifferentialGeometry.Geometry.Comparison.Soul.SoulRetraction
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_far_spatialNeck_unbounded_separated_component_of_nonnegative
    : ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        [ConnectedSpace M] [NoncompactSpace M],
      ∀ (g0 : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g0 →
      DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g0 →
      ∀ (p : M) (A : ℝ), 0 ≤ A →
      ∃ D0 C0 : ℝ, 0 < D0 ∧ 0 < C0 ∧
      ∀ (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g →
        DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g →
        ∀ (eta : ℝ) (x : M) (nk : SpatialNeck g eta x), eta ≤ eta0 →
          (∀ q r : M, |metricDistance g q r - metricDistance g0 q r| ≤ A) →
          D0 < metricDistance g0 p x → C0 < metricScalarAt g x →
          ∀ R : ℝ, ∃ z : M, R < metricDistance g0 p z ∧
            z ∉ connectedComponentIn (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ p := by
  let epsilon := spatialNeckControlEpsilon
  have hepsilon : 0 < epsilon := spatialNeckControlEpsilon_pos
  obtain ⟨eta0, heta0, hconvert⟩ := exists_spatialNeckWitness_of_spatialNeck hepsilon
  refine ⟨eta0, heta0, ?_⟩
  intro M _ _ _ _ _ _ _ g0 hcomplete0 hsec0 p A hA
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun z : M => TangentSpace I3 z) := ⟨g0.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : M => TangentSpace I3 z) :=
    ⟨⟨g0.inner, g0.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  let _ : CompleteSpace M := hcomplete0.complete
  have hEnorm0 : IsMetricNorm g0 := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm g0 z v
  let _ : MetricSpace M := riemMetricSpace (I := I3) (M := M)
  let _ : ProperSpace M := properSpace_riemMetric hcomplete0.complete g0 hEnorm0
  let _ : IsRiemannianManifold I3 M := ⟨fun z w => by
    rw [edist_dist, riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I3) z w)⟩
  have hdist0 (z w : M) : dist z w = metricDistance g0 z w := by
    rw [riemMetric_dist_eq (I := I3), ← riemannianEDistOf_eq_riemannianEDist g0 hEnorm0]
    rfl
  obtain ⟨S, _hSne, hScompact, _hconv, _hboundary, ρ, hrange, hρ, _hfix⟩ :=
    exists_soul_homotopic_retraction g0 hEnorm0 hsec0
  obtain ⟨Rs, hRs, hSbound⟩ := hScompact.isBounded.subset_closedBall_lt 0 p
  obtain ⟨Rr, hRr, hrays⟩ := exists_radius_busemann_ray_gt g0 hEnorm0 hsec0 p (2 * A + 1)
  let K := spatialNeckCoreRadiusConstant epsilon
  have hK : 0 < K := spatialNeckCoreRadiusConstant_pos epsilon
  let X := ULift.{0} M
  let refMetric : MetricSpace X :=
    (Homeomorph.ulift : X ≃ₜ M).isEmbedding.comapMetricSpace ULift.down
  let _ : MetricSpace X := refMetric
  let _ : PseudoMetricSpace X := refMetric.toPseudoMetricSpace
  let _ : Dist X := refMetric.toPseudoMetricSpace.toDist
  let e : M ≃ₜ X := Homeomorph.ulift.symm
  have heiso : Isometry e := by
    apply Isometry.of_dist_eq
    intro q r
    rfl
  let _ : ProperSpace X := heiso.antilipschitzWith.properSpace e.continuous e.surjective
  have href (q r : M) : dist (e q) (e r) = metricDistance g0 q r := hdist0 q r
  refine ⟨Rs + Rr + A + K + 1, 1, by positivity, zero_lt_one, ?_⟩
  intro g hg hsec eta x nk heta herror hfar hQ R
  obtain ⟨W, hW⟩ := hconvert M g hg x eta heta nk
  have hsphere : W.centralSphere = nk.map '' (univ ×ˢ ({0} : Set ℝ)) := by
    rw [W.centralSphere_eq_range]
    have hcenter (y : SpatialNeckSphere) : W.centralMap y = nk.map (y, 0) := by
      unfold SpatialNeckWitness.centralMap
      rw [hW]
      exact congrArg nk.map (cylinderAxialScale_central (Real.sqrt 2) (by positivity) y)
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(y, 0), ⟨mem_univ _, rfl⟩, (hcenter y).symm⟩
    · rintro ⟨⟨y, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨y, hcenter y⟩
  have hfarRef : Rr < dist p x := by rw [hdist0]; linarith
  obtain ⟨c0, hc0, hcstart, hclevel⟩ := hrays x hfarRef
  let c : ℝ≥0 → X := e ∘ c0
  have hc : Isometry c := heiso.comp hc0
  have hbuse (q : M) : busemann c (e q) = busemann c0 q := by
    unfold busemann busemannApprox
    rfl
  have hlevel : busemann c (e p) + 2 * A < busemann c (e x) := by
    rw [hbuse, hbuse, ← hcstart, busemann_ray hc0 0]
    change (0 : ℝ) + 2 * A < busemann c0 x
    linarith
  have hSref (q : M) (hq : q ∈ S) : dist (e p) (e q) ≤ Rs := by
    have hh := hSbound hq
    simpa only [Metric.mem_closedBall, dist_comm, heiso.dist_eq] using hh
  let _ : RiemannianBundle (fun z : M => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  have hEnorm : IsMetricNorm g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  let _ : MetricSpace M := riemMetricSpace (I := I3) (M := M)
  let _ : PseudoMetricSpace X := refMetric.toPseudoMetricSpace
  let _ : Dist X := refMetric.toPseudoMetricSpace.toDist
  let _ : IsRiemannianManifold I3 M := ⟨fun z w => by
    rw [edist_dist, riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I3) z w)⟩
  have hdist (z w : M) : dist z w = metricDistance g z w := by
    rw [riemMetric_dist_eq (I := I3), ← riemannianEDistOf_eq_riemannianEDist g hEnorm]
    rfl
  have herr (q r : M) : |dist q r - dist (e q) (e r)| ≤ A := by
    rw [hdist, href]
    exact herror q r
  have hsqrt : 1 ≤ Real.sqrt (metricScalarAt g x) := Real.le_sqrt_of_sq_le (by linarith)
  have hkradius : K / Real.sqrt (metricScalarAt g x) ≤ K := div_le_self hK.le hsqrt
  have havoid : Disjoint (range ρ) W.centralSphere := by
    rw [hrange]
    apply Set.disjoint_left.mpr
    intro q hqS hqneck
    have hcore := W.core_dist_le hEnorm le_rfl (W.centralSphere_subset_core hqneck)
    have hnear : dist (e x) (e q) ≤ K + A := by
      have hh := (abs_le.mp (herr x q)).1
      linarith
    have htri := dist_triangle (e p) (e q) (e x)
    rw [dist_comm (e q) (e x), href p x] at htri
    linarith [hSref q hqS]
  have hfarCore : K / Real.sqrt (metricScalarAt g x) + A < dist (e p) (e x) := by
    rw [href]
    linarith
  obtain ⟨z, hzfar, hzcomp⟩ := W.exists_separated_dist_gt_of_reference_ray
    hEnorm le_rfl hsec e A herr c hc p hlevel hfarCore ρ hρ havoid R
  refine ⟨z, ?_, ?_⟩
  · simpa only [href] using hzfar
  · simpa only [hsphere] using hzcomp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
