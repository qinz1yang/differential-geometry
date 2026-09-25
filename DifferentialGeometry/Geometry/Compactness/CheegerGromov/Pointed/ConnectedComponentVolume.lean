import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds

noncomputable section
open Set Filter DifferentialGeometry
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianManifold.connectedComponent_closedBall
    (X : PointedRiemannianManifold.{u, uE, uH} I) (r : ℝ) :
    riemannianClosedBallOf X.connectedComponent.metric X.connectedComponent.basepoint r =
      (Subtype.val : connectedComponentOpen (I := I) X.basepoint → X.M) ⁻¹'
        riemannianClosedBallOf X.metric X.basepoint r := by
  ext y
  change riemannianEDistOf (X.metric.restrictOpen (connectedComponentOpen (I := I) X.basepoint))
      ⟨X.basepoint, mem_connectedComponent⟩ y ≤ ENNReal.ofReal r ↔
    riemannianEDistOf X.metric X.basepoint y.val ≤ ENNReal.ofReal r
  exact (congrArg (fun t : ℝ≥0∞ => t ≤ ENNReal.ofReal r)
    (riemannianEDistOf_restrictOpen_of_isClosed X.metric
    (connectedComponentOpen (I := I) X.basepoint) isClosed_connectedComponent
    ⟨X.basepoint, mem_connectedComponent⟩ y)).to_iff


theorem PointedRiemannianManifold.connectedComponent_ball_volume
    (X : PointedRiemannianManifold.{u, uE, uH} I) (x : X.connectedComponent.M) (r : ℝ) :
    Integral.Measure.riemannianVolumeMeasure I X.connectedComponent.M X.connectedComponent.metric
        (riemannianBallOf X.connectedComponent.metric x r) =
      Integral.Measure.riemannianVolumeMeasure I X.M X.metric
        (riemannianBallOf X.metric x.val r) :=
  Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
    X.metric (connectedComponentOpen (I := I) X.basepoint) isClosed_connectedComponent x r

theorem PointedRiemannianSeq.inner_ball_volume_lower_bound_connectedComponent
    (X : PointedRiemannianSeq.{u, uE, uH} I) (rho : ℝ)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop,
        ∀ x ∈ riemannianClosedBallOf (X.connectedComponent.obj n).metric
            (X.connectedComponent.obj n).basepoint r,
          ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
            Integral.Measure.riemannianVolumeMeasure I (X.connectedComponent.obj n).M
              (X.connectedComponent.obj n).metric
              (riemannianBallOf (X.connectedComponent.obj n).metric x a) := by
  intro r R hr hrR hR C hC
  obtain ⟨a,κ,ha,hκ,hra,hac,hv⟩ := hvol r R hr hrR hR C hC
  refine ⟨a,κ,ha,hκ,hra,hac,?_⟩
  filter_upwards [hv] with n hn x hx
  have hcenter : x.val ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r := by
    exact (Set.ext_iff.mp ((X.obj n).connectedComponent_closedBall r) x).mp hx
  have heq := (X.obj n).connectedComponent_ball_volume x a
  exact (hn x.val hcenter).trans_eq heq.symm

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Set Filter DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianManifold.isCompact_closedBall_connectedComponent
    (X : PointedRiemannianManifold.{u, uE, uH} I) (R : ℝ)
    (hcompact : IsCompact (riemannianClosedBallOf X.metric X.basepoint R)) :
    IsCompact (riemannianClosedBallOf X.connectedComponent.metric X.connectedComponent.basepoint R) := by
  rw [X.connectedComponent_closedBall R]
  have hsubset : riemannianClosedBallOf X.metric X.basepoint R ⊆
      (connectedComponentOpen (I := I) X.basepoint : Set X.M) := by
    intro y hy
    apply Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I) X.metric X.basepoint (max R 0 + 1)
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by linarith [le_max_left R 0]))
  change IsCompact ((Subtype.val : connectedComponentOpen (I := I) X.basepoint →
    X.M) ⁻¹' riemannianClosedBallOf X.metric X.basepoint R)
  exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact
    (fun y hy => ⟨⟨y, hsubset hy⟩, rfl⟩)

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HasLocalCurvDerivBound.connectedComponent
    {X : PointedRiemannianManifold.{u, uE, uH} I} {R C : ℝ} {p : ℕ}
    (h : HasLocalCurvDerivBound (I := I) X X.basepoint R p C) :
    HasLocalCurvDerivBound (I := I) X.connectedComponent X.connectedComponent.basepoint R p C := by
  intro y hy
  have hy' : y.val ∈ riemannianClosedBallOf X.metric X.basepoint R :=
    (Set.ext_iff.mp (X.connectedComponent_closedBall R) y).mp hy
  exact (curvDerivNorm_restrictOpen X.metric
    (connectedComponentOpen (I := I) X.basepoint) p y).trans_le (h y.val hy')

end DifferentialGeometry.CheegerGromovCompactness

end
