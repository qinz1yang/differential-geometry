import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RemotePointTriangle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedOpenPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

structure TransversePath (p z : M) (sphere : Set M) where
  curve : ℝ → M
  continuous : ContinuousOn curve (Set.Icc 0 1)
  start : curve 0 = p
  finish : curve 1 = z
  collar : PartialDiffeomorph IC I3 Cylinder M ∞
  collar_domain : Set.univ ×ˢ Set.Icc (-1) 1 ⊆ collar.source
  central_eq : sphere = collar '' (Set.univ ×ˢ ({0} : Set ℝ))
  crossings : Finset ℝ
  crossings_interior : ∀ s ∈ crossings, s ∈ Set.Ioo 0 1
  crossings_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, curve s ∈ sphere ↔ s ∈ crossings
  transverse : ∀ s ∈ crossings,
    deriv (fun t => (collar.symm (curve t)).2) s ≠ 0

def TransversePath.intersection {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : ℤ :=
  ∑ s ∈ c.crossings, if 0 < deriv (fun t => (c.collar.symm (c.curve t)).2) s then 1 else -1


structure MinimizingArm (g : SmoothRiemannianMetric I3 M) (x : M) where
  length : ℝ
  length_pos : 0 < length
  point : ℝ → M
  start : point 0 = x
  minimizing : ∀ s ∈ Set.Icc 0 length, ∀ t ∈ Set.Icc 0 length,
    metricDistance g (point s) (point t) = |s - t|

structure SpatialNeck (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M) where
  eps_pos : 0 < eps
  eps_small : eps < 1 / 11
  Q_pos : 0 < metricScalarAt g x
  cylinder : CylinderReference
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  center : Sphere 2
  center_eq : map (center, 0) = x
  domain : Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ map.source
  comparison : MetricComparisonOn (fun _ => cylinder.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) Q_pos g) map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) {0} (⌈eps⁻¹⌉₊) eps


structure BufferedCanonical (S : SolutionOn (I := I3) (M := M) D)
    (alpha C H : ℝ) (x : M) (t : ℝ) where
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  tolerance_lt : tolerance < alpha
  witness : CanonicalWitness S tolerance C C x t
  a : ℝ
  b : ℝ
  margin : ℝ
  a_pos : 0 < a
  margin_pos : 0 < margin
  radial_margin : b ≤ (2 - margin) * a
  inner_ball : riemannianBallOf (I := I3) (S.base.metric t) x a ⊆ witness.domain.carrier
  outer_ball : witness.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b
  scalar_reserve : ∀ y ∈ witness.domain.carrier,
    C⁻¹ * S.scalar t x < S.scalar t y ∧ S.scalar t y < C * S.scalar t x
  rm_reserve : ∀ y ∈ witness.domain.carrier,
    Real.sqrt (FlowMetricBall.rmNormSq S t y) < C * S.scalar t x
  volume_reserve : witness.alternative.requiresVolume →
    ENNReal.ofReal (C⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
      riemannianVolumeMeasure I3 M (S.base.metric t) witness.domain.carrier
  cap_collar : ∀ cap : LocalCap S tolerance x t witness.domain.carrier,
    (∃ hdepth : ∀ y ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y,
      witness.alternative = CanonicalAlternative.cap cap hdepth) →
    ∃ (v : M) (neck : StrongNeck S alpha v t),
      v ∈ cap.tube ∧ C⁻¹ * S.scalar t x ≤ S.scalar t v ∧ S.scalar t v ≤ C * S.scalar t x ∧
      (∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
        H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z) ∧
      (∀ y ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
        ∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x))

theorem kappa_canonical_neighborhood :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          IsAncientKappaSolution kappa P → PointedFlowScalarAtBase P 1 →
          TangentOrientationSection P.M → Nonempty (CanonicalWitness P.S eps C1 C2 P.basepoint 0) := by
  sorry

theorem good_point_derivatives {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar C : ℝ, 0 < epsStar ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → interior D.carrier ⊆ D.regular →
          ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ x t, Nonempty (WindowedModelWitness eps kappa S x t) →
            (∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
              2 * C * S.scalar t x * Real.sqrt (S.scalar t x) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
            |derivWithin (fun s => S.scalar s x) (Set.Iic t) t| ≤ C * S.scalar t x ^ 2 := by
  exact good_point_derivatives_of_modelCurvatureBound
    (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
      (I := I3) (by simp [ThreeSpace]) hkappa)

theorem local_propagation {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
              let L := 1 + |(X.term i).S.scalar s z|
              Set.Icc (s - c / L) s ⊆ (X.interval i).carrier ∧
                ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s c c L →
                  -6 * (X.scale i)⁻¹ * Phi 0 ≤ (X.term i).S.scalar v y ∧
                  (X.term i).S.scalar v y ≤ 4 * L ∧
                  Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤
                    C * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) := by
  exact canonical_neighborhood_local_propagation hkappa

theorem good_point_buffered_canonical {kappa alpha theta : ℝ}
    (hkappa : 0 < kappa) (ha : 0 < alpha) (haSmall : alpha < 1 / 44)
    (htheta : 0 < theta) (hthetaPi : theta ≤ Real.pi) :
    ∃ Lmin Lmax : ℝ, 0 < Lmin ∧ Lmin < Lmax ∧ ∀ H : ℝ, 0 < H →
      ∃ epsStar C : ℝ, 0 < epsStar ∧ 1 ≤ C ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
          (o : TangentOrientationSection M) (x : M) (t : ℝ),
          OrientedWitness S o epsStar kappa x t →
          Nonempty (BufferedCanonical S alpha C H x t) ∧
          ∀ a b : MinimizingArm (S.base.metric t) x, ∀ s v : ℝ,
            s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
            Real.sqrt (S.scalar t x) * s ∈ Set.Icc Lmin Lmax →
            Real.sqrt (S.scalar t x) * v ∈ Set.Icc Lmin Lmax →
            theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
              metricDistance (S.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
            ∃ (neck : StrongNeck S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Set.Icc s a.length,
                a.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Set.Icc v b.length,
                b.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x)) := by
  sorry

theorem terminal_limit_global_bound {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) := by
  sorry


theorem first_backward_slab {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  sorry

theorem recentered_source_bound {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
          ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
            (X.term i).S.scalar s z ≤ A →
            metricDistance ((X.term i).S.base.metric s) z y ≤ D →
              (X.term i).S.scalar s y ≤ C := by
  sorry

theorem uniform_moving_slice_propagation {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C := by
  sorry

theorem open_nonnegative_sphere_separation
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (hcomp : MetricComplete P)
    (hconn : ConnectedSpace P.M) (o : TangentOrientationSection P.M)
    (hopen : ¬ CompactSpace P.M) (hsec : SecLower P.metric 0 Set.univ)
    (f : Sphere 2 → P.M) (hf : ContMDiff I2 I3 ∞ f) (he : _root_.Topology.IsEmbedding f)
    (himm : ∀ x, Function.Injective (mfderiv I2 I3 f x)) :
    ¬ IsPreconnected (Set.range f)ᶜ ∧
      ∀ p z : P.M, p ∉ Set.range f → z ∉ Set.range f →
        ∀ c : TransversePath p z (Set.range f),
          (c.intersection = 1 ∨ c.intersection = -1) →
            z ∉ connectedComponentIn (Set.range f)ᶜ p := by
  sorry

theorem far_point_separating_neck {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (J : RealTimeInterval) (B : BackwardExtension L J),
        ¬ CompactSpace L.space.M → ∀ D : ℝ, 0 ≤ D →
        (∀ s ∈ J.carrier, ∀ y z : L.space.M,
          |metricDistance (B.solution.base.metric s) y z -
            metricDistance L.space.metric y z| ≤ D) →
        ∀ p : L.space.M, ∃ alpha D0 C0 : ℝ, 0 < alpha ∧ alpha < 1 / 11 ∧
          0 < D0 ∧ 0 < C0 ∧ ∀ s ∈ J.carrier, ∀ y : L.space.M,
            D0 < metricDistance L.space.metric p y →
            C0 < B.solution.scalar s y →
            ∃ (neck : SpatialNeck (B.solution.base.metric s) alpha y) (z : L.space.M),
              metricDistance L.space.metric p y <
                metricDistance L.space.metric p z ∧
              p ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)) ∧
              z ∉ connectedComponentIn (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ p ∧
              ∀ v ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ w ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance (B.solution.base.metric s) v w ≤
                    C0 / Real.sqrt (B.solution.scalar s y) := by
  sorry


def BackwardExtension.pointed {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : PointedFlowData.{u, 0, 0} I3 J where
  M := L.space.M
  topology := L.space.topology
  charted := L.space.charted
  smooth := L.space.smooth
  sigmaCompact := L.space.sigmaCompact
  t2 := L.space.t2
  t2TangentBundle := L.space.t2TangentBundle
  basepoint := L.space.basepoint
  S := B.solution
  isSolution := B.isSolution

structure AncientExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) where
  extension : BackwardExtension L ancientTimeInterval
  agrees : ∀ s ∈ J.carrier, extension.solution.base.metric s = B.solution.base.metric s
  diagonal : ℕ → ℕ
  strictMono : StrictMono diagonal
  maps_agree : extension.subseq = B.subseq ∘ diagonal
  ancient : IsAncientKappaSolution kappa extension.pointed
  normalized : PointedFlowScalarAtBase extension.pointed 1
  global_rm : ∃ C : ℝ, PointedFlowRmNormSqBounded extension.pointed C

theorem ancient_extension {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
