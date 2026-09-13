import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RemotePointTriangle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedOpenPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

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

theorem CanonicalWitness.exists_bufferedCanonical
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {tolerance C1 C2 alpha H : ℝ}
    (W : CanonicalWitness S tolerance C1 C2 x t) (htol : tolerance < alpha)
    (hcap : ∀ cap : LocalCap S tolerance x t W.domain.carrier,
      (∃ hdepth : ∀ y ∈ cap.tube,
          10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y,
        W.alternative = CanonicalAlternative.cap cap hdepth) →
      ∃ (v : M) (neck : StrongNeck S alpha v t),
        v ∈ cap.tube ∧
        (max C1 C2 + 1)⁻¹ * S.scalar t x ≤ S.scalar t v ∧
        S.scalar t v ≤ (max C1 C2 + 1) * S.scalar t x ∧
        (∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z) ∧
        (∀ y ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          ∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
            metricDistance (S.base.metric t) y z ≤
              (max C1 C2 + 1) / Real.sqrt (S.scalar t x))) :
    Nonempty (BufferedCanonical S alpha (max C1 C2 + 1) H x t) := by
  obtain ⟨hC, hC1, hC2, hscalar, hrm, hvolume⟩ := W.strict_curvature_volume_reserves
  let W' : CanonicalWitness S tolerance (max C1 C2 + 1) (max C1 C2 + 1) x t :=
    W.enlarge_constants hC1.le hC2.le
  obtain ⟨a, b, margin, ha, har, hm, hbm, hinner, houter⟩ := W'.exists_radial_reserve
  refine ⟨{ tolerance := tolerance
            tolerance_pos := W.eps_pos
            tolerance_lt := htol
            witness := W'
            a := a
            b := b
            margin := margin
            a_pos := ha
            margin_pos := hm
            radial_margin := hbm.le
            inner_ball := hinner
            outer_ball := houter
            scalar_reserve := hscalar
            rm_reserve := hrm
            volume_reserve := fun hv => hvolume (by
              simpa only [W', CanonicalWitness.enlarge_constants_requiresVolume] using hv)
            cap_collar := fun cap hc => ?_ }⟩
  obtain ⟨hdepth, halteq⟩ := hc
  simp only [W', CanonicalWitness.enlarge_constants] at halteq
  have halteq' : W.alternative = CanonicalAlternative.cap cap hdepth := by
    cases hW : W.alternative with
    | neck data =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        exact absurd halteq (by simp)
    | cap data deep =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        cases halteq
        rfl
    | positive whole data hsec =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        exact absurd halteq (by simp)
    | round whole data =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        exact absurd halteq (by simp)
  exact hcap cap ⟨hdepth, halteq'⟩

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

theorem terminal_limit_of_metric_compact_limit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (hPhi : AdmissiblePinchingFunction Phi)
    (P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (capture : MetricSourceCapture P.maps)
    (precompact : ∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source))
    (connected_domains : ∀ i, IsConnected (P.maps.partialDiffeomorph i).source)
    (nested : ∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
      (P.maps.partialDiffeomorph (i + 1)).source)
    (orientation : TangentOrientationSection P.limit.M)
    (orientation_preserved : ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
      ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
        PreservesTangentOrientationAt orientation (X.orientation (P.subseq i))
          (P.maps.partialDiffeomorph i) y hf)
    (scalar_bound : ∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C)
    (noncollapse : MetricNoncollapsed P.limit kappa Set.univ)
    (hconnected : ConnectedSpace P.limit.M) :
    Nonempty (TerminalLimit X) := by
  have hscalar_one : metricScalarAt P.limit.metric P.limit.basepoint = 1 :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains
      P.convergence.metrics hcanonical
      (c := 1) (fun k => by
        have hk := X.base_one (P.subseq k)
        simp only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar] at hk ⊢
        exact hk)
  exact ⟨{ space := P.limit
           subseq := P.subseq
           strictMono := P.strictMono
           maps := P.maps
           converges := P.convergence.metrics
           canonical_domains := hcanonical
           capture := capture
           precompact := precompact
           connected_domains := connected_domains
           nested := nested
           connected := hconnected
           orientation := orientation
           orientation_preserved := orientation_preserved
           complete := P.limit_complete
           nonnegative := blowup_limit_nonnegative X hPhi
             P.limit P.subseq P.strictMono P.maps P.convergence.metrics hcanonical
           scalar_one := hscalar_one
           scalar_bound := scalar_bound
           noncollapse := noncollapse }⟩

theorem terminal_limit_global_bound_of_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (hcompactness : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X →
        ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
          ConnectedSpace P.limit.M ∧
          MetricSourceCapture P.maps ∧
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) ∧
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) ∧
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) ∧
          (∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C) ∧
          MetricNoncollapsed P.limit kappa Set.univ) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) := by
  let _ := hkappa
  let _ := hsigma
  obtain ⟨epsStar, hpos, h⟩ := hcompactness
  refine ⟨epsStar, hpos, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanonical, hconn, hcap, hpre, hcd, hnested, ⟨o, hor⟩, hsb, hnc⟩ :=
    h eps heps hle X hb hd
  exact terminal_limit_of_metric_compact_limit hPhi P hcanonical hcap hpre hcd hnested o hor
    hsb hnc hconn


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

def IsHalfLineExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  g 0 = L.space.metric ∧
    (∀ s ∈ J.carrier, g s = B.solution.base.metric s) ∧
    ∃ diagonal : ℕ → ℕ, ∃ hdiag : StrictMono diagonal,
      ConvergesOn (subsequenceMaps L.maps (B.subseq ∘ diagonal)
        (B.strictMono.comp hdiag))
        ({ base := { metric := g } } :
          SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)

def HalfLineExtensionExists {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g

def HalfLineExtensionIsFlow {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)

def HalfLineExtensionSliceGeometry {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    (∀ t ∈ ancientTimeInterval.carrier,
      MetricComplete ({ L.space with metric := g t } : PointedRiemannianManifold.{u, 0, 0} I3)) ∧
    ∀ t ∈ ancientTimeInterval.carrier, SecLower (g t) 0 Set.univ

def HalfLineExtensionCurvatureBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    ∃ C : ℝ, ∀ t ∈ ancientTimeInterval.carrier, ∀ x : L.space.M,
      FlowMetricBall.rmNormSq ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval) t x ≤ C

def HalfLineExtensionAncient {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g →
    ∃ hsol : IsSolutionOn ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval),
      IsAncientKappaSolution kappa (flowOfMetric ancientTimeInterval L.space g hsol)

theorem halfLineExtensionIsFlow_of_ancient {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J} (h : HalfLineExtensionAncient B) :
    HalfLineExtensionIsFlow B :=
  fun g hg => (h g hg).1

theorem pointedFlowScalarAtBase_flowOfMetric {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} (hg : g 0 = L.space.metric)
    (hsol : IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)) :
    PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval L.space g hsol) 1 := by
  change (flowOfMetric ancientTimeInterval L.space g hsol).S.scalar 0
    (flowOfMetric ancientTimeInterval L.space g hsol).basepoint = 1
  change metricScalarAt ((flowOfMetric ancientTimeInterval L.space g hsol).S.base.metric 0)
    (flowOfMetric ancientTimeInterval L.space g hsol).basepoint = 1
  rw [show (flowOfMetric ancientTimeInterval L.space g hsol).S.base.metric 0 = g 0 from rfl,
    show (flowOfMetric ancientTimeInterval L.space g hsol).basepoint = L.space.basepoint from rfl,
    hg]
  exact L.scalar_one


def HalfLineAnalyticInputs {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  HalfLineExtensionExists B ∧ HalfLineExtensionSliceGeometry B ∧
    HalfLineExtensionCurvatureBound B ∧ HalfLineExtensionAncient B

theorem ancientExtension_of_halfLine {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (h : HalfLineAnalyticInputs B) :
    Nonempty (AncientExtension B) := by
  obtain ⟨⟨g, hg0, hagree, diagonal, hdiag, hconv⟩, hgeom, hrm, hanc⟩ := h
  have hlim : IsHalfLineExtension B g := ⟨hg0, hagree, diagonal, hdiag, hconv⟩
  obtain ⟨hsol, hanc1⟩ := hanc g hlim
  have hanc2 : PointedFlowScalarAtBase
      (flowOfMetric ancientTimeInterval L.space g hsol) 1 :=
    pointedFlowScalarAtBase_flowOfMetric hlim.1 hsol
  obtain ⟨Cr, hCr⟩ := hrm g hlim
  refine ⟨{ extension :=
              { solution := ({ base := { metric := g } } :
                  SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)
                isSolution := hsol
                terminal := hg0
                subseq := B.subseq ∘ diagonal
                strictMono := B.strictMono.comp hdiag
                convergence := hconv
                complete := fun t ht => (hgeom g hlim).1 t ht
                nonnegative := fun t ht => (hgeom g hlim).2 t ht
                compact_time_bound := fun a b hab hsub =>
                  ⟨Cr, fun t ht x => hCr t (hsub ht) x⟩ }
            agrees := hagree
            diagonal := diagonal
            strictMono := hdiag
            maps_agree := rfl
            ancient := hanc1
            normalized := hanc2
            global_rm := ⟨Cr, fun t ht x => hCr t ht x⟩ }⟩

theorem ancient_extension_of_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
        HalfLineAnalyticInputs B) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B) := by
  obtain ⟨epsStar, hpos, hI⟩ := h
  exact ⟨epsStar, hpos, fun eps heps hle X L delta hd B =>
    ancientExtension_of_halfLine B (hI eps heps hle X L delta hd B)⟩

theorem ancient_extension {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
