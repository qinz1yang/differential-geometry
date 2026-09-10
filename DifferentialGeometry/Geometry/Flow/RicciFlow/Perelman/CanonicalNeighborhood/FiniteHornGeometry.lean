import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredSourceInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.KernelSecondDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceForm

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

abbrev I3 := ThreeModel
abbrev I2 := 𝓡 2
abbrev Cylinder := Sphere 2 × ℝ
abbrev IC := I2.prod 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

def metricDistance (g : SmoothRiemannianMetric I3 M) (x y : M) : ℝ :=
  (riemannianEDistOf (I := I3) g x y).toReal

structure CompactDomain (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] where
  carrier : Set M
  compact : IsCompact carrier
  connected : IsConnected carrier
  regular_closed : closure (interior carrier) = carrier
  boundary_chart : ∀ x ∈ frontier carrier,
    ∃ F : PartialDiffeomorph I3 I3 M ThreeSpace ∞,
      x ∈ F.source ∧ (F x) 0 = 0 ∧
      ∀ y ∈ F.source, (y ∈ carrier ↔ (F y) 0 ≤ 0)

structure MetricComparisonOn
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [CompleteSpace E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    (h : ℝ → SmoothRiemannianMetric J N) (g : ℝ → SmoothRiemannianMetric I3 M)
    (F : N → M) (U : Set N) (times : Set ℝ) (order : ℕ) (eps : ℝ) where
  pullback : ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2
  pullback_eq : ∀ s y (v : Fin 2 → TangentSpace J y),
    pullback s y v = (g s).inner (F y)
      (mfderiv J I3 F y (v 0)) (mfderiv J I3 F y (v 1))
  jet : ℕ → ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2
  jet_zero : ∀ s y v,
    jet 0 s y v = pullback s y v - (h s).inner y (v 0) (v 1)
  jet_succ : ∀ b s, s ∈ times → ∀ y ∈ U, ∀ v,
    jet (b + 1) s y v = derivWithin (fun a => jet b a y v) times s
  equivalence : ∀ s ∈ times, ∀ y ∈ U, ∀ v : TangentSpace J y,
    (1 - eps) * (h s).inner y v v ≤ pullback s y (fun _ => v) ∧
      pullback s y (fun _ => v) ≤ (1 + eps) * (h s).inner y v v
  close : ∀ a b, a + 2 * b ≤ order → ∀ s ∈ times, ∀ y ∈ U,
    tensor02CovDerivNormWith (I := J) a (jet b s) (h s) (h s) y ≤ eps

structure WindowedModelWitness {D : RealTimeInterval}
    (eps kappa : ℝ) (S : SolutionOn (I := I3) (M := M) D) (x : M) (t : ℝ) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  time_mem : t ∈ D.carrier
  scalar_pos : 0 < S.scalar t x
  window_mem : Set.Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D.carrier
  model : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval
  model_ancient : IsAncientKappaSolution kappa model
  model_scalar_base : PointedFlowScalarAtBase model 1
  embedding :
    letI := model.topology
    letI := model.charted
    PartialDiffeomorph I3 I3 model.M M ∞
  buffered_ball :
    letI := model.topology
    letI := model.charted
    letI := model.smooth
    letI := model.t2
    letI := model.sigmaCompact
    riemannianClosedBallOf (I := I3) (model.S.base.metric 0)
      model.basepoint (modelRadius eps + 1) ⊆ embedding.source
  base_map : embedding model.basepoint = x
  comparison :
    letI := model.topology
    letI := model.charted
    letI := model.smooth
    letI := model.t2
    letI := model.sigmaCompact
    MetricComparisonOn (fun s => model.S.base.metric s)
      (rescaledMetric S t (S.scalar t x) scalar_pos) embedding
      (riemannianClosedBallOf (I := I3) (model.S.base.metric 0) model.basepoint (modelRadius eps))
      (Set.Icc (-modelDepth eps) 0) (modelOrder eps) eps
  source_capture : riemannianBallOf (I := I3)
    (rescaledMetric S t (S.scalar t x) scalar_pos 0) x (modelRadius eps - 1) ⊆
      embedding '' embedding.source

def OrientedWitness {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) (eps kappa : ℝ) (x : M) (t : ℝ) : Prop :=
  ∃ W : WindowedModelWitness eps kappa S x t,
    letI : TopologicalSpace W.model.M := W.model.topology
    letI : ChartedSpace ThreeSpace W.model.M := W.model.charted
    letI : IsManifold I3 ∞ W.model.M := W.model.smooth
    ∃ oN : TangentOrientationSection W.model.M,
      ∀ y ∈ W.embedding.source,
        ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
          PreservesTangentOrientationAt oN o W.embedding y hf

structure CylinderReference where
  metric : ℝ → SmoothRiemannianMetric IC Cylinder
  inner_eq : ∀ s ≤ 0, ∀ y : Cylinder, ∀ v w : TangentSpace IC y,
    (metric s).inner y v w =
      2 * (1 - s) * inner ℝ
        (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 v.1)
        (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 w.1) + v.2 * w.2


structure StrongNeck {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (eps : ℝ) (x : M) (t : ℝ) where
  eps_pos : 0 < eps
  eps_small : eps < 1 / 11
  Q_pos : 0 < S.scalar t x
  cylinder : CylinderReference
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  center : Sphere 2
  center_eq : map (center, 0) = x
  domain : Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ map.source
  time_domain : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier
  comparison : MetricComparisonOn cylinder.metric
    (rescaledMetric S t (S.scalar t x) Q_pos) map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0)
    (⌈eps⁻¹⌉₊) eps


structure LocalNeck {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (eps : ℝ) (x : M) (t : ℝ) (U : Set M) where
  strong : StrongNeck S eps x t
  region_eq : U = strong.map '' (Set.univ ×ˢ Set.Icc (-10) 10)
  boundary_eq : frontier U = strong.map '' (Set.univ ×ˢ ({-10, 10} : Set ℝ))

structure ProjectivePresentation
    (Z : Type*) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] where
  quotient : Sphere 3 → Z
  smooth : ContMDiff (𝓡 3) I3 ∞ quotient
  onto : Function.Surjective quotient
  fibers : ∀ a b : Sphere 3,
    quotient a = quotient b ↔ a = b ∨ (a : EuclideanSpace ℝ (Fin 4)) = -(b : EuclideanSpace ℝ (Fin 4))
  local_diffeo : ∀ a, Function.Bijective (mfderiv (𝓡 3) I3 quotient a)

inductive CapCore (X : Set M) : Type (u + 1)
  | ball (F : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
      (contains : Metric.closedBall (0 : ThreeSpace) 1 ⊆ F.source)
      (image_eq : F '' Metric.closedBall (0 : ThreeSpace) 1 = X) : CapCore X
  | projective (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
      [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
      (presentation : ProjectivePresentation Z)
      (ball : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
      (contains_ball : Metric.closedBall (0 : ThreeSpace) 2 ⊆ ball.source)
      (F : PartialDiffeomorph I3 I3 Z M ∞)
      (contains : (ball '' Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
      (image_eq : F '' (ball '' Metric.ball (0 : ThreeSpace) 1)ᶜ = X) : CapCore X

structure OrderedNeckChain {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (eps t : ℝ) (V : Set M) where
  count : ℕ
  count_pos : 0 < count
  centers : Fin count → M
  necks : ∀ i, StrongNeck S eps (centers i) t
  lo : Fin count → ℝ
  hi : Fin count → ℝ
  lo_lt_hi : ∀ i, lo i < hi i
  inside : ∀ i, Set.univ ×ˢ Set.Icc (lo i) (hi i) ⊆ (necks i).map.source
  swept_eq : V = ⋃ i, (necks i).map '' (Set.univ ×ˢ Set.Icc (lo i) (hi i))
  transition_increasing : ∀ i j : Fin count, j.val = i.val + 1 →
    ∀ z ∈ (necks i).map.source, (necks i).map z ∈ (necks j).map.target →
      0 < fderiv ℝ (fun a : ℝ =>
        ((necks j).map.symm ((necks i).map (z.1, a))).2) z.2 1


structure LocalCap {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (eps : ℝ) (x : M) (t : ℝ) (U : Set M) where
  core : CompactDomain M
  core_inside : core.carrier ⊆ interior U
  center_inside : x ∈ interior core.carrier
  core_model : CapCore core.carrier
  tube : Set M
  tube_map : PartialDiffeomorph IC I3 Cylinder M ∞
  tube_domain : Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ⊆ tube_map.source
  tube_eq : tube_map '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) = tube
  union_eq : U = core.carrier ∪ tube
  overlap_eq : core.carrier ∩ tube = frontier core.carrier
  inner_boundary : tube_map '' (Set.univ ×ˢ ({0} : Set ℝ)) = frontier core.carrier
  outer_boundary : tube_map '' (Set.univ ×ˢ ({1} : Set ℝ)) = frontier U
  boundary_eq : frontier tube = frontier core.carrier ∪ frontier U
  boundaries_disjoint : Disjoint (frontier core.carrier) (frontier U)
  chain : OrderedNeckChain S eps t tube
  core_boundary_map : Sphere 2 → M
  core_boundary_eq : ∀ z, core_boundary_map z = tube_map (z, 0)


def SecLower (g : SmoothRiemannianMetric I3 M) (c : ℝ) (U : Set M) : Prop :=
  ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
    c * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) ≤
      metricRm04At g x (fun i : Fin 4 => ![v, w, w, v] i)


inductive PositiveComponent (U : Set M) : Type (u + 1)
  | sphere (F : PartialDiffeomorph (𝓡 3) I3 (Sphere 3) M ∞)
      (source_eq : F.source = Set.univ) (target_eq : F.target = U) : PositiveComponent U
  | projective (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
      [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
      (presentation : ProjectivePresentation Z)
      (F : PartialDiffeomorph I3 I3 Z M ∞)
      (source_eq : F.source = Set.univ) (target_eq : F.target = U) : PositiveComponent U

structure RoundComponent {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (eps : ℝ) (x : M) (t : ℝ) (U : Set M) where
  Z : Type u
  [topology : TopologicalSpace Z]
  [charted : ChartedSpace ThreeSpace Z]
  [smooth : IsManifold I3 ∞ Z]
  [t2 : T2Space Z]
  [compact : CompactSpace Z]
  [connected : ConnectedSpace Z]
  metric : SmoothRiemannianMetric I3 Z
  p : Z
  scalar_one : ∀ z, metricScalarAt metric z = 1
  constant_curvature : ∀ z (v w : TangentSpace I3 z),
    metricRm04At metric z (fun i : Fin 4 => ![v, w, w, v] i) =
      (1 / 6 : ℝ) * (metric.inner z v v * metric.inner z w w - (metric.inner z v w) ^ 2)
  map : PartialDiffeomorph I3 I3 Z M ∞
  source_eq : map.source = Set.univ
  target_eq : map.target = U
  center_eq : map p = x
  Q_pos : 0 < S.scalar t x
  comparison : MetricComparisonOn (fun _ => metric)
    (fun _ => scaleMetric (S.scalar t x) Q_pos (S.base.metric t)) map Set.univ {0} (⌈eps⁻¹⌉₊) eps
  metric_bounds : ∀ z (v : TangentSpace I3 z),
    (1 / 2 : ℝ) * metric.inner z v v ≤
      S.scalar t x * (S.base.metric t).inner (map z)
        (mfderiv I3 I3 map z v) (mfderiv I3 I3 map z v) ∧
    S.scalar t x * (S.base.metric t).inner (map z)
        (mfderiv I3 I3 map z v) (mfderiv I3 I3 map z v) ≤ 2 * metric.inner z v v


inductive CanonicalAlternative {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (eps C : ℝ) (x : M) (t : ℝ) (U : Set M)
    : Type (u + 1)
  | neck (data : LocalNeck S eps x t U) : CanonicalAlternative S eps C x t U
  | cap (data : LocalCap S eps x t U)
      (deep : ∀ y ∈ data.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y) :
      CanonicalAlternative S eps C x t U
  | positive (whole : U = connectedComponent x) (data : PositiveComponent U)
      (sec : SecLower (S.base.metric t) (C⁻¹ * S.scalar t x) U) :
      CanonicalAlternative S eps C x t U
  | round (whole : U = connectedComponent x) (data : RoundComponent S eps x t U) :
      CanonicalAlternative S eps C x t U


def CanonicalAlternative.requiresVolume {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps C : ℝ} {x : M} {t : ℝ} {U : Set M} :
    CanonicalAlternative S eps C x t U → Prop
  | .round _ _ => False
  | _ => True

structure CanonicalWitness {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (eps C1 C2 : ℝ) (x : M) (t : ℝ) where
  Q_pos : 0 < S.scalar t x
  time_mem : t ∈ D.carrier
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  domain : CompactDomain M
  center_inside : x ∈ interior domain.carrier
  radius : ℝ
  radius_lower : (Real.sqrt (S.scalar t x))⁻¹ ≤ radius
  radius_upper : radius ≤ C1 / Real.sqrt (S.scalar t x)
  ball_inside : riemannianBallOf (I := I3) (S.base.metric t) x radius ⊆ domain.carrier
  inside_ball : domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x (2 * radius)
  scalar_bounds : ∀ y ∈ domain.carrier,
    C2⁻¹ * S.scalar t x ≤ S.scalar t y ∧ S.scalar t y ≤ C2 * S.scalar t x
  rm_bound : ∀ y ∈ domain.carrier,
    Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ C2 * S.scalar t x
  alternative : CanonicalAlternative S eps C2 x t domain.carrier
  volume : alternative.requiresVolume →
    ENNReal.ofReal (C2⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) domain.carrier
  gradient : ∀ v : TangentSpace I3 x,
    |scalarDifferential S t x v| ≤ C2 * S.scalar t x * Real.sqrt (S.scalar t x) *
      Real.sqrt ((S.base.metric t).inner x v v)
  time_derivative : |derivWithin (fun s => S.scalar s x) (Set.Iic t) t| ≤ C2 * S.scalar t x ^ 2

structure ConeChart (g : SmoothRiemannianMetric I3 M) (U : Set M) where
  surface : Type u
  [topology : TopologicalSpace surface]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface]
  [smooth : IsManifold I2 ∞ surface]
  [t2 : T2Space surface]
  [sigmaCompact : SigmaCompactSpace surface]
  metric : SmoothRiemannianMetric I2 surface
  map : PartialDiffeomorph (𝓘(ℝ, ℝ).prod I2) I3 (ℝ × surface) M ∞
  positive_radius : ∀ z ∈ map.source, 0 < z.1
  target_eq : map.target = U
  radial_metric : ∀ z ∈ map.source, ∀ v w : TangentSpace (𝓘(ℝ, ℝ).prod I2) z,
    g.inner (map z) (mfderiv (𝓘(ℝ, ℝ).prod I2) I3 map z v)
      (mfderiv (𝓘(ℝ, ℝ).prod I2) I3 map z w) =
        v.1 * w.1 + z.1 ^ 2 * metric.inner z.2 v.2 w.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
