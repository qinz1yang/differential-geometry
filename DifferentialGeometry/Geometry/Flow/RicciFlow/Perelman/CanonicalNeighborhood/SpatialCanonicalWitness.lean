import DifferentialGeometry.Geometry.Neck.Spatial

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

structure SpatialOrderedNeckChain (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (V : Set M) where
  count : ℕ
  count_pos : 0 < count
  centers : Fin count → M
  necks : ∀ i, SpatialNeck g eps (centers i)
  lo : Fin count → ℝ
  hi : Fin count → ℝ
  lo_lt_hi : ∀ i, lo i < hi i
  inside : ∀ i, Set.univ ×ˢ Set.Icc (lo i) (hi i) ⊆ (necks i).map.source
  swept_eq : V = ⋃ i, (necks i).map '' (Set.univ ×ˢ Set.Icc (lo i) (hi i))
  transition_increasing : ∀ i j : Fin count, j.val = i.val + 1 →
    ∀ z ∈ (necks i).map.source, (necks i).map z ∈ (necks j).map.target →
      0 < fderiv ℝ (fun a : ℝ =>
        ((necks j).map.symm ((necks i).map (z.1, a))).2) z.2 1

structure SpatialLocalNeck (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M) (U : Set M) where
  neck : SpatialNeck g eps x
  region_eq : U = neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10)
  boundary_eq : frontier U = neck.map '' (Set.univ ×ˢ ({-10, 10} : Set ℝ))

structure SpatialLocalCap (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M) (U : Set M) where
  core : CompactDomain M
  core_inside : core.carrier ⊆ interior U
  center_inside : x ∈ interior core.carrier
  coreModel : CapCore core.carrier
  tube : Set M
  tubeMap : PartialDiffeomorph IC I3 Cylinder M ∞
  tube_domain : Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ⊆ tubeMap.source
  tube_eq : tubeMap '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) = tube
  union_eq : U = core.carrier ∪ tube
  overlap_eq : core.carrier ∩ tube = frontier core.carrier
  inner_boundary : tubeMap '' (Set.univ ×ˢ ({0} : Set ℝ)) = frontier core.carrier
  outer_boundary : tubeMap '' (Set.univ ×ˢ ({1} : Set ℝ)) = frontier U
  boundary_eq : frontier tube = frontier core.carrier ∪ frontier U
  boundaries_disjoint : Disjoint (frontier core.carrier) (frontier U)
  chain : SpatialOrderedNeckChain g eps tube
  coreBoundaryMap : Sphere 2 → M
  core_boundary_eq : ∀ z, coreBoundaryMap z = tubeMap (z, 0)

structure SpatialRoundComponent (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M)
    (U : Set M) where
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
  Q_pos : 0 < metricScalarAt g x
  comparison : MetricComparisonOn (fun _ => metric)
    (fun _ => scaleMetric (metricScalarAt g x) Q_pos g) map Set.univ {0} (⌈eps⁻¹⌉₊) eps
  metric_bounds : ∀ z (v : TangentSpace I3 z),
    (1 / 2 : ℝ) * metric.inner z v v ≤
      metricScalarAt g x * g.inner (map z) (mfderiv I3 I3 map z v) (mfderiv I3 I3 map z v) ∧
    metricScalarAt g x * g.inner (map z) (mfderiv I3 I3 map z v) (mfderiv I3 I3 map z v) ≤
      2 * metric.inner z v v

inductive SpatialCanonicalAlternative (g : SmoothRiemannianMetric I3 M) (eps C : ℝ) (x : M)
    (U : Set M) : Type (u + 1)
  | neck (data : SpatialLocalNeck g eps x U) : SpatialCanonicalAlternative g eps C x U
  | cap (data : SpatialLocalCap g eps x U)
      (deep : ∀ y ∈ data.tube,
        10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y) :
      SpatialCanonicalAlternative g eps C x U
  | positive (whole : U = connectedComponent x) (data : PositiveComponent U)
      (sec : SecLower g (C⁻¹ * metricScalarAt g x) U) :
      SpatialCanonicalAlternative g eps C x U
  | round (whole : U = connectedComponent x) (data : SpatialRoundComponent g eps x U) :
      SpatialCanonicalAlternative g eps C x U

def SpatialCanonicalAlternative.requiresVolume {g : SmoothRiemannianMetric I3 M}
    {eps C : ℝ} {x : M} {U : Set M} : SpatialCanonicalAlternative g eps C x U → Prop
  | .round _ _ => False
  | _ => True

structure SpatialCanonicalWitness (g : SmoothRiemannianMetric I3 M) (eps C1 C2 : ℝ) (x : M) where
  Q_pos : 0 < metricScalarAt g x
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  domain : CompactDomain M
  center_inside : x ∈ interior domain.carrier
  radius : ℝ
  radius_lower : (Real.sqrt (metricScalarAt g x))⁻¹ ≤ radius
  radius_upper : radius ≤ C1 / Real.sqrt (metricScalarAt g x)
  ball_inside : riemannianBallOf (I := I3) g x radius ⊆ domain.carrier
  inside_ball : domain.carrier ⊆ riemannianBallOf (I := I3) g x (2 * radius)
  scalar_bounds : ∀ y ∈ domain.carrier,
    C2⁻¹ * metricScalarAt g x ≤ metricScalarAt g y ∧
      metricScalarAt g y ≤ C2 * metricScalarAt g x
  rm_bound : ∀ y ∈ domain.carrier,
    Real.sqrt (normSq0S (I := I3) g y 4 (metricRm04 g y)) ≤ C2 * metricScalarAt g x
  alternative : SpatialCanonicalAlternative g eps C2 x domain.carrier
  volume : alternative.requiresVolume →
    ENNReal.ofReal (C2⁻¹ / (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 M g domain.carrier
  gradient : ∀ v : TangentSpace I3 x,
    |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
      C2 * metricScalarAt g x * Real.sqrt (metricScalarAt g x) * Real.sqrt (g.inner x v v)

def SpatialCanonicalWitness.capTubeHasNeckChart {g : SmoothRiemannianMetric I3 M}
    {eps C1 C2 : ℝ} {x : M} (K : SpatialCanonicalWitness g eps C1 C2 x) (alpha : ℝ) : Prop :=
  ∀ (cap : SpatialLocalCap g eps x K.domain.carrier)
    (depth : ∀ y ∈ cap.tube, 10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y),
    K.alternative = SpatialCanonicalAlternative.cap cap depth →
      ∃ (v : M) (nk : SpatialNeck g alpha v), ∀ z, cap.tubeMap z = nk.map z

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
