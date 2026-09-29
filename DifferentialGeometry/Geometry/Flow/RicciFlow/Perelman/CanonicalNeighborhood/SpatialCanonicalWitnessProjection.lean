import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ContDiff

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps C C1 C2 alpha t : ℝ} {x : M} {U : Set M}

def OrderedNeckChain.toSpatial (c : OrderedNeckChain S eps t U) :
    SpatialOrderedNeckChain (S.base.metric t) eps U where
  count := c.count
  count_pos := c.count_pos
  centers := c.centers
  necks i := (c.necks i).toSpatialNeck
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := c.inside
  swept_eq := c.swept_eq
  transition_increasing := c.transition_increasing

def LocalNeck.toSpatial (n : LocalNeck S eps x t U) :
    SpatialLocalNeck (S.base.metric t) eps x U where
  neck := n.strong.toSpatialNeck
  region_eq := n.region_eq
  boundary_eq := n.boundary_eq

def LocalCap.toSpatial (c : LocalCap S eps x t U) : SpatialLocalCap (S.base.metric t) eps x U where
  core := c.core
  core_inside := c.core_inside
  center_inside := c.center_inside
  coreModel := c.coreModel
  tube := c.tube
  tubeMap := c.tubeMap
  tube_domain := c.tube_domain
  tube_eq := c.tube_eq
  union_eq := c.union_eq
  overlap_eq := c.overlap_eq
  inner_boundary := c.inner_boundary
  outer_boundary := c.outer_boundary
  boundary_eq := c.boundary_eq
  boundaries_disjoint := c.boundaries_disjoint
  chain := c.chain.toSpatial
  coreBoundaryMap := c.coreBoundaryMap
  core_boundary_eq := c.core_boundary_eq

def RoundComponent.toSpatial (R : RoundComponent S eps x t U) :
    SpatialRoundComponent (S.base.metric t) eps x U where
  Z := R.Z
  topology := R.topology
  charted := R.charted
  smooth := R.smooth
  t2 := R.t2
  compact := R.compact
  connected := R.connected
  metric := R.metric
  p := R.p
  scalar_one := R.scalar_one
  constant_curvature := R.constant_curvature
  map := R.map
  source_eq := R.source_eq
  target_eq := R.target_eq
  center_eq := R.center_eq
  Q_pos := R.Q_pos
  comparison := R.comparison
  metric_bounds := R.metric_bounds

def CanonicalAlternative.toSpatial :
    CanonicalAlternative S eps C x t U → SpatialCanonicalAlternative (S.base.metric t) eps C x U
  | .neck data => .neck data.toSpatial
  | .cap data deep => .cap data.toSpatial deep
  | .positive whole data sec => .positive whole data sec
  | .round whole data => .round whole data.toSpatial

omit [T2Space M] [SigmaCompactSpace M] in
theorem CanonicalAlternative.requiresVolume_toSpatial (A : CanonicalAlternative S eps C x t U) :
    A.toSpatial.requiresVolume ↔ A.requiresVolume := by
  cases A <;> rfl

def CanonicalWitness.toSpatial (W : CanonicalWitness S eps C1 C2 x t) :
    SpatialCanonicalWitness (S.base.metric t) eps C1 C2 x where
  Q_pos := W.Q_pos
  eps_pos := W.eps_pos
  eps_lt_one := W.eps_lt_one
  domain := W.domain
  center_inside := W.center_inside
  radius := W.radius
  radius_lower := W.radius_lower
  radius_upper := W.radius_upper
  ball_inside := W.ball_inside
  inside_ball := W.inside_ball
  scalar_bounds := W.scalar_bounds
  rm_bound := W.rm_bound
  alternative := W.alternative.toSpatial
  volume h := W.volume (W.alternative.requiresVolume_toSpatial.mp h)
  gradient := W.gradient

theorem CanonicalWitness.capTubeHasNeckChart_toSpatial {W : CanonicalWitness S eps C1 C2 x t}
    (h : W.capTubeHasNeckChart alpha) : W.toSpatial.capTubeHasNeckChart alpha := by
  intro cap depth heq
  change W.alternative.toSpatial = SpatialCanonicalAlternative.cap cap depth at heq
  cases halt : W.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change SpatialCanonicalAlternative.cap data.toSpatial deep = _ at heq
    cases heq
    obtain ⟨v, nk, hnk⟩ := h data deep halt
    exact ⟨v, nk.toSpatialNeck, hnk⟩
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
