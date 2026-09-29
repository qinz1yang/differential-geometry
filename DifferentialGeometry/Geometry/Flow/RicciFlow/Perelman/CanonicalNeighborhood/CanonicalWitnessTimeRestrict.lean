import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {D' : RealTimeInterval}

def StrongNeck.timeRestrict {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t)
    (hD : D.carrier ⊆ D'.carrier) : StrongNeck (S.timeRestrict D') eps x t where
  eps_pos := nk.eps_pos
  eps_small := nk.eps_small
  Q_pos := nk.Q_pos
  cylinder := nk.cylinder
  map := nk.map
  center := nk.center
  center_eq := nk.center_eq
  domain := nk.domain
  time_domain := nk.time_domain.trans hD
  comparison := nk.comparison

def LocalNeck.timeRestrict {eps : ℝ} {x : M} {t : ℝ} {U : Set M} (L : LocalNeck S eps x t U)
    (hD : D.carrier ⊆ D'.carrier) : LocalNeck (S.timeRestrict D') eps x t U where
  strong := L.strong.timeRestrict hD
  region_eq := L.region_eq
  boundary_eq := L.boundary_eq

def OrderedNeckChain.timeRestrict {eps t : ℝ} {V : Set M} (c : OrderedNeckChain S eps t V)
    (hD : D.carrier ⊆ D'.carrier) : OrderedNeckChain (S.timeRestrict D') eps t V where
  count := c.count
  count_pos := c.count_pos
  centers := c.centers
  necks := fun i => (c.necks i).timeRestrict hD
  lo := c.lo
  hi := c.hi
  lo_lt_hi := c.lo_lt_hi
  inside := c.inside
  swept_eq := c.swept_eq
  transition_increasing := c.transition_increasing

def LocalCap.timeRestrict {eps : ℝ} {x : M} {t : ℝ} {U : Set M} (C : LocalCap S eps x t U)
    (hD : D.carrier ⊆ D'.carrier) : LocalCap (S.timeRestrict D') eps x t U where
  core := C.core
  core_inside := C.core_inside
  center_inside := C.center_inside
  coreModel := C.coreModel
  tube := C.tube
  tubeMap := C.tubeMap
  tube_domain := C.tube_domain
  tube_eq := C.tube_eq
  union_eq := C.union_eq
  overlap_eq := C.overlap_eq
  inner_boundary := C.inner_boundary
  outer_boundary := C.outer_boundary
  boundary_eq := C.boundary_eq
  boundaries_disjoint := C.boundaries_disjoint
  chain := C.chain.timeRestrict hD
  coreBoundaryMap := C.coreBoundaryMap
  core_boundary_eq := C.core_boundary_eq

def RoundComponent.timeRestrict {eps : ℝ} {x : M} {t : ℝ} {U : Set M}
    (R : RoundComponent S eps x t U) (D' : RealTimeInterval) :
    RoundComponent (S.timeRestrict D') eps x t U := by
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  letI : ConnectedSpace R.Z := R.connected
  exact
    { Z := R.Z
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
      metric_bounds := R.metric_bounds }

def CanonicalAlternative.timeRestrict {eps C : ℝ} {x : M} {t : ℝ} {U : Set M}
    (A : CanonicalAlternative S eps C x t U) (hD : D.carrier ⊆ D'.carrier) :
    CanonicalAlternative (S.timeRestrict D') eps C x t U := by
  cases A with
  | neck data => exact .neck (data.timeRestrict hD)
  | cap data deep => exact .cap (data.timeRestrict hD) deep
  | positive whole data sec => exact .positive whole data sec
  | round whole data => exact .round whole (data.timeRestrict D')

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem CanonicalAlternative.timeRestrict_requiresVolume {eps C : ℝ} {x : M} {t : ℝ}
    {U : Set M} (A : CanonicalAlternative S eps C x t U) (hD : D.carrier ⊆ D'.carrier) :
    (A.timeRestrict hD).requiresVolume = A.requiresVolume := by
  cases A <;> rfl

def CanonicalWitness.timeRestrict {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) (hD : D.carrier ⊆ D'.carrier) :
    CanonicalWitness (S.timeRestrict D') eps C1 C2 x t where
  Q_pos := W.Q_pos
  time_mem := hD W.time_mem
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
  alternative := W.alternative.timeRestrict hD
  volume := by
    intro hv
    exact W.volume (by
      simpa only [CanonicalAlternative.timeRestrict_requiresVolume] using hv)
  gradient := W.gradient
  time_derivative := W.time_derivative

theorem CanonicalWitness.capTubeHasNeckChart.timeRestrict {eps C1 C2 alpha : ℝ} {x : M} {t : ℝ}
    {W : CanonicalWitness S eps C1 C2 x t} (h : W.capTubeHasNeckChart alpha)
    (hD : D.carrier ⊆ D'.carrier) : (W.timeRestrict hD).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change W.alternative.timeRestrict hD = CanonicalAlternative.cap cap depth at heq
  cases halt : W.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change CanonicalAlternative.cap (data.timeRestrict hD) deep =
      CanonicalAlternative.cap cap depth at heq
    cases heq
    obtain ⟨v, nk, hnk⟩ := h _ _ halt
    exact ⟨v, nk.timeRestrict hD, hnk⟩
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
