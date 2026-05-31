import RicciFlower.GlobalGeometry.Lecture07.FirstVariation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Parallel frames for Myers

This file proves the metric-preservation fact used by the Myers test-frame
argument: for a metric-compatible connection, the inner product of two
pullback-parallel fields along a curve is constant.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Lecture07
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- A field along a curve is pullback-parallel if its pullback covariant
derivative vanishes at every time. -/
def IsPBParallel
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (S : VectorFieldAlong I gamma) : Prop :=
  ∀ t : Real, HasPBCovAlongAt (I := I) cov gamma S t
    (0 : TangentSpace I (gamma t))

/-- Metric compatibility: the inner product of two pullback-parallel fields is
constant along the curve. -/
theorem inner_const_of_isPBParallel
    (g : SmoothRiemannianMetric I M)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {gamma : Curve M} {S T : VectorFieldAlong I gamma}
    (hS : IsPBParallel (I := I) cov gamma S)
    (hT : IsPBParallel (I := I) cov gamma T) (s t : Real) :
    g.inner (gamma t) (S t) (T t) = g.inner (gamma s) (S s) (T s) := by
  let φ : Real -> Real := fun r => g.inner (gamma r) (S r) (T r)
  have hφ : ∀ r : Real, HasDerivAt φ 0 r := by
    intro r
    have hprod :=
      Lecture07.inner_hasDerivAt_of_pbCov (I := I) g hmc
        (hS r) (hT r)
    simpa [φ] using hprod
  have hdiff : Differentiable Real φ := fun r => (hφ r).differentiableAt
  have hderiv : ∀ r : Real, deriv φ r = 0 := fun r => (hφ r).deriv
  simpa [φ] using is_const_of_deriv_eq_zero hdiff hderiv t s

/-- A pullback-parallel orthonormal frame perpendicular to the velocity. -/
structure IsPBParallelONFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gamma : Curve M) (frame : ι -> VectorFieldAlong I gamma) : Prop where
  parallel : ∀ i, IsPBParallel (I := I) cov gamma (frame i)
  velocity_parallel : ∀ t, HasPBCovAccelAt (I := I) cov gamma t 0
  ortho_at :
    ∀ i j, g.inner (gamma 0) (frame i 0) (frame j 0) =
      if i = j then 1 else 0
  perp_at :
    ∀ i, g.inner (gamma 0) (frame i 0)
      (velocityAlong I gamma 0) = 0

/-- Orthonormality holds at every time, not just `t = 0`. -/
theorem IsPBParallelONFrame.ortho
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {frame : ι -> VectorFieldAlong I gamma}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (hfr : IsPBParallelONFrame (I := I) g cov gamma frame)
    (t : Real) (i j : ι) :
    g.inner (gamma t) (frame i t) (frame j t) = if i = j then 1 else 0 := by
  have hconst :=
    inner_const_of_isPBParallel (I := I) g hmc
      (hfr.parallel i) (hfr.parallel j) 0 t
  simpa [hfr.ortho_at i j] using hconst

/-- Perpendicularity to the velocity holds at every time. -/
theorem IsPBParallelONFrame.perp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : SmoothRiemannianMetric I M}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {gamma : Curve M} {frame : ι -> VectorFieldAlong I gamma}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (hfr : IsPBParallelONFrame (I := I) g cov gamma frame)
    (t : Real) (i : ι) :
    g.inner (gamma t) (frame i t) (velocityAlong I gamma t) = 0 := by
  have hvel : IsPBParallel (I := I) cov gamma (velocityAlong I gamma) := by
    intro τ
    simpa [HasPBCovAccelAt] using hfr.velocity_parallel τ
  have hconst :=
    inner_const_of_isPBParallel (I := I) g hmc
      (hfr.parallel i) hvel 0 t
  simpa [velocityAlong] using hconst.trans (hfr.perp_at i)

/-- A rank-`n - 1` orthonormal frame perpendicular to velocity along `gamma`,
orthonormal and perpendicular at every time of `Icc 0 L`. -/
structure ParallelFrameData
    (g : SmoothRiemannianMetric I M) (gamma : Curve M) (n : Nat) (L : Real) where
  Eframe : Fin (n - 1) -> VectorFieldAlong I gamma
  hON : ∀ t, t ∈ Set.Icc (0 : Real) L -> ∀ i j,
    g.inner (gamma t) (Eframe i t) (Eframe j t) = if i = j then 1 else 0
  hperp : ∀ t, t ∈ Set.Icc (0 : Real) L -> ∀ i,
    g.inner (gamma t) (Eframe i t) (velocityAlong I gamma t) = 0

/-- **Parallel-transport / ON-complement frontier.**  For a supplied
metric-compatible connection `cov` and a supplied geodesic equation for `gamma`,
there is a pullback-parallel orthonormal frame of rank `n - 1` perpendicular to
the velocity.  The only remaining frontier is existence of the pullback-parallel
frame itself: solve the linear parallel-transport ODE from a chosen initial
orthonormal basis of the orthogonal complement of `velocityAlong I gamma 0`.
Metric compatibility and
the geodesic equation are inputs (`hmc`, `hgeo`), and the
`velocity_parallel` field is supplied by `hgeo`. -/
theorem exists_pbParallelONFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {gamma : Curve M} {n : Nat} {L : Real}
    (_hn : 1 < n)
    (_hdim : Module.finrank Real E = n)
    (_hsmooth : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (_hunit : ∀ t, t ∈ Set.Icc (0 : Real) L ->
      g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1)
    (hgeo : ∀ t, HasPBCovAccelAt (I := I) cov gamma t 0) :
    ∃ (frame : Fin (n - 1) -> VectorFieldAlong I gamma),
      IsPBParallelONFrame (I := I) g cov gamma frame := by
  sorry

/-- **P2 producer.**  Checked reduction of the parallel-frame frontier to
`ParallelFrameData`: orthonormality and perpendicularity hold at every time by
the metric-compatibility preservation lemmas. -/
theorem exists_parallel_on_frame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {gamma : Curve M} {n : Nat} {L : Real}
    (hn : 1 < n)
    (hdim : Module.finrank Real E = n)
    (hsmooth : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hunit : ∀ t, t ∈ Set.Icc (0 : Real) L ->
      g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1)
    (hgeo : ∀ t, HasPBCovAccelAt (I := I) cov gamma t 0) :
    Nonempty (ParallelFrameData (I := I) g gamma n L) := by
  obtain ⟨frame, hfr⟩ :=
    exists_pbParallelONFrame (I := I) g cov hmc hn hdim hsmooth hunit hgeo
  exact ⟨{
    Eframe := frame
    hON := fun t _ht i j => hfr.ortho hmc t i j
    hperp := fun t _ht i => hfr.perp hmc t i }⟩

end GlobalGeometry
end RicciFlower
