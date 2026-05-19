/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.Scalar
import RicciFlower.MaximumPrinciple.ScalarWeak
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Curvature Lower Bound

This file records the native ODE-comparison layer for MSM110 Corollary 7.3.
The main comparison theorem consumes the parabolic scalar inequality
`(2 / n) R^2 <= (partial_t - Delta_g - X) R`, then applies the compact
value-set version of the scalar weak maximum principle.  The Ricci-flow
producer bridge is kept explicit: scalar evolution plus a heat-operator
realization and the trace/norm Cauchy-Schwarz inequality produce the parabolic
inequality.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## The scalar lower-bound ODE -/

/-- The explicit solution to `c' = (2 / n) c^2`, `c(0) = c0`. -/
def scalarLowerBarrier (n c0 : Real) (t : Real) : Real :=
  c0 / (1 - (2 / n) * c0 * t)

@[simp] theorem scalarLowerBarrier_zero (n c0 : Real) :
    scalarLowerBarrier n c0 0 = c0 := by
  simp [scalarLowerBarrier]

/-- The lower-bound reaction term `F(a,t) = (2 / n) a^2`. -/
def scalarLowerReaction (n : Real) (a _t : Real) : Real :=
  (2 / n) * a ^ 2

theorem scalarLowerReaction_apply (n a t : Real) :
    scalarLowerReaction n a t = (2 / n) * a ^ 2 := by
  rfl

/-- The barrier solves the ODE as a within-derivative, away from its pole. -/
theorem scalarLowerBarrier_hasDerivWithinAt
    (s : Set Real) (n c0 t : Real)
    (hn : n ≠ 0)
    (hden : 1 - (2 / n) * c0 * t ≠ 0) :
    HasDerivWithinAt
      (scalarLowerBarrier n c0)
      (scalarLowerReaction n (scalarLowerBarrier n c0 t) t)
      s t := by
  have hden' : 1 - ((2 / n) * c0) * t ≠ 0 := by
    simpa [mul_assoc] using hden
  have hnum : HasDerivAt (fun _ : Real => c0) 0 t := hasDerivAt_const t c0
  have hlin :
      HasDerivAt (fun y : Real => ((2 / n) * c0) * y) ((2 / n) * c0) t :=
    hasDerivAt_const_mul ((2 / n) * c0)
  have hdenDeriv :
      HasDerivAt
        (fun y : Real => 1 - ((2 / n) * c0) * y)
        (-((2 / n) * c0)) t := by
    simpa using hlin.const_sub 1
  have hquot :
      HasDerivAt
        (fun y : Real => c0 / (1 - ((2 / n) * c0) * y))
        ((0 * (1 - ((2 / n) * c0) * t) -
          c0 * (-((2 / n) * c0))) /
          (1 - ((2 / n) * c0) * t) ^ 2) t :=
    hnum.div hdenDeriv hden'
  have hwithin := hquot.hasDerivWithinAt (s := s)
  convert hwithin using 1
  rw [scalarLowerReaction]
  unfold scalarLowerBarrier
  field_simp [hden, hden', hn]
  ring_nf

theorem scalarLowerBarrier_derivWithin
    {T n c0 t : Real}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hn : n ≠ 0)
    (hden : 1 - (2 / n) * c0 * t ≠ 0) :
    derivWithin (scalarLowerBarrier n c0) (Set.Icc 0 T) t =
      scalarLowerReaction n (scalarLowerBarrier n c0 t) t :=
  (scalarLowerBarrier_hasDerivWithinAt
      (s := Set.Icc 0 T) n c0 t hn hden).derivWithin huniq

theorem scalarLowerReaction_locallyLipschitz (n t : Real) :
    LocallyLipschitz (fun a : Real => scalarLowerReaction n a t) := by
  have hcd : ContDiff Real 1 (fun a : Real => scalarLowerReaction n a t) := by
    unfold scalarLowerReaction
    fun_prop
  exact hcd.locallyLipschitz

/-- The square reaction has a uniform Lipschitz constant on the compact
spacetime value set used by the scalar WMP. -/
theorem exists_scalarLowerReaction_lipschitzOn_valueSet
    (n T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    (hcompact : IsCompact (Realized.scalarWMPValueSet (M := M) T u c)) :
    ∃ K : NNReal,
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
          (Realized.scalarWMPValueSet (M := M) T u c) := by
  have hloc :
      LocallyLipschitzOn (Realized.scalarWMPValueSet (M := M) T u c)
        (fun a : Real => scalarLowerReaction n a 0) :=
    (scalarLowerReaction_locallyLipschitz n 0).locallyLipschitzOn
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact hloc
  refine ⟨K, ?_⟩
  intro t _ht
  simpa [scalarLowerReaction] using hK

/-! ## Analytic comparison endpoint -/

/-- Corollary 7.3's ODE-comparison core.

This theorem deliberately consumes the parabolic scalar inequality directly.
The Ricci-flow production of that inequality is a separate bridge below, since
it depends on how the scalar Laplacian and the metric trace/norm inequality are
realized. -/
theorem scalar_curvature_lower_bound_of_parabolic_inequality
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (X : Real -> (x : M) -> TangentSpace I x)
    (scalar : Real -> M -> Real) (K : NNReal)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
      (Realized.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t y - scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalar t z - scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x)
    (hparabolic : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        Realized.parabolicOperatorWithDrift (I := I) G T X scalar t x)
    (hinit : ∀ x : M, c0 <= scalar 0 x)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x := by
  refine Realized.scalar_wmp_supersolutions_of_lipschitz_on_value_set_of_regular_positive_time
    (I := I) G T (le_of_lt hT) X scalar (scalarLowerBarrier n c0)
    (scalarLowerReaction n) K hw_cont hw_mdiff hw_grad hscalar_time ?_
    hscalar_space hdiff_space hdiff_grad hparabolic ?_ ?_ hF_lip
  · intro t ht
    exact (scalarLowerBarrier_hasDerivWithinAt
      (s := Set.Icc 0 T) n c0 t hn
      (ne_of_gt (hden t ht))).differentiableWithinAt
  · intro t ht
    exact scalarLowerBarrier_derivWithin
      (T := T) (n := n) (c0 := c0) (t := t)
      (uniqueDiffOn_Icc hT t ht) hn (ne_of_gt (hden t ht))
  · intro x
    simpa using hinit x

/-- Positivity consequence of the lower barrier. -/
theorem scalar_curvature_positive_of_lower_barrier
    {n c0 t Rtx : Real}
    (hbound : scalarLowerBarrier n c0 t <= Rtx)
    (hc0 : 0 < c0)
    (hden : 0 < 1 - (2 / n) * c0 * t) :
    0 < Rtx := by
  have hbar : 0 < scalarLowerBarrier n c0 t := by
    exact div_pos hc0 hden
  exact lt_of_lt_of_le hbar hbound

/-! ## Initial minimum wrappers -/

/-- Initial lower bound hypothesis used by the ODE comparison theorem. -/
def InitialScalarLowerBound (scalar : Real -> M -> Real) (c0 : Real) : Prop :=
  forall x : M, c0 <= scalar 0 x

/-- Book-facing minimum package for `c0 = min_M scalar(0, ·)`. -/
def InitialScalarMinimum (scalar : Real -> M -> Real) (c0 : Real) : Prop :=
  exists x0 : M, scalar 0 x0 = c0 /\ InitialScalarLowerBound (M := M) scalar c0

namespace InitialScalarMinimum

theorem lowerBound
    {scalar : Real -> M -> Real} {c0 : Real}
    (h : InitialScalarMinimum (M := M) scalar c0) :
    InitialScalarLowerBound (M := M) scalar c0 := by
  rcases h with ⟨_x0, _hc0, hbound⟩
  exact hbound

end InitialScalarMinimum

theorem initialScalarMinimum_of_isMinOn
    (scalar : Real -> M -> Real) {c0 : Real} {x0 : M}
    (hc0 : c0 = scalar 0 x0)
    (hmin : IsMinOn (fun x : M => scalar 0 x) Set.univ x0) :
    InitialScalarMinimum (M := M) scalar c0 := by
  refine ⟨x0, hc0.symm, ?_⟩
  intro x
  rw [hc0]
  exact hmin (by simp : x ∈ Set.univ)

theorem exists_initialScalarMinimum_of_continuous
    [CompactSpace M] [Nonempty M]
    (scalar : Real -> M -> Real)
    (hcont : Continuous (fun x : M => scalar 0 x)) :
    exists c0 : Real, InitialScalarMinimum (M := M) scalar c0 := by
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty hcont.continuousOn
  exact ⟨scalar 0 x0,
    initialScalarMinimum_of_isMinOn (M := M) scalar rfl hmin⟩

/-! ## WMP regularity package -/

/-- The analytic regularity hypotheses needed by the scalar WMP comparison
step for Corollary 7.3.

This is an honest producer interface: it only bundles the smoothness inputs
already consumed by the WMP theorem.  Producing this package from geometric
smoothness is a separate regularity frontier. -/
structure ScalarLowerBoundWMPRegularity
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (scalar : Real -> M -> Real) (K : NNReal) : Prop where
  weighted_cont : ContinuousOn
    (fun p : Real × M =>
      Real.exp (-(K : Real) * p.1) *
        (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
    (Realized.spacetimeSlab (M := M) T)
  weighted_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        Real.exp (-(K : Real) * t) *
          (scalar t y - scalarLowerBarrier n c0 t)) x
  weighted_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ x : M, MDiffAt (T% fun y : M =>
      Realized.gradientFun (I := I) (G.metric t)
        (fun z : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t z - scalarLowerBarrier n c0 t)) y) x
  scalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
    DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t
  scalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y
  diff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
      (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y
  diff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ x : M, MDiffAt (T% fun y : M =>
      Realized.gradientFun (I := I) (G.metric t)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x

/-! ## Ricci-flow producer bridge for the WMP hypothesis -/

/-- Closed-slab scalar evolution interface kept for compatibility.  The
book-facing Corollary 7.3 route uses `ScalarEvolutionEquationOn` on positive
regular times instead. -/
def ScalarEvolutionAllTimesOn
    (T : Real) (scalar scalarLap ricciNormSq : Real -> M -> Real) : Prop :=
  forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (scalarLap t x + 2 * ricciNormSq t x)
      (Set.Icc 0 T) t

/-- All-times scalar evolution plus the Ricci trace/norm lower bound produces
the parabolic inequality consumed by the comparison theorem.

This is intentionally stated with an all-times derivative hypothesis on
`[0,T]` and is retained as a compatibility wrapper.  It is not the preferred
book-facing Corollary 7.3 producer. -/
theorem scalar_parabolic_inequality_of_scalarEvolution_allTimes
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (hscalar : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      HasDerivWithinAt
        (fun s : Real => scalar s x)
        (scalarLap t x + 2 * ricciNormSq t x)
        (Set.Icc 0 T) t)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := by
  intro t ht x
  have hderiv :
      derivWithin (fun s : Real => scalar s x) (Set.Icc 0 T) t =
        scalarLap t x + 2 * ricciNormSq t x :=
    (hscalar t ht x).derivWithin (uniqueDiffOn_Icc hT t ht)
  have hparabolic :
      Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x =
        2 * ricciNormSq t x := by
    have hlap_zero :=
      ScalarLaplacianRealizesHeatOperatorOn.zero_drift
        (I := I) (G := G) (T := T) (scalar := scalar)
        (scalarLap := scalarLap) hlap t ht x
    rw [Realized.parabolicOperatorWithDrift_eq, hderiv, hlap_zero]
    ring
  have hscale :
      2 * ((1 / n) * (scalar t x) ^ 2) <= 2 * ricciNormSq t x :=
    mul_le_mul_of_nonneg_left (hricci t ht x) (by norm_num)
  calc
    scalarLowerReaction n (scalar t x) t =
        2 * ((1 / n) * (scalar t x) ^ 2) := by
          rw [scalarLowerReaction]
          ring
    _ <= 2 * ricciNormSq t x := hscale
    _ = Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := hparabolic.symm

/-- Regular-time scalar evolution plus the Ricci trace/norm lower bound
produces the positive-time parabolic inequality consumed by Corollary 7.3.

The interval hypothesis says that the closed test slab `[0,T]` lies in the
solution carrier, and every positive time in that slab is a regular time of
the solution.  For a solution on `[0,omega)`, this is the usual `T < omega`
restriction. -/
theorem scalar_parabolic_inequality_of_scalarEvolution_regularTime
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hscalar : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := by
  intro t ht htpos x
  let τ : Realized.RealTimeInterval.RegularTime D :=
    ⟨t, hregular t ht htpos⟩
  have hwithin :
      HasDerivWithinAt
        (fun s : Real => scalar s x)
        (scalarLap t x + 2 * ricciNormSq t x)
        (Set.Icc 0 T) t := by
    simpa [τ] using (hscalar τ x).mono hslab
  have hderiv :
      derivWithin (fun s : Real => scalar s x) (Set.Icc 0 T) t =
        scalarLap t x + 2 * ricciNormSq t x :=
    hwithin.derivWithin (uniqueDiffOn_Icc hT t ht)
  have hparabolic :
      Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x =
        2 * ricciNormSq t x := by
    have hlap_zero :=
      ScalarLaplacianRealizesHeatOperatorOn.zero_drift
        (I := I) (G := G) (T := T) (scalar := scalar)
        (scalarLap := scalarLap) hlap t ht x
    rw [Realized.parabolicOperatorWithDrift_eq, hderiv, hlap_zero]
    ring
  have hscale :
      2 * ((1 / n) * (scalar t x) ^ 2) <= 2 * ricciNormSq t x :=
    mul_le_mul_of_nonneg_left (hricci t ht x) (by norm_num)
  calc
    scalarLowerReaction n (scalar t x) t =
        2 * ((1 / n) * (scalar t x) ^ 2) := by
          rw [scalarLowerReaction]
          ring
    _ <= 2 * ricciNormSq t x := hscale
    _ = Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := hparabolic.symm

theorem scalar_parabolic_inequality_of_scalarEvolutionAllTimes
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (hscalar : ScalarEvolutionAllTimesOn (M := M) T scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x :=
  scalar_parabolic_inequality_of_scalarEvolution_allTimes
    (I := I) G T n hT scalar scalarLap ricciNormSq
    hscalar hlap hricci

/-- In-frame geometric producer for the WMP parabolic inequality.  The raw
trace/norm Cauchy-Schwarz hypothesis is produced from the inverse-metric frame
data. -/
theorem scalar_parabolic_inequality_of_scalarEvolutionAllTimes_inFrame
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hn : n = (Fintype.card Idx : Real))
    (hscalar : ScalarEvolutionAllTimesOn (M := M) T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerReaction n (scalarTraceInFrame (I := I) S gInv frame t x) t <=
        Realized.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x))
          (scalarTraceInFrame (I := I) S gInv frame) t x := by
  have hricci :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
          ricciNormSqInFrame (I := I) S gInv frame t x := by
    have hcs :=
      RicciTraceNormCauchySchwarzInFrame.of_metric_inverse_frame
        (I := I) S gInv frame hframe hcover hinv n hn
    intro t _ht x
    exact hcs t x
  exact scalar_parabolic_inequality_of_scalarEvolutionAllTimes
    (I := I) G T n hT
    (scalarTraceInFrame (I := I) S gInv frame)
    (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
    (ricciNormSqInFrame (I := I) S gInv frame)
    hscalar hlap hricci

/-- Corollary 7.3 assembly theorem from regular-time scalar evolution. -/
theorem scalar_curvature_lower_bound_of_scalarEvolution
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
      (Realized.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t y - scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalar t z - scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x := by
  have hparabolic :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
        scalarLowerReaction n (scalar t x) t <=
          Realized.parabolicOperatorWithDrift (I := I) G T
            (fun _t x => (0 : TangentSpace I x)) scalar t x :=
    scalar_parabolic_inequality_of_scalarEvolution_regularTime
      (I := I) (D := D) G T n hT scalar scalarLap ricciNormSq
      hslab hregular hevol hlap hricci
  exact scalar_curvature_lower_bound_of_parabolic_inequality
    (I := I) G T n c0 hT hn
    (fun _t x => (0 : TangentSpace I x)) scalar K hden
    hw_cont hw_mdiff hw_grad hscalar_time hscalar_space hdiff_space
    hdiff_grad hparabolic hinit hF_lip

/-- Corollary 7.3 assembly theorem using the named WMP regularity package. -/
theorem scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hreg : ScalarLowerBoundWMPRegularity (I := I) G T n c0 scalar K)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x :=
  scalar_curvature_lower_bound_of_scalarEvolution
    (I := I) (D := D) G T n c0 hT hn scalar scalarLap ricciNormSq K
    hslab hregular hden
    hreg.weighted_cont hreg.weighted_mdiff hreg.weighted_grad
    hreg.scalar_time hreg.scalar_space hreg.diff_space hreg.diff_grad
    hevol hlap hricci hinit hF_lip

/-- Closed-open interval convenience wrapper for Corollary 7.3.

For a solution defined on `[0, omega)`, a finite comparison slab with
`T < omega` lies in the carrier and has positive times in the regular set. -/
theorem scalar_curvature_lower_bound_of_scalarEvolution_closedOpen
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T) (hTω : T < omega)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hreg : ScalarLowerBoundWMPRegularity (I := I) G T n c0 scalar K)
    (hevol : ScalarEvolutionEquationOn
      (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
      scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x := by
  have hslab :
      Set.Icc 0 T ⊆
        (Realized.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    intro t ht
    change t ∈ Set.Ico 0 omega
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hregular :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
        t ∈ (Realized.RealTimeInterval.closedOpen 0 omega h0ω).regular := by
    intro t ht htpos
    change t ∈ Set.Ioo 0 omega
    exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
  exact scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := I) (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    G T n c0 hT hn scalar scalarLap ricciNormSq K
    hslab hregular hden hreg hevol hlap hricci hinit hF_lip

/-- Book-facing variant of the scalar lower-bound theorem using a realized
initial minimum instead of a raw lower-bound hypothesis. -/
theorem scalar_curvature_lower_bound_of_scalarEvolution_initialMinimum
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
      (Realized.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t y - scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalar t z - scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarMinimum (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x :=
  scalar_curvature_lower_bound_of_scalarEvolution
    (I := I) (D := D) G T n c0 hT hn scalar scalarLap ricciNormSq K
    hslab hregular hden
    hw_cont hw_mdiff hw_grad hscalar_time hscalar_space hdiff_space
    hdiff_grad hevol hlap hricci
    (InitialScalarMinimum.lowerBound (M := M) hinit) hF_lip

/-- Book-facing in-frame variant of the scalar lower-bound theorem.  The
trace/norm inequality is supplied by the frame inverse-metric producer rather
than exposed as a raw hypothesis. -/
theorem scalar_curvature_lower_bound_of_scalarEvolution_inFrame
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn_ne : n ≠ 0)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hn_rank : n = (Fintype.card Idx : Real))
    (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalarTraceInFrame (I := I) S gInv frame p.1 p.2 -
            scalarLowerBarrier n c0 p.1))
      (Realized.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalarTraceInFrame (I := I) S gInv frame t y -
              scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalarTraceInFrame (I := I) S gInv frame t z -
                scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real
        (fun s : Real => scalarTraceInFrame (I := I) S gInv frame s x)
        (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (scalarTraceInFrame (I := I) S gInv frame t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M =>
          scalarTraceInFrame (I := I) S gInv frame t z -
            scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            scalarTraceInFrame (I := I) S gInv frame t z -
              scalarLowerBarrier n c0 t) y) x)
    (hevol : ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic))
    (hinit : InitialScalarLowerBound (M := M)
      (scalarTraceInFrame (I := I) S gInv frame) c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T
          (scalarTraceInFrame (I := I) S gInv frame)
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <=
        scalarTraceInFrame (I := I) S gInv frame t x := by
  have hricci :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
          ricciNormSqInFrame (I := I) S gInv frame t x := by
    have hcs :=
      RicciTraceNormCauchySchwarzInFrame.of_metric_inverse_frame
        (I := I) S gInv frame hframe hcover hinv n hn_rank
    intro t _ht x
    exact hcs t x
  exact scalar_curvature_lower_bound_of_scalarEvolution
    (I := I) (D := D) G T n c0 hT hn_ne
    (scalarTraceInFrame (I := I) S gInv frame)
    (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
    (ricciNormSqInFrame (I := I) S gInv frame) K hslab hregular hden
    hw_cont hw_mdiff hw_grad hscalar_time hscalar_space hdiff_space
    hdiff_grad hevol hlap hricci hinit hF_lip

/-- Closed-open in-frame variant of the scalar lower-bound theorem.  This is
the finite-slab wrapper for a solution defined on `[0, omega)`. -/
theorem scalar_curvature_lower_bound_of_scalarEvolution_inFrame_closedOpen
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {omega : Real} (h0ω : 0 < omega)
    {u : Set M}
    (S : SolutionOn (I := I) (M := M)
      (Realized.RealTimeInterval.closedOpen 0 omega h0ω))
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T) (hTω : T < omega)
    (hn_ne : n ≠ 0)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hn_rank : n = (Fintype.card Idx : Real))
    (K : NNReal)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hreg : ScalarLowerBoundWMPRegularity (I := I) G T n c0
      (scalarTraceInFrame (I := I) S gInv frame) K)
    (hevol : ScalarEvolutionEquationOn
      (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic))
    (hinit : InitialScalarLowerBound (M := M)
      (scalarTraceInFrame (I := I) S gInv frame) c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (Realized.scalarWMPValueSet (M := M) T
          (scalarTraceInFrame (I := I) S gInv frame)
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <=
        scalarTraceInFrame (I := I) S gInv frame t x := by
  have hslab :
      Set.Icc 0 T ⊆
        (Realized.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    intro t ht
    change t ∈ Set.Ico 0 omega
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hregular :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
        t ∈ (Realized.RealTimeInterval.closedOpen 0 omega h0ω).regular := by
    intro t ht htpos
    change t ∈ Set.Ioo 0 omega
    exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
  have hricci :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
          ricciNormSqInFrame (I := I) S gInv frame t x := by
    have hcs :=
      RicciTraceNormCauchySchwarzInFrame.of_metric_inverse_frame
        (I := I) S gInv frame hframe hcover hinv n hn_rank
    intro t _ht x
    exact hcs t x
  exact scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := I) (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    G T n c0 hT hn_ne
    (scalarTraceInFrame (I := I) S gInv frame)
    (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
    (ricciNormSqInFrame (I := I) S gInv frame) K
    hslab hregular hden hreg hevol hlap hricci hinit hF_lip

end RicciFlow
end RicciFlower
