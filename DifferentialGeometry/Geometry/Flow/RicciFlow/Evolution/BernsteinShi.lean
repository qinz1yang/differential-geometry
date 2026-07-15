import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ScalarLowerBound

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bernstein–Bando–Shi First Derivative Estimate (parametric core)

This file formalizes the `m = 1` case of the global Bernstein–Bando–Shi
derivative estimate (MSM144 Theorem 14.5) on a closed manifold, following the
maximum-principle proof of Section 2.1.  The geometric production of the two
curvature-norm heat inequalities is deliberately kept as a separate frontier:
here the curvature norm `|Rm|^2` and the gradient norm `|nabla Rm|^2` are given
scalar fields, and the two heat inequalities are taken as hypotheses.

The mathematics is the standard one.  Writing `u = |nabla Rm|^2`,
`v = |Rm|^2`, one has on `M x [0,T]`:

* `(partial_t - Delta) u <= C(n) |Rm| u`  (eq 14.17, dropping `-2|nabla^2 Rm|^2`);
* `(partial_t - Delta) v = -2 u + reaction`, with `|reaction| <= 16 |Rm|^3`
  (eq 14.16).

With `v <= K^2` and `t <= alpha / K`, set `F = t u + beta v` with
`beta = 1 + C(n) alpha`.  Then `(partial_t - Delta) F <= C(n) beta K^3` because the
`u`-terms cancel, and the upper-bound maximum principle gives
`F <= beta K^2 (1 + C(n) alpha) = C(n, alpha) K^2`, hence `u <= C(n, alpha) K^2 / t`.

## Main results

* `scalar_subsolution_affine_bound` — Part A, the upper-bound scalar maximum
  principle: a closed-manifold subsolution `(partial_t - Delta) F <= b` with
  `F(0, .) <= a` satisfies `F(t, x) <= a + b t`.
* `NablaRm04NormHeatBoundOn` — the `|nabla Rm|^2` heat-inequality predicate.
* `bernstein_first_derivative_estimate` — Part B, the parametric Bernstein
  lemma: under the two heat inequalities and `|Rm| <= K`, `t <= alpha / K`,
  one gets `u(t, x) <= C(n, alpha) K^2 / t` for `t in (0, T]`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## Part A — affine-barrier upper-bound scalar maximum principle -/

/-- Operator linearity for the affine barrier `(a + b t) - F`.

This generalizes `parabolic_const_sub` to a spatially-constant additive term
that is affine in time.  The proof differentiates the affine time term and uses
that the spatial heat operator is insensitive to spatially-constant shifts and
scales by `-1`. -/
theorem parabolicOperatorWithDrift_affine_sub
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (F : Real -> M -> Real) (a b t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hF_time : DifferentiableWithinAt Real
      (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (F t) y)
    (hF_grad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) x) :
    DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X
        (fun s y => (a + b * s) - F s y) t x =
      b - DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X F t x := by
  unfold DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift
  -- time derivative of the affine barrier
  have hbarrier_const : DifferentiableWithinAt Real
      (fun s : Real => a + b * s) (Set.Icc 0 T) t := by
    have hlin : DifferentiableWithinAt Real (fun s : Real => b * s) (Set.Icc 0 T) t := by
      simpa using
        (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul b
    exact (differentiableWithinAt_const a).add hlin
  have hbarrier_deriv :
      derivWithin (fun s : Real => a + b * s) (Set.Icc 0 T) t = b := by
    have hlin : DifferentiableWithinAt Real (fun s : Real => b * s) (Set.Icc 0 T) t := by
      simpa using
        (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul b
    rw [derivWithin_fun_add (differentiableWithinAt_const a) hlin]
    have hconst_deriv :
        derivWithin (fun _s : Real => a) (Set.Icc 0 T) t = 0 :=
      (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T) (c := a)).derivWithin huniq
    have hlin_deriv :
        derivWithin (fun s : Real => b * s) (Set.Icc 0 T) t = b := by
      rw [derivWithin_const_mul b
        (d := fun s : Real => s) (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
      rw [derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t) huniq]
      ring
    rw [hconst_deriv, hlin_deriv]
    ring
  have htime :
      derivWithin (fun s : Real => (a + b * s) - F s x) (Set.Icc 0 T) t =
        b - derivWithin (fun s : Real => F s x) (Set.Icc 0 T) t := by
    rw [derivWithin_fun_sub hbarrier_const hF_time, hbarrier_deriv]
  -- the spatial subtracted function and its gradient regularity
  have hsub_grad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
        (fun z : M => F t z - (a + b * t)) y) x := by
    have hplain :
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => F t z - (a + b * t)) y) =
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) := by
      funext y
      calc
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => F t z - (a + b * t)) y =
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y -
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
              (fun _ : M => (a + b * t)) y := by
            exact DifferentialGeometry.Integral.Connection.gradientFun_sub (I := I) (G.metric t)
              (hF_space y) mdifferentiableAt_const
        _ = DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y := by
            rw [DifferentialGeometry.Integral.Connection.gradientFun_const]
            simp
    have hsection :
        (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => F t z - (a + b * t)) y) =
        (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) := by
      funext y
      simpa using congrFun hplain y
    rw [hsection]
    exact hF_grad
  have hsub_space : forall y : M,
      MDifferentiableAt I 𝓘(Real, Real) (fun z : M => F t z - (a + b * t)) y := by
    intro y
    exact (hF_space y).sub mdifferentiableAt_const
  -- heat operator: insensitive to constant shift, scales by -1
  have hheat_sub :
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => F t y - (a + b * t)) x =
        DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t (X t) (F t) x :=
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_sub_const (I := I) G t (X t)
      (a + b * t) hF_space x
  have hheat_scale :
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t (X t)
          ((-1 : Real) • fun y : M => F t y - (a + b * t)) x =
        (-1 : Real) *
          DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t (X t)
            (fun y : M => F t y - (a + b * t)) x :=
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_const_smul (I := I) G t (X t) (-1)
      (f := fun y : M => F t y - (a + b * t)) hsub_space hsub_grad
  have hheat :
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => (a + b * t) - F t y) x =
        - DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t (X t) (F t) x := by
    have hfun :
        (fun y : M => (a + b * t) - F t y) =
          ((-1 : Real) • fun y : M => F t y - (a + b * t)) := by
      funext y
      simp
    rw [hfun, hheat_scale, hheat_sub]
    ring
  rw [htime, hheat]
  ring

/-- The realized Laplacian is linear over the affine combination
`c1 f + c2 g`. -/
theorem laplacianAt_linear_combo
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) (f g : M -> Real) (c1 c2 : Real) (x : M)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hg : forall y : M, MDifferentiableAt I 𝓘(Real, Real) g y)
    (hgradf : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y) x)
    (hgradg : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) g y) x) :
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
        (fun z : M => c1 * f z + c2 * g z) x =
      c1 * DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t f x +
        c2 * DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t g x := by
  -- gradient of the combination is `c1 • grad f + c2 • grad g`
  have hgrad_eq :
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M => c1 * f z + c2 * g z) =
        (c1 • fun y : M =>
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y) +
          (c2 • fun y : M =>
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) g y) := by
    funext y
    have hc1 : MDifferentiableAt I 𝓘(Real, Real) (fun z : M => c1 * f z) y := by
      simpa using (hf y).const_smul c1
    have hc2 : MDifferentiableAt I 𝓘(Real, Real) (fun z : M => c2 * g z) y := by
      simpa using (hg y).const_smul c2
    calc
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M => c1 * f z + c2 * g z) y =
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => c1 * f z) y +
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => c2 * g z) y := by
          exact DifferentialGeometry.Integral.Connection.gradientFun_add (I := I) (G.metric t) hc1 hc2
      _ = c1 • DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y +
            c2 • DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) g y := by
          rw [show (fun z : M => c1 * f z) = (c1 • f) by funext z; simp [smul_eq_mul]]
          rw [show (fun z : M => c2 * g z) = (c2 • g) by funext z; simp [smul_eq_mul]]
          rw [DifferentialGeometry.Integral.Connection.gradientFun_const_smul (I := I) (G.metric t) c1 (hf y)]
          rw [DifferentialGeometry.Integral.Connection.gradientFun_const_smul (I := I) (G.metric t) c2 (hg y)]
      _ = (c1 • fun y : M =>
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y) y +
            (c2 • fun y : M =>
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) g y) y := by
          rfl
  rw [DifferentialGeometry.Integral.Connection.laplacianAt_eq,
    DifferentialGeometry.Integral.Connection.laplacianAt_eq,
    DifferentialGeometry.Integral.Connection.laplacianAt_eq]
  unfold DifferentialGeometry.Integral.Connection.laplacian
  rw [hgrad_eq]
  rw [DifferentialGeometry.Integral.Connection.divergence_add (I := I) (G.connection t)
      (hgradf.smul_const_section (a := c1)) (hgradg.smul_const_section (a := c2))]
  rw [DifferentialGeometry.Integral.Connection.divergence_const_smul (I := I) (G.connection t) c1 hgradf]
  rw [DifferentialGeometry.Integral.Connection.divergence_const_smul (I := I) (G.connection t) c2 hgradg]

/-- The zero-drift heat operator of `c1 f + c2 g` splits linearly. -/
theorem heatOperator_linear_combo
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) (f g : M -> Real) (c1 c2 : Real) (x : M)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hg : forall y : M, MDifferentiableAt I 𝓘(Real, Real) g y)
    (hgradf : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y) x)
    (hgradg : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) g y) x) :
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (fun z : M => c1 * f z + c2 * g z) x =
      c1 * DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
          (fun _y : M => (0 : TangentSpace I _y)) f x +
        c2 * DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
          (fun _y : M => (0 : TangentSpace I _y)) g x := by
  rw [DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift,
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift,
    DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift]
  rw [DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt,
    DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt,
    DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt]
  exact laplacianAt_linear_combo (I := I) G t f g c1 c2 x hf hg hgradf hgradg

/-- **Part A.** Upper-bound scalar maximum principle for affine barriers.

On a closed manifold, a scalar subsolution `(partial_t - Delta_{g(t)}) F <= b`
(with constant `b`) on the positive times of `[0,T]`, with `F(0, .) <= a`,
satisfies `F(t, x) <= a + b t` on the whole slab.

The proof applies the existing strict-barrier nonnegativity theorem to the
affine barrier `w = (a + b t) - F` and uses
`parabolicOperatorWithDrift_affine_sub` for the operator linearity.  The
subsolution inequality is only needed at positive times, mirroring
`scalar_sub_const_posReg`. -/
theorem scalar_subsolution_affine_bound
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (F : Real -> M -> Real) (a b : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => (a + b * p.1) - F p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hF_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (F t) y)
    (hF_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) x)
    (hinit : forall x : M, F 0 x <= a)
    (hsub : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X F t x <= b) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, F t x <= a + b * t := by
  let w : Real -> M -> Real := fun t x => (a + b * t) - F t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have : F 0 x <= a := hinit x
    simp only [w]
    nlinarith [this]
  have hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    have hbarrier : DifferentiableWithinAt Real
        (fun s : Real => a + b * s) (Set.Icc 0 T) t := by
      have hlin : DifferentiableWithinAt Real (fun s : Real => b * s) (Set.Icc 0 T) t := by
        simpa using
          (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul b
      exact (differentiableWithinAt_const a).add hlin
    exact hbarrier.sub (hF_time t ht htpos x)
  have hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x
    have : MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (a + b * t) - F t y) x :=
      mdifferentiableAt_const.sub (hF_space t ht htpos x)
    simpa [w] using this
  have hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    -- gradient of `(a + b t) - F t = (-1) • (F t - (a + b t))`, same as gradient of `F t`
    have hplain :
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w t) y) =
        (fun y : M =>
          - DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) := by
      funext y
      have hwt : w t = (fun z : M => (a + b * t) - F t z) := rfl
      rw [hwt]
      calc
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
            (fun z : M => (a + b * t) - F t z) y =
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
              (fun _ : M => (a + b * t)) y -
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y := by
            exact DifferentialGeometry.Integral.Connection.gradientFun_sub (I := I) (G.metric t)
              mdifferentiableAt_const (hF_space t ht htpos y)
        _ = - DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y := by
            rw [DifferentialGeometry.Integral.Connection.gradientFun_const]
            simp
    have hsection :
        (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w t) y) =
        (T% fun y : M =>
          - DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) := by
      funext y
      simpa using congrFun hplain y
    rw [hsection]
    -- `- grad = (-1) • grad`; differentiability of the negated section
    have hneg :
        (T% fun y : M =>
          - DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y) =
        (T% ((-1 : Real) • fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (F t) y)) := by
      funext y
      simp
    rw [hneg]
    exact (hF_grad t ht htpos x).smul_const_section (a := (-1 : Real))
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x _hwneg
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc (lt_of_lt_of_le htpos ht.2)).uniqueDiffWithinAt ht
    have hident :
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X w t x =
          b - DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X F t x := by
      simpa [w] using
        parabolicOperatorWithDrift_affine_sub (I := I) G T X F a b t x huniq
          (hF_time t ht htpos x) (hF_space t ht htpos) (hF_grad t ht htpos x)
    rw [hident]
    have := hsub t ht htpos x
    linarith
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    DifferentialGeometry.Integral.Connection.strict_barrier_posReg (I := I) G T hT X w
      hw_cont hw0 hw_time hw_mdiff hw_grad hnegative
  intro t ht x
  have := hw_nonneg t ht x
  simp only [w] at this
  linarith

/-! ## Part B — the parametric Bernstein lemma -/

/-- Heat-inequality predicate for `|nabla Rm|^2`, mirroring
`Rm04NormHeatEquationOn`.

This states the differential inequality `(partial_t - Delta) u <= cReact * v^{1/2} * u`
in `HasDerivWithinAt` form: the time derivative of `u` is bounded above by
`uLap + cReact * sqrt v * u`, where `uLap` realizes `Delta u`.  This is eq 14.17
with the favourable `-2|nabla^2 Rm|^2` term dropped; the reaction coefficient
`cReact` packages the dimensional constant `C(n)`. -/
def NablaRm04NormHeatBoundOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (nablaRmNormSq nablaRmNormLap rmNormSq : Real -> M -> Real) (cReact : Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    ∃ d : Real,
      HasDerivWithinAt
        (fun s : Real => nablaRmNormSq s x)
        d
        D.carrier
        (t : Real) ∧
      d <= nablaRmNormLap (t : Real) x +
        cReact * Real.sqrt (rmNormSq (t : Real) x) * nablaRmNormSq (t : Real) x

/-- The explicit constant `C(n, alpha) = (1 + cReact * alpha) * (1 + 16 * alpha)`
appearing in the first-derivative estimate.  It is `beta * (1 + 16 alpha)` with
`beta = 1 + cReact * alpha`. -/
def bernsteinConstant (cReact alpha : Real) : Real :=
  (1 + cReact * alpha) * (1 + 16 * alpha)

/-- **Part B.** Parametric Bernstein–Bando–Shi first derivative estimate.

Given the gradient norm `u = |nabla Rm|^2 >= 0`, the curvature norm
`v = |Rm|^2 >= 0`, the two curvature heat inequalities, the curvature bound
`v <= K^2` and the time bound `T <= alpha / K`, the gradient norm satisfies the
on-diagonal bound `u(t, x) <= C(n, alpha) K^2 / t` for `t in (0, T]`.

The proof forms `F = t u + beta v` with `beta = 1 + cReact alpha` and runs the
upper-bound maximum principle `scalar_subsolution_affine_bound`.  The barrier
data `a = beta K^2`, `b = beta * 16 K^3` come from the heat inequalities once the
`u`-terms cancel.  The various regularity inputs the maximum principle needs are
threaded through as hypotheses, in the same style as the scalar lower-bound
endpoint. -/
theorem bernstein_first_derivative_estimate
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 < T)
    (u v uLap vLap reaction : Real -> M -> Real)
    (cReact K alpha : Real)
    (hcReact : 0 <= cReact) (hK : 0 < K) (halpha : 0 <= alpha)
    -- the spacetime slab lies in the carrier, with positive times regular
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    -- nonnegativity and the two curvature norm bounds
    (hu_nonneg : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= u t x)
    (hv_nonneg : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= v t x)
    (hv_bound : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, v t x <= K ^ 2)
    (hTK : T <= alpha / K)
    -- the gradient-norm heat inequality (eq 14.17)
    (hu_heat : NablaRm04NormHeatBoundOn (D := D) u uLap v cReact)
    -- the curvature-norm heat equation (eq 14.16) and its reaction bound
    (hv_heat : Rm04NormHeatEquationOn (D := D) v vLap u reaction)
    (hreaction : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      |reaction t x| <= 16 * (v t x) ^ ((3 : Real) / 2))
    -- the Laplacian realizations as the driftless heat operator
    (huLap : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (u t) x = uLap t x)
    (hvLap : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (v t) x = vLap t x)
    -- spatial regularity of the two curvature norms (used for the heat split)
    (hu_space : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_space : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (hv_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (v t) y) x)
    -- regularity of `F = t u + beta v` consumed by Part A
    (hF_cont : ContinuousOn
      (fun p : Real × M =>
        ((1 + cReact * alpha) * K ^ 2 + ((1 + cReact * alpha) * (16 * K ^ 3)) * p.1) -
          (p.1 * u p.1 p.2 + (1 + cReact * alpha) * v p.1 p.2))
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hF_time : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentiableWithinAt Real
        (fun s : Real => s * u s x + (1 + cReact * alpha) * v s x) (Set.Icc 0 T) t)
    (hF_space : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => t * u t z + (1 + cReact * alpha) * v t z) y)
    (hF_grad : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M => t * u t z + (1 + cReact * alpha) * v t z) y) x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      u t x <= bernsteinConstant cReact alpha * K ^ 2 / t := by
  classical
  set β : Real := 1 + cReact * alpha with hβdef
  have hβ_pos : 0 < β := by
    have : 0 <= cReact * alpha := mul_nonneg hcReact halpha
    simp only [hβdef]; linarith
  -- The combined field `F = t u + β v`, with driftless heat operator.
  let F : Real -> M -> Real := fun s y => s * u s y + β * v s y
  let X : Real -> (x : M) -> TangentSpace I x := fun _t x => (0 : TangentSpace I x)
  -- The barrier constants.
  set a : Real := β * K ^ 2 with hadef
  set b : Real := β * (16 * K ^ 3) with hbdef
  -- bound `t * sqrt v <= alpha` on the slab
  have hK2 : (0 : Real) <= K ^ 2 := by positivity
  have hsqrt_v_le : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      Real.sqrt (v t x) <= K := by
    intro t ht x
    have hle : v t x <= K ^ 2 := hv_bound t ht x
    have : Real.sqrt (v t x) <= Real.sqrt (K ^ 2) :=
      Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (le_of_lt hK)] at this
  have ht_sqrt_v_le : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      t * Real.sqrt (v t x) <= alpha := by
    intro t ht x
    have htK : t * K <= alpha := by
      have htle : t <= alpha / K := le_trans ht.2 hTK
      calc t * K <= (alpha / K) * K := by
              exact mul_le_mul_of_nonneg_right htle (le_of_lt hK)
        _ = alpha := by field_simp
    calc t * Real.sqrt (v t x) <= t * K :=
          mul_le_mul_of_nonneg_left (hsqrt_v_le t ht x) ht.1
      _ <= alpha := htK
  -- Part A's subsolution inequality: `(∂ₜ - Δ) F ≤ b` at positive times.
  have hsub : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X F t x <= b := by
    intro t ht htpos x
    -- regular-time wrapper for the carrier derivative interfaces
    let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D :=
      ⟨t, hregular t ht htpos⟩
    -- derivative of `u` from the heat inequality
    obtain ⟨du, hdu_deriv, hdu_le⟩ := hu_heat τ x
    -- derivative of `v` from the heat equation
    have hdv_deriv :
        HasDerivWithinAt (fun s : Real => v s x)
          (vLap t x + (-2 * u t x + reaction t x)) D.carrier (t : Real) :=
      hv_heat τ x
    -- restrict both to the test slab `[0,T] ⊆ D.carrier`
    have hdu_slab :
        HasDerivWithinAt (fun s : Real => u s x) du (Set.Icc 0 T) t := by
      simpa [τ] using hdu_deriv.mono hslab
    have hdv_slab :
        HasDerivWithinAt (fun s : Real => v s x)
          (vLap t x + (-2 * u t x + reaction t x)) (Set.Icc 0 T) t := by
      simpa [τ] using hdv_deriv.mono hslab
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
    -- time derivative of `F` at `t`
    have hFtime :
        HasDerivWithinAt (fun s : Real => F s x)
          ((u t x + t * du) + β * (vLap t x + (-2 * u t x + reaction t x)))
          (Set.Icc 0 T) t := by
      have hprod :
          HasDerivWithinAt (fun s : Real => s * u s x)
            (u t x + t * du) (Set.Icc 0 T) t := by
        have hid : HasDerivWithinAt (fun s : Real => s) 1 (Set.Icc 0 T) t :=
          hasDerivWithinAt_id t (Set.Icc 0 T)
        have := hid.mul hdu_slab
        simpa [one_mul, mul_comm] using this
      have hscaled :
          HasDerivWithinAt (fun s : Real => β * v s x)
            (β * (vLap t x + (-2 * u t x + reaction t x))) (Set.Icc 0 T) t :=
        hdv_slab.const_mul β
      exact hprod.add hscaled
    have hderivWithin :
        derivWithin (fun s : Real => F s x) (Set.Icc 0 T) t =
          (u t x + t * du) + β * (vLap t x + (-2 * u t x + reaction t x)) :=
      hFtime.derivWithin huniq
    -- heat operator of `F t`: linear combination of those of `u t`, `v t`
    have hheatF :
        DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
            (fun _y : M => (0 : TangentSpace I _y)) (F t) x =
          t * uLap t x + β * vLap t x := by
      have hcombo :
          DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
              (fun _y : M => (0 : TangentSpace I _y))
              (fun z : M => t * u t z + β * v t z) x =
            t * DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
                (fun _y : M => (0 : TangentSpace I _y)) (u t) x +
              β * DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
                (fun _y : M => (0 : TangentSpace I _y)) (v t) x :=
        heatOperator_linear_combo (I := I) G t (u t) (v t) t β x
          (hu_space t ht htpos) (hv_space t ht htpos)
          (hu_grad t ht htpos x) (hv_grad t ht htpos x)
      have hFt : F t = (fun z : M => t * u t z + β * v t z) := rfl
      rw [hFt, hcombo, huLap t ht htpos x, hvLap t ht htpos x]
    -- assemble the parabolic operator value
    have hParab :
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X F t x =
          u t x + (t * (du - uLap t x) + β * (-2 * u t x + reaction t x)) := by
      have hXt : X t = (fun _y : M => (0 : TangentSpace I _y)) := rfl
      rw [DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift_eq, hderivWithin, hXt,
        hheatF]
      ring
    -- now estimate using the two heat inequalities
    rw [hParab]
    -- `du - uLap ≤ cReact * sqrt v * u`
    have hdu_diff : du - uLap t x <= cReact * Real.sqrt (v t x) * u t x := by
      have := hdu_le
      simp only [τ] at this
      linarith
    have hu_nn : 0 <= u t x := hu_nonneg t ht x
    have hv_nn : 0 <= v t x := hv_nonneg t ht x
    -- `t * (du - uLap) ≤ t * cReact * sqrt v * u ≤ cReact * alpha * u`
    have hterm_u :
        t * (du - uLap t x) <= (cReact * alpha) * u t x := by
      have h1 : t * (du - uLap t x) <= t * (cReact * Real.sqrt (v t x) * u t x) :=
        mul_le_mul_of_nonneg_left hdu_diff ht.1
      have h2 : t * (cReact * Real.sqrt (v t x) * u t x)
          = cReact * (t * Real.sqrt (v t x)) * u t x := by ring
      have h3 : cReact * (t * Real.sqrt (v t x)) * u t x
          <= cReact * alpha * u t x := by
        have hca : cReact * (t * Real.sqrt (v t x)) <= cReact * alpha :=
          mul_le_mul_of_nonneg_left (ht_sqrt_v_le t ht x) hcReact
        exact mul_le_mul_of_nonneg_right hca hu_nn
      linarith [h1, h2.le, h2.ge, h3]
    -- reaction bound: `reaction ≤ 16 v^{3/2} ≤ 16 K^3`
    have hreact_le : reaction t x <= 16 * K ^ 3 := by
      have habs : |reaction t x| <= 16 * (v t x) ^ ((3 : Real) / 2) := hreaction t ht x
      have hle1 : reaction t x <= 16 * (v t x) ^ ((3 : Real) / 2) :=
        le_trans (le_abs_self _) habs
      have hpow : (v t x) ^ ((3 : Real) / 2) <= K ^ 3 := by
        have hvle : v t x <= K ^ 2 := hv_bound t ht x
        have hbase : (v t x) ^ ((3 : Real) / 2) <= (K ^ 2) ^ ((3 : Real) / 2) :=
          Real.rpow_le_rpow hv_nn hvle (by norm_num)
        have hKpow : (K ^ 2 : Real) ^ ((3 : Real) / 2) = K ^ 3 := by
          rw [← Real.rpow_natCast K 2, ← Real.rpow_mul (le_of_lt hK),
            ← Real.rpow_natCast K 3]
          norm_num
        rw [hKpow] at hbase
        exact hbase
      calc reaction t x <= 16 * (v t x) ^ ((3 : Real) / 2) := hle1
        _ <= 16 * K ^ 3 := by
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    -- combine: the `u`-terms cancel against `+u - 2β u`, leaving `≤ β·16 K^3 = b`
    have hβ_react' : β * reaction t x <= β * (16 * K ^ 3) :=
      mul_le_mul_of_nonneg_left hreact_le (le_of_lt hβ_pos)
    -- The full `u`-coefficient is `1 + cReact α - 2β = -(1 + cReact α) ≤ 0`.
    have hu_cancel :
        u t x + (cReact * alpha) * u t x + β * (-2 * u t x) <= 0 := by
      have heq : u t x + (cReact * alpha) * u t x + β * (-2 * u t x)
          = -(1 + cReact * alpha) * u t x := by
        simp only [hβdef]; ring
      rw [heq]
      have hcoef : 0 <= (1 + cReact * alpha) := by
        have : 0 <= cReact * alpha := mul_nonneg hcReact halpha
        linarith
      have hmul : 0 <= (1 + cReact * alpha) * u t x := mul_nonneg hcoef hu_nn
      linarith
    rw [hbdef]
    calc u t x + (t * (du - uLap t x) + β * (-2 * u t x + reaction t x))
        <= u t x + ((cReact * alpha) * u t x + β * (-2 * u t x + reaction t x)) := by
            linarith [hterm_u]
      _ = (u t x + (cReact * alpha) * u t x + β * (-2 * u t x)) + β * reaction t x := by
            ring
      _ <= 0 + β * (16 * K ^ 3) := by
            linarith [hβ_react', hu_cancel]
      _ = β * (16 * K ^ 3) := by ring
  -- F(0) ≤ a
  have hinitF : ∀ x : M, F 0 x <= a := by
    intro x
    have h0mem : (0 : Real) ∈ Set.Icc 0 T := ⟨le_rfl, le_of_lt hT⟩
    have hv0 : v 0 x <= K ^ 2 := hv_bound 0 h0mem x
    change (0 : Real) * u 0 x + β * v 0 x <= a
    rw [hadef]
    have hbv : β * v 0 x <= β * K ^ 2 :=
      mul_le_mul_of_nonneg_left hv0 (le_of_lt hβ_pos)
    simp only [zero_mul, zero_add]
    exact hbv
  -- Apply Part A.
  have hPartA :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, F t x <= a + b * t := by
    apply scalar_subsolution_affine_bound (I := I) G T (le_of_lt hT) X F a b
    · simpa only [hadef, hbdef, F] using hF_cont
    · intro t ht htpos x; simpa only [F] using hF_time t ht htpos x
    · intro t ht htpos y; simpa only [F] using hF_space t ht htpos y
    · intro t ht htpos x; simpa only [F] using hF_grad t ht htpos x
    · exact hinitF
    · exact hsub
  -- Convert `F ≤ a + b t` into `u ≤ C(n,α) K²/t`.
  intro t ht htpos x
  have hFle : F t x <= a + b * t := hPartA t ht x
  have hv_nn : 0 <= v t x := hv_nonneg t ht x
  have htu_le : t * u t x <= a + b * t := by
    have hβv : 0 <= β * v t x := mul_nonneg (le_of_lt hβ_pos) hv_nn
    have : t * u t x + β * v t x <= a + b * t := hFle
    linarith
  -- `a + b t = β K² + β·16K³·t ≤ β K²(1 + 16 α) = C(n,α) K²`
  have hbt_le : a + b * t <= bernsteinConstant cReact alpha * K ^ 2 := by
    rw [hadef, hbdef, bernsteinConstant, hβdef]
    -- need: β K² + β·16K³·t ≤ β K² (1 + 16 α), i.e. 16 K³ t ≤ 16 K² α.
    have htK : t * K <= alpha := by
      have htle : t <= alpha / K := le_trans ht.2 hTK
      calc t * K <= (alpha / K) * K := mul_le_mul_of_nonneg_right htle (le_of_lt hK)
        _ = alpha := by field_simp
    have hβpos' : 0 < (1 + cReact * alpha) := hβ_pos
    -- (1+cReact α)*K² + (1+cReact α)*(16 K³)*t ≤ (1+cReact α)*(1+16α)*K²
    have hexpand : (1 + cReact * alpha) * (1 + 16 * alpha) * K ^ 2
        = (1 + cReact * alpha) * K ^ 2 + (1 + cReact * alpha) * (16 * K ^ 2 * alpha) := by
      ring
    rw [hexpand]
    have hKt : 16 * K ^ 3 * t <= 16 * K ^ 2 * alpha := by
      have hKt' : K * t <= alpha := by rw [mul_comm]; exact htK
      have hstep : K ^ 2 * (K * t) <= K ^ 2 * alpha :=
        mul_le_mul_of_nonneg_left hKt' hK2
      nlinarith [hstep]
    have hfactor : (1 + cReact * alpha) * (16 * K ^ 3) * t
        <= (1 + cReact * alpha) * (16 * K ^ 2 * alpha) := by
      have : (1 + cReact * alpha) * (16 * K ^ 3) * t
          = (1 + cReact * alpha) * (16 * K ^ 3 * t) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hKt (le_of_lt hβpos')
    linarith [hfactor]
  have htu_le' : t * u t x <= bernsteinConstant cReact alpha * K ^ 2 :=
    le_trans htu_le hbt_le
  -- divide by `t > 0`
  rw [le_div_iff₀ htpos]
  calc u t x * t = t * u t x := by ring
    _ <= bernsteinConstant cReact alpha * K ^ 2 := htu_le'

end DifferentialGeometry.PDE.RicciFlow
