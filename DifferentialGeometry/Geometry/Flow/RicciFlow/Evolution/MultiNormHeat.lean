import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Rank-uniform finite-rank Bochner identity for `compNormSqMulti`

This file proves the **rank-uniform component Bochner identity** (eq-7.4 Step 1):
for a rank-`r` real component array `A` with a supplied per-component time
derivative `Aₜ`, a covariant Laplacian component array `LapA`, and a
covariant-derivative component array `nablaA` (rank `r+1`), the squared component
norm `compNormSqMulti A = Σₘ (A m)²` satisfies

`∂ₜ (compNormSqMulti A) = Δ(compNormSqMulti A) − 2·(compNormSqMulti (∇A))
                            + 2·⟨(∂ₜ − Δ)A, A⟩`.

It is the rank-free generalization of the `|Rm|²` Bochner of
`Evolution/RiemannNorm.lean` (`Rm04NormLaplacianComponentsOn`,
`rm04NormHeatEquationOn_of_components`) and the `|∇Rm|²` Bochner shape of
`Evolution/NablaRiemannHeat.lean`, stated once and for all on the rank-uniform
`compNormSqMulti A` (defined in `NablaRiemannHeat.lean`).  Stated this way, it
later instantiates at `A = ∇ᵏRm` for **any** `k` (rank `r = 4 + k`).

## The two algebraic facts

The whole identity rests on two pointwise component facts, exactly as in the
`k = 0` producer:

* **time derivative**: `∂ₜ Σₘ (A m)² = 2 Σₘ (A m)·(∂ₜ A m)` (product rule on each
  squared component, then a finite sum);
* **Laplacian split** (Bochner): `Δ Σₘ (A m)² = 2 Σₘ (A m)·(Δ A m)
  + 2 Σₘ |∇(A m)|²`, i.e. `Δ|A|² = 2⟨ΔA, A⟩ + 2|∇A|²`.

The second is the genuinely geometric input (the integration-by-parts/Bochner
split) and is taken as a hypothesis at the component level — strictly the same
status as `Rm04NormLaplacianComponentsOn` in the `k = 0` producer.  The reaction
is then *defined* as `2⟨(∂ₜ − Δ)A, A⟩`, and the heat equation is pure algebra.

Nothing here depends on curvature, the metric, or a Ricci-flow hypothesis: it is
reusable real-algebra at the abstraction level mandated by the project's
tensor-calculation workflow.  Everything is phrased so that, in an orthonormal
frame, `compNormSqMulti` is the genuine squared norm (via
`multiNormInFrame_eq_compNormSqMulti`).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

/-! ## Pure pointwise norm-square algebra

`A`, `B` are rank-`r` real component arrays (functions `(Fin r → Idx) → ℝ`).  The
multi-index pairing `⟨A, B⟩ = Σₘ (A m)·(B m)` and the squared norm
`compNormSqMulti A = Σₘ (A m)²` are connected by the product/quotient rules used
below.  No analytic or geometric hypothesis enters. -/

section PointwiseAlgebra

variable {Idx : Type*} [Fintype Idx]

/-- Multi-index pairing of two rank-`r` component arrays,
`⟨A, B⟩ = Σₘ (A m)·(B m)`.  In an orthonormal frame this is the genuine tensor
inner product. -/
def compPairMulti {r : ℕ} (A B : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, A m * B m

theorem compPairMulti_self {r : ℕ} (A : (Fin r → Idx) → Real) :
    compPairMulti A A = compNormSqMulti A := by
  unfold compPairMulti compNormSqMulti
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem compPairMulti_comm {r : ℕ} (A B : (Fin r → Idx) → Real) :
    compPairMulti A B = compPairMulti B A := by
  unfold compPairMulti
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end PointwiseAlgebra

/-! ## The component-level heat-equation interfaces

We phrase the producer over a fixed manifold `M` and a `RealTimeInterval`,
matching the `k = 0`/`k = 1` architecture.  The level array `level`, its time
derivative `levelDt`, its covariant Laplacian `levelLap`, and its
covariant-derivative array `nextLevel` (rank `r + 1`) are all supplied as
abstract component families; the squared-norm fields `normSq`, `normLap`, the
"next" squared norm `nextNormSq`, and `reaction` are the scalar fields. -/

section Producer

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Per-component time-derivative identity for a rank-`r` level array: every
component `s ↦ level s x m` is differentiable in time at every regular time with
derivative `levelDt t x m`.  This is the rank-uniform analogue of the
`rm04Dt`/`nablaRm04`-style time-derivative data. -/
def MultiLevelTimeDerivOn {r : ℕ}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level : Real -> M -> (Fin r → Idx) → Real)
    (levelDt : Real -> M -> (Fin r → Idx) → Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (m : Fin r → Idx),
    HasDerivWithinAt
      (fun s : Real => level s x m)
      (levelDt (t : Real) x m)
      D.carrier
      (t : Real)

/-- The squared component norm `normSq t x = compNormSqMulti (level t x)`. -/
def MultiNormSqDef {r : ℕ}
    (level : Real -> M -> (Fin r → Idx) → Real)
    (normSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), normSq t x = compNormSqMulti (level t x)

/-- **Bochner Laplacian split** at the component level (the genuinely geometric
input): `Δ|A|² = 2⟨ΔA, A⟩ + 2|∇A|²`, i.e.
`normLap t x = 2·⟨levelLap, level⟩ + 2·(compNormSqMulti nextLevel)`,
where `levelLap t x` is the covariant Laplacian of the level array and
`nextLevel t x` is its covariant derivative (rank `r + 1`).  This is the
rank-uniform analogue of `Rm04NormLaplacianComponentsOn`. -/
def MultiNormLaplacianSplit {r : ℕ}
    (level : Real -> M -> (Fin r → Idx) → Real)
    (levelLap : Real -> M -> (Fin r → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (r + 1) → Idx) → Real)
    (normLap nextNormSq : Real -> M -> Real) : Prop :=
  (∀ (t : Real) (x : M),
      normLap t x =
        2 * compPairMulti (levelLap t x) (level t x) +
          2 * nextNormSq t x) ∧
    (∀ (t : Real) (x : M),
      nextNormSq t x = compNormSqMulti (nextLevel t x))

/-- The schematic reaction realized on the level array: twice the pairing of the
component **heat residual** `(∂ₜ − Δ)A` against `A`,
`reaction = 2·⟨levelDt − levelLap, level⟩`.  This is the rank-uniform reaction
shape; under Ricci flow `(∂ₜ − Δ)(∇ᵏRm)` is schematic `∗`-curvature data. -/
def multiReactionDown {r : ℕ}
    (level levelDt levelLap : Real -> M -> (Fin r → Idx) → Real)
    (t : Real) (x : M) : Real :=
  2 * compPairMulti (fun m => levelDt t x m - levelLap t x m) (level t x)

/-- **The time derivative of the squared component norm.**  From the per-component
time-derivative data, `∂ₜ (compNormSqMulti A) = 2 Σₘ (A m)·(∂ₜ A m)`, i.e.
`∂ₜ|A|² = 2⟨∂ₜA, A⟩`.  This is the product-rule + finite-sum half of the Bochner
identity, the rank-uniform analogue of the `|Rm|²` time-derivative. -/
theorem hasDerivWithinAt_compNormSqMulti {r : ℕ}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt : Real -> M -> (Fin r → Idx) → Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) :
    HasDerivWithinAt
      (fun s : Real => compNormSqMulti (level s x))
      (2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x))
      D.carrier
      (t : Real) := by
  classical
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ m : Fin r → Idx, (level s x m) ^ 2)
        (∑ m : Fin r → Idx,
          2 * level (t : Real) x m * levelDt (t : Real) x m)
        D.carrier
        (t : Real) := by
    refine HasDerivWithinAt.fun_sum ?_
    intro m _hm
    have hm := h_dt t x m
    -- `∂ₜ (A m)² = 2 (A m) (∂ₜ A m)`
    have hmul := hm.mul hm
    have hgoal :
        HasDerivWithinAt (fun s : Real => level s x m * level s x m)
          (2 * level (t : Real) x m * levelDt (t : Real) x m) D.carrier (t : Real) := by
      refine hmul.congr_deriv ?_
      ring
    simpa [pow_two] using hgoal
  -- repackage both sides into `compNormSqMulti` / `compPairMulti`
  have hval :
      (∑ m : Fin r → Idx,
          2 * level (t : Real) x m * levelDt (t : Real) x m) =
        2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x) := by
    unfold compPairMulti
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hval] at hsum
  simpa [compNormSqMulti] using hsum

/-- **Rank-uniform Bochner heat equation** (eq-7.4 Step 1).  From

* the per-component time-derivative data (`h_dt`),
* the squared-norm definition `normSq = compNormSqMulti level` (`h_normSq`),
* the Bochner Laplacian split `Δ|A|² = 2⟨ΔA, A⟩ + 2|∇A|²` (`h_lap`),

the squared component norm satisfies, at every regular time and point,

`∂ₜ normSq = normLap + (−2·nextNormSq + reaction)`,
`reaction = 2·⟨(∂ₜ − Δ)A, A⟩ = multiReactionDown level levelDt levelLap`.

This is the rank-uniform generalization of `rm04NormHeatEquationOn_of_components`,
proved as pure component algebra on top of the two pointwise facts.  The
reaction RHS is *derived* from the heat residual `(∂ₜ − Δ)A`, not assumed. -/
theorem multiNormHeatEquationOn_of_components {r : ℕ}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt levelLap : Real -> M -> (Fin r → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (r + 1) → Idx) → Real)
    (normSq normLap nextNormSq : Real -> M -> Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (h_normSq : MultiNormSqDef (M := M) level normSq)
    (h_lap : MultiNormLaplacianSplit (M := M) level levelLap nextLevel
      normLap nextNormSq) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real => normSq s x)
        (normLap (t : Real) x +
          (-2 * nextNormSq (t : Real) x +
            multiReactionDown level levelDt levelLap (t : Real) x))
        D.carrier
        (t : Real) := by
  classical
  obtain ⟨h_lap_eq, _h_next⟩ := h_lap
  intro t x
  -- The derivative of `normSq` agrees with `∂ₜ compNormSqMulti level`.
  have hderiv :
      HasDerivWithinAt
        (fun s : Real => compNormSqMulti (level s x))
        (2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x))
        D.carrier
        (t : Real) :=
    hasDerivWithinAt_compNormSqMulti (D := D) level levelDt h_dt t x
  -- rewrite `normSq = compNormSqMulti level` pointwise in `s`
  have hfun :
      HasDerivWithinAt
        (fun s : Real => normSq s x)
        (2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x))
        D.carrier
        (t : Real) := by
    refine hderiv.congr ?_ ?_
    · intro s _hs; exact h_normSq s x
    · exact h_normSq (t : Real) x
  -- The two derivative values agree by the Laplacian split and the definition
  -- of the reaction term.
  have hval :
      normLap (t : Real) x +
          (-2 * nextNormSq (t : Real) x +
            multiReactionDown level levelDt levelLap (t : Real) x) =
        2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x) := by
    rw [h_lap_eq (t : Real) x]
    -- Name the three pairings; the `±2·nextNormSq` cancel and the pairings add
    -- termwise (`⟨ΔA,A⟩ + ⟨(∂ₜ−Δ)A,A⟩ = ⟨∂ₜA,A⟩`).
    set N : Real := nextNormSq (t : Real) x with hNdef
    have hpair :
        compPairMulti (levelLap (t : Real) x) (level (t : Real) x) +
            compPairMulti
              (fun m => levelDt (t : Real) x m - levelLap (t : Real) x m)
              (level (t : Real) x) =
          compPairMulti (levelDt (t : Real) x) (level (t : Real) x) := by
      unfold compPairMulti
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    unfold multiReactionDown
    -- LHS `= 2⟨ΔA,A⟩ + 2N + (-2N + 2⟨(∂ₜ−Δ)A,A⟩)`; cancel `N` and apply `hpair`.
    have : 2 * compPairMulti (levelLap (t : Real) x) (level (t : Real) x) + 2 * N +
          (-2 * N +
            2 * compPairMulti
              (fun m => levelDt (t : Real) x m - levelLap (t : Real) x m)
              (level (t : Real) x)) =
        2 * (compPairMulti (levelLap (t : Real) x) (level (t : Real) x) +
          compPairMulti
            (fun m => levelDt (t : Real) x m - levelLap (t : Real) x m)
            (level (t : Real) x)) := by ring
    rw [this, hpair]
  rw [hval]
  exact hfun

/-! ## The schematic heat residual and the reaction identity

The reaction produced by `multiNormHeatEquationOn_of_components` is exactly
`2⟨(∂ₜ − Δ)A, A⟩` (the pairing of the **heat residual** against `A`).  For the
`k = 1` curvature tower the geometric content of eq 7.2 is the residual identity

`(∂ₜ − Δ)(∇Rm) = Rm ∗ ∇Rm`   (schematic),

whose RHS, paired with `∇Rm`, is the schematic reaction `nablaRmReactionDown`.
The following lemma is the *thin bridge*: it shows that **whenever** the heat
residual `levelDt − levelLap` equals a supplied schematic `∗`-array `star`, the
`multiReactionDown` reaction equals `2⟨star, A⟩` — i.e. the reaction produced by
the Bochner identity is the schematic `∗`-reaction.  This isolates the genuine
geometric input to the single residual identity.

**Frontier (not yet available at the component level).**  The residual identity
`(∂ₜ − Δ)(∇Rm) = Rm ∗ ∇Rm` is the heat-equation content of eq 7.2.  Deriving it
requires two component-level inputs that the codebase does not yet expose for the
`(0,4)` Riemann tensor:

* `∂ₜ(∇Rm) = ∇(∂ₜRm) + (∂ₜΓ) ∗ Rm` — the time derivative of a covariant
  derivative of a general tensor (only the `g`-specific piece behind `∂ₜΓ`,
  `Variation/Connection.lean`'s `covDtEqDotCov` and
  `Connection/Producers.lean`'s `evol_christoffel_inFrame`, exist);
* `Δ(∇Rm) = ∇(ΔRm) + [Δ, ∇]Rm` with `[Δ, ∇]Rm = Rm ∗ ∇Rm` — the
  Laplacian/covariant-derivative commutator on the `(0,4)` Riemann tensor at the
  component level (the only `[Δ, ∇]`-style result, `frame_trace_thirdCovDeriv_swap`
  in `CurvatureOperator/TensorThirdOrderWeitzenbock.lean`, is bundled
  section-level `TensorRSSpace`/`covApply`/`riemannSec` and has no bridge to these
  `Idx`-component arrays; the component Ricci-identity commutators
  `Ricci/Commutator.lean`, `Tensor/RicciIdentity/OneForm.lean` cover only the
  `(0,2)` Ricci and `(0,1)` one-form cases).

Until those land, `multiReactionDown_eq_of_residual` is the exact splice point:
supplying its `hres` discharges the whole `k = 1` reaction. -/

/-- If the component heat residual `(∂ₜ − Δ)A = levelDt − levelLap` equals a
supplied schematic array `star`, then the Bochner reaction `multiReactionDown`
equals `2·⟨star, A⟩`.  Pure algebra: it is just `multiReactionDown` rewritten
through the residual identity. -/
theorem multiReactionDown_eq_of_residual {r : ℕ}
    (level levelDt levelLap star : Real -> M -> (Fin r → Idx) → Real)
    (t : Real) (x : M)
    (hres : ∀ m : Fin r → Idx,
      levelDt t x m - levelLap t x m = star t x m) :
    multiReactionDown level levelDt levelLap t x =
      2 * compPairMulti (star t x) (level t x) := by
  unfold multiReactionDown compPairMulti
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only []
  rw [hres m]

end Producer

end DifferentialGeometry.PDE.RicciFlow
