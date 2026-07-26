import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The time derivative of `∇Rm` (level 1): `∂ₜ(∇Rm) = ∇(∂ₜRm) + (∂ₜΓ) ∗ Rm`

This file builds the **temporal half** of the `k = 1` Bernstein–Bando–Shi heat
residual: differentiating the explicit covariant-derivative component formula
`covDerivStepComp` in time produces `∇(∂ₜRm)` plus an explicit `(∂ₜΓ) ∗ Rm`
correction.

It is the temporal companion of the spatial Laplacian commutator
`Evolution/NablaRiemannCommutator.lean` (`[Δ, ∇] Rm = Rm ∗ ∇Rm`); together they
furnish the heat residual `(∂ₜ − Δ)(∇Rm)` that the `k = 1` Bochner producer
`Evolution/MultiNormHeat.lean` (`multiReactionDown_eq_of_residual`) and
`Evolution/NablaRiemannHeat.lean` consume.

## The identity

The level-1 tower array (`Evolution/IteratedNablaRmTower.lean`) is
`iteratedRmComp frame chr base 1 t x = covDerivStepComp (frameExtData …) (chr t x) (base t x)`,
i.e. (writing `A` for the level-0 array `Rm04` frame components)

`(∇A)(n) = ∂_{n 0} A(tail n) − Σ_slot Σ_p Γᵖ_{(n 0),(tail n slot)} · A((tail n)[slot ↦ p])`.

Differentiating in time at a regular time, with the two cited geometric inputs:

* `∂ₜA` (the Uhlenbeck curvature evolution `∂ₜRm = ΔRm + Rm∗Rm`,
  `UhlenbeckCurvatureEvolutionInFrameOn` / `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`),
* `∂ₜΓ` (the Christoffel evolution `∂ₜΓ = ∇Ric ∗ 1`,
  `evol_christoffel_inFrame`),

and the spatial-frame/time **derivative swap** `FixedBaseExtDerivTimeDerivativeOnRegular`
(`Bundle/PartialMfderiv/FixedBase.lean`) for the leading exterior-derivative
slot, the product rule gives

`∂ₜ (∇A)(n) = (∇(∂ₜA))(n) − Σ_slot Σ_p (∂ₜΓ)ᵖ_{(n 0),(tail n slot)} · A((tail n)[slot ↦ p])`.

The first summand `∇(∂ₜA) = covDerivStepComp (frameExtData (∂ₜA)) (chr) (∂ₜA)`
is the covariant derivative of `∂ₜRm`; the second is the explicit `(∂ₜΓ) ∗ Rm`
correction array.

## What this file produces

* `covDerivStepDt` — the explicit `(∂ₜΓ) ∗ A` correction array: the single
  Christoffel-time-derivative term per moving slot;
* `covDerivStepComp_hasDerivWithinAt` — the **rank-uniform** time-derivative
  identity at the `covDerivStepComp` level (pure real calculus, no curvature or
  Ricci-flow hypothesis): the time derivative of the covariant-derivative array
  equals `covDerivStepComp (… ∂ₜA …) − covDerivStepDt`;
* `iteratedRmComp_one_hasDerivWithinAt` — the **specialization to the realized
  level-1 tower** `iteratedRmComp (coordinateFrameAt) (realizedChr) (realizedRmBase) 1`,
  delivering the `MultiLevelTimeDerivOn`-shaped `HasDerivWithinAt` of
  `s ↦ iteratedRmComp … 1 s x n` that the downstream splice expects, with the
  level-1 time derivative array given explicitly by `covDerivStepComp (∂ₜRm) − (∂ₜΓ)∗Rm`.

The two geometric time derivatives `∂ₜRm` and `∂ₜΓ` and the derivative swap are
taken as the cited interface hypotheses (`evol_christoffel_inFrame`,
`UhlenbeckCurvatureEvolutionInFrameOn`, `FixedBaseExtDerivTimeDerivativeOnRegular`);
no time-derivative fact is axiomatized here.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry
open scoped Manifold ContDiff BigOperators

/-! ## The rank-uniform `covDerivStepComp` time derivative

We work at the pure component level (a rank-`r` array is `(Fin r → Idx) → ℝ`),
matching the abstraction level of `covDerivStepComp` itself.  The only inputs are
real-calculus differentiability facts about the supplied component families; no
curvature, metric, or Ricci-flow hypothesis enters, so this lives at the reusable
level mandated by the project's tensor-calculation workflow. -/

section StepDeriv

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The explicit `(∂ₜΓ) ∗ A` correction array, rank `r → r+1`: for a rank-`r`
array `A` and a Christoffel-time-derivative datum `chrDt`, the single correction
term per moving slot,

`covDerivStepDt chrDt A n = Σ_slot Σ_p (∂ₜΓ)ᵖ_{(n 0),(tail n slot)} · A((tail n)[slot ↦ p])`.

This is exactly the term produced by differentiating the Christoffel-correction
part of `covDerivStepComp` in time and freezing `A`. -/
def covDerivStepDt {r : ℕ}
    (chrDt : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) : (Fin (r + 1) → Idx) → Real :=
  fun n =>
    ∑ s : Fin r, ∑ p : Idx,
      chrDt (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p)

/-- **The rank-uniform `covDerivStepComp` time-derivative identity.**

Fix a base point `x`, a multi-index `n`, and a time `t` (with the derivative
taken within a time set `D`).  Suppose, for the supplied time-dependent rank-`r`
component family `A`, Christoffel family `chr`, and their time derivatives `Adt`,
`chrDt`:

* `hA` — every component `s ↦ A s x m` is differentiable in time with derivative
  `Adt t x m`;
* `hchr` — every Christoffel entry `s ↦ chr s x i a p` is differentiable in time
  with derivative `chrDt t x i a p`;
* `hswap` — for the leading derivative direction `frame (n 0) x` and each moving
  multi-index `m`, the spatial exterior derivative `s ↦ ∂_{frame (n 0)} A s x m`
  is differentiable in time with derivative `∂_{frame (n 0)} (Adt t) x m`
  (the time/spatial-frame **derivative swap**, supplied by
  `FixedBaseExtDerivTimeDerivativeOnRegular`).

Then the level-`(r+1)` covariant-derivative component
`s ↦ covDerivStepComp (frameExtData frame (A s ·) x) (chr s x) (A s x) n` is
differentiable in time, with derivative

`covDerivStepComp (frameExtData frame (Adt t ·) x) (chr t x) (Adt t x) n
   − covDerivStepDt (chrDt t x) (A t x) n`,

i.e. `∂ₜ(∇A) = ∇(∂ₜA) − (∂ₜΓ) ∗ A`. -/
theorem covDerivStepComp_hasDerivWithinAt {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (A Adt : Real → M → (Fin r → Idx) → Real)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    {D : Set Real} {t : Real} (x : M) (n : Fin (r + 1) → Idx)
    (hA : ∀ m : Fin r → Idx,
      HasDerivWithinAt (fun s : Real => A s x m) (Adt t x m) D t)
    (hchr : ∀ i a p : Idx,
      HasDerivWithinAt (fun s : Real => chr s x i a p) (chrDt t x i a p) D t)
    (hswap : ∀ m : Fin r → Idx,
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I) (fun y : M => A s y m) x (frame (n 0) x))
        (extDerivFun (I := I) (fun y : M => Adt t y m) x (frame (n 0) x))
        D t) :
    HasDerivWithinAt
      (fun s : Real =>
        covDerivStepComp
          (frameExtData (I := I) frame (fun y : M => A s y) x)
          (chr s x) (A s x) n)
      (covDerivStepComp
          (frameExtData (I := I) frame (fun y : M => Adt t y) x)
          (chr t x) (Adt t x) n -
        covDerivStepDt (chrDt t x) (A t x) n)
      D t := by
  classical
  -- The leading slot derivative is the supplied derivative swap (at `m = tail n`).
  have hlead := hswap (Fin.tail n)
  -- The correction double sum differentiates by the product rule per term.
  have hcorr :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ slot : Fin r, ∑ p : Idx,
            chr s x (n 0) (Fin.tail n slot) p *
              A s x (Function.update (Fin.tail n) slot p))
        (∑ slot : Fin r, ∑ p : Idx,
          (chrDt t x (n 0) (Fin.tail n slot) p *
              A t x (Function.update (Fin.tail n) slot p) +
            chr t x (n 0) (Fin.tail n slot) p *
              Adt t x (Function.update (Fin.tail n) slot p)))
        D t := by
    refine HasDerivWithinAt.fun_sum ?_
    intro slot _hslot
    refine HasDerivWithinAt.fun_sum ?_
    intro p _hp
    exact (hchr (n 0) (Fin.tail n slot) p).mul (hA (Function.update (Fin.tail n) slot p))
  -- The covariant-derivative array's `s`-dependence is, definitionally, the
  -- leading exterior-derivative slot minus the Christoffel-correction double sum;
  -- so its time derivative is `hlead.sub hcorr`.
  have hmain :
      HasDerivWithinAt
        (fun s : Real =>
          covDerivStepComp
            (frameExtData (I := I) frame (fun y : M => A s y) x)
            (chr s x) (A s x) n)
        (extDerivFun (I := I) (fun y : M => Adt t y (Fin.tail n)) x (frame (n 0) x) -
          ∑ slot : Fin r, ∑ p : Idx,
            (chrDt t x (n 0) (Fin.tail n slot) p *
                A t x (Function.update (Fin.tail n) slot p) +
              chr t x (n 0) (Fin.tail n slot) p *
                Adt t x (Function.update (Fin.tail n) slot p)))
        D t :=
    hlead.sub hcorr
  refine hmain.congr_deriv ?_
  -- Identify the derivative value with `∇(∂ₜA) − (∂ₜΓ)∗A`.  Unfold both target
  -- summands and distribute the per-term product-rule sum into the
  -- `chr·(∂ₜA)` (covariant-derivative) and `(∂ₜΓ)·A` (correction) atomic sums.
  rw [covDerivStepComp, frameExtData, covDerivStepDt]
  simp only [Finset.sum_add_distrib]
  ring

end StepDeriv

/-! ## Specialization to the realized level-1 tower

For a Ricci-flow `SolutionOn`, the level-1 producer array
`iteratedRmComp (coordinateFrameAt x₀) (realizedChr S x₀) (realizedRmBase S x₀) 1`
unfolds (via `iteratedRmComp_succ` / `iteratedRmComp_zero`) into exactly the
`covDerivStepComp` shape of the general lemma, with `A = realizedRmBase` and
`chr = realizedChr`.  Feeding the cited geometric time derivatives delivers the
`MultiLevelTimeDerivOn`-shaped `HasDerivWithinAt` for `∇Rm`. -/

section Realized

open Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **The level-1 time-derivative identity for the realized `∇Rm` tower.**

At a base point `x` of the chart-frame neighbourhood, for the realized tower over
a Ricci-flow solution `S`, the level-1 array `s ↦ ∇Rm(s)` is differentiable in
time with derivative `∇(∂ₜRm) − (∂ₜΓ) ∗ Rm`.

The three geometric inputs are taken as the cited interface hypotheses:

* `hrm` — the level-0 time derivative `∂ₜRm` of the lowered Riemann frame
  components (Uhlenbeck curvature evolution, the realized `MultiLevelTimeDerivOn`
  shape of `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` /
  `UhlenbeckCurvatureEvolutionInFrameOn`);
* `hchr` — the Christoffel time derivative `∂ₜΓ` in the chart frame
  (`evol_christoffel_inFrame`);
* `hswap` — the spatial-frame/time derivative swap for the level-0 components
  (`FixedBaseExtDerivTimeDerivativeOnRegular`, applied at the leading derivative
  direction).

The output is exactly the `HasDerivWithinAt (fun s => iteratedRmComp … 1 s x n) …`
shape required by `MultiLevelTimeDerivOn` for level 1 — the temporal half of the
`k = 1` BBS heat residual. -/
theorem iteratedRmComp_one_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (rm04Dt : Real → M → (Fin 4 → CoordinateIdx (𝕜 := Real) E) → Real)
    (chrDt : Real → M →
      CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → Real)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M)
    (n : Fin 5 → CoordinateIdx (𝕜 := Real) E)
    (hrm : ∀ m : Fin 4 → CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real => realizedRmBase (I := I) S x₀ s x m)
        (rm04Dt (t : Real) x m) D.carrier (t : Real))
    (hchr : ∀ i a p : CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real => realizedChr (I := I) S x₀ s x i a p)
        (chrDt (t : Real) x i a p) D.carrier (t : Real))
    (hswap : ∀ m : Fin 4 → CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I) (fun y : M => realizedRmBase (I := I) S x₀ s y m) x
            (coordinateFrameAt (I := I) x₀ (n 0) x))
        (extDerivFun (I := I) (fun y : M => rm04Dt (t : Real) y m) x
          (coordinateFrameAt (I := I) x₀ (n 0) x))
        D.carrier (t : Real)) :
    HasDerivWithinAt
      (fun s : Real =>
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
          (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 s x n)
      (covDerivStepComp
          (frameExtData (I := I) (coordinateFrameAt (I := I) x₀)
            (fun y : M => rm04Dt (t : Real) y) x)
          (realizedChr (I := I) S x₀ (t : Real) x)
          (rm04Dt (t : Real) x) n -
        covDerivStepDt (chrDt (t : Real) x)
          (realizedRmBase (I := I) S x₀ (t : Real) x) n)
      D.carrier (t : Real) := by
  -- Unfold the level-1 tower array to the bare `covDerivStepComp` shape.
  have hunfold :
      (fun s : Real =>
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
          (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 s x n) =
        fun s : Real =>
          covDerivStepComp
            (frameExtData (I := I) (coordinateFrameAt (I := I) x₀)
              (fun y : M => realizedRmBase (I := I) S x₀ s y) x)
            (realizedChr (I := I) S x₀ s x)
            (realizedRmBase (I := I) S x₀ s x) n := by
    funext s
    rw [iteratedRmComp_succ]
    simp only [iteratedRmComp_zero]
  rw [hunfold]
  exact covDerivStepComp_hasDerivWithinAt
    (I := I) (coordinateFrameAt (I := I) x₀)
    (realizedRmBase (I := I) S x₀) rm04Dt
    (realizedChr (I := I) S x₀) chrDt
    x n hrm hchr hswap

end Realized

end DifferentialGeometry.PDE.RicciFlow
