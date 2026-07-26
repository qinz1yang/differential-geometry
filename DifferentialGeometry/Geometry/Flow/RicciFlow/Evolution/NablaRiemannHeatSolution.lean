import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.MultiNormHeat

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The frame-independent `k = 1` heat-inequality producer for `|∇Rm|²`

This file closes the **algebraic / frame-independent** half of the `k = 1`
Bernstein–Bando–Shi curvature-derivative producer: it produces the scalar
heat-inequality predicate `NablaRm04NormHeatBoundOn`
(`Evolution/BernsteinShi.lean`) consumed by `bernstein_first_derivative_estimate`,
**without** the orthonormal-frame `InverseMetricOrthonormalAt` plumbing of
`Evolution/NablaRiemannHeat.lean`'s `nablaRm04NormHeatBoundOn_of_components`.

## Why a `horth`-free variant

`bernstein_first_derivative_estimate` (`Evolution/BernsteinShi.lean:419`) consumes
the heat inequality as `NablaRm04NormHeatBoundOn (D := D) u uLap v cReact` for
**abstract scalar fields** `u = |∇Rm|²`, `v = |Rm|²`, `uLap = Δ|∇Rm|²`.  The
existing producer `nablaRm04NormHeatBoundOn_of_components`
(`Evolution/NablaRiemannHeat.lean:634`) threads everything through the
*orthonormal-frame* component norm `nablaRm04NormSqInFrame nablaRm04 gInv` and
requires `horth : InverseMetricOrthonormalAt gInv` (so that
`nablaRm04NormSqInFrame = compNormSq5`), and through the *orthonormal* schematic
reaction `nablaRmReactionInFrame`.  That `horth` is genuinely needed by its
reaction bound `abs_nablaRmReactionInFrame_le`, which is hardwired to
`compNormSq*` (plain component sums).

The scalar inequality itself,
`(∂ₜ − Δ) |∇Rm|² ≤ −2|∇²Rm|² + C·|Rm|·|∇Rm|²`,
is **frame-independent**: `u`, `v`, `uLap`, `|∇²Rm|²` and the contracted reaction
`2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩` are all intrinsic scalars.  The orthonormal frame is only a
*convenience* for evaluating `compNormSq` and for the Cauchy–Schwarz reaction
bound.  This file therefore restates the producer over the *bare scalar fields*,
taking as inputs exactly:

* a heat **equation** `NablaRm04NormHeatEquationOn u uLap nabla2 reaction` (the
  assembled `∂ₜu = uLap + (−2·nabla2 + reaction)` identity — the same status as
  `Rm04NormHeatEquationOn` in the `k = 0` producer `rm04NormHeatEquationOn_of_solution`,
  which likewise takes its Bochner-split component identity as a hypothesis);
* a **reaction bound** `reaction t x ≤ cReact · √(v t x) · u t x`;
* `nabla2 ≥ 0`.

No orthonormality, no `gInv`, no `compNormSq`.

## What this file produces

* `nablaRm04NormHeatBoundSharp_scalar` / `nablaRm04NormHeatBoundOn_scalar` — the
  frame-independent producer: from the heat equation and a frame-independent
  reaction bound, the sharp (`−2|∇²Rm|²`) and dropped scalar heat inequalities,
  the latter being exactly `NablaRm04NormHeatBoundOn`.  This is the `horth`-free
  variant the `k = 1` frontier needs.
* `nablaRm04NormHeatEquationOn_of_multiBochner` — the bridge from the rank-uniform
  Bochner splice `multiNormHeatEquationOn_of_components`
  (`Evolution/MultiNormHeat.lean`, at rank `r = 4`) to the `k = 1` heat-equation
  predicate `NablaRm04NormHeatEquationOn`: the `MultiNormHeat` machinery (the
  per-component time derivative, the Bochner Laplacian split, and the reaction
  *defined* as `2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`) produces the producer's predicate with the
  reaction realized as `multiReactionDown`.
* `nablaRm04NormHeatBoundOn_of_multiBochner_residual` — the assembled
  frame-independent producer from the Bochner splice + the schematic residual
  identity `(∂ₜ − Δ)∇Rm = star` + a frame-independent `∗`-bound on `2⟨star, ∇Rm⟩`.

## Status of the inputs

The two **scalar** inputs (`NablaRm04NormHeatEquationOn` for the solution, and the
frame-independent reaction bound `2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩ ≤ C·|Rm|·|∇Rm|²`) are the
same status as the `k = 0` producer's `Rm04NormHeatEquationOn` /
`abs_rmReactionInFrame_le` hypotheses: component-level assembled facts, fed from
the time-derivative side (`Evolution/NablaRiemannTimeDeriv.lean`,
`iteratedRmComp_one_hasDerivWithinAt`) and the spatial commutator
(`Evolution/NablaRiemannReactionBound.lean`,
`abs_spatialCommNablaRm_orthoFrame_le`).  See the file footer and
`Evolution/IteratedNablaRmTower.md` for the precise frontier on assembling those
two scalars *from a bare `SolutionOn`* in a single frame (the time-derivative /
orthonormal-frame reconciliation).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

/-! ## The frame-independent scalar producer

These work over bare scalar fields `u, uLap, nabla2, reaction, v : Real → M → ℝ`.
No frame, no inverse metric, no `compNormSq`.  They are the `horth`-free analogues
of `nablaRm04NormHeatBoundSharp_of_components` /
`nablaRm04NormHeatBoundOn_of_components`. -/

section ScalarProducer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Sharp frame-independent `k = 1` heat inequality** (Chow–Knopf eq 7.2,
retaining `−2|∇²Rm|²`), scalar form.

From the assembled heat **equation** `∂ₜu = uLap + (−2·nabla2 + reaction)` and a
frame-independent reaction bound `reaction ≤ cReact·√v·u`, every regular time and
point gets a derivative `d = ∂ₜu` with `d ≤ uLap − 2·nabla2 + cReact·√v·u`.

This is the `horth`-free analogue of `nablaRm04NormHeatBoundSharp_of_components`:
nothing here mentions a frame, an inverse metric, or `compNormSq`. -/
theorem nablaRm04NormHeatBoundSharp_scalar
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (u uLap nabla2 reaction v : Real -> M -> Real) (cReact : Real)
    (h_heat : NablaRm04NormHeatEquationOn (D := D) u uLap nabla2 reaction)
    (hreact_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), reaction (t : Real) x ≤ cReact * Real.sqrt (v (t : Real) x) * u (t : Real) x) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      ∃ d : Real,
        HasDerivWithinAt (fun s : Real => u s x) d D.carrier (t : Real) ∧
        d ≤ uLap (t : Real) x +
          (-2 * nabla2 (t : Real) x +
            cReact * Real.sqrt (v (t : Real) x) * u (t : Real) x) := by
  intro t x
  refine ⟨_, h_heat t x, ?_⟩
  have hr := hreact_bound t x
  linarith [hr]

/-- **The frame-independent `k = 1` heat inequality** (Chow–Knopf eq 7.2 /
eq 7.4 at `k = 1`, = MSM144 eq 14.17), scalar form: the `horth`-free
`NablaRm04NormHeatBoundOn` producer.

Dropping the favourable `−2|∇²Rm|² ≤ 0` term from the sharp inequality yields the
exact `NablaRm04NormHeatBoundOn` predicate consumed by
`bernstein_first_derivative_estimate`
(`Evolution/BernsteinShi.lean`):

`(∂ₜ − Δ) |∇Rm|² ≤ cReact · |Rm| · |∇Rm|²`.

This is the `horth`-free analogue of `nablaRm04NormHeatBoundOn_of_components`:
its inputs are the bare scalar heat equation, a frame-independent reaction bound,
and `nabla2 ≥ 0` — no orthonormal frame is required.  It is the producer the
`k = 1` frontier needs once the heat equation and reaction bound are available in
*any* single frame. -/
theorem nablaRm04NormHeatBoundOn_scalar
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (u uLap nabla2 reaction v : Real -> M -> Real) (cReact : Real)
    (h_heat : NablaRm04NormHeatEquationOn (D := D) u uLap nabla2 reaction)
    (hnabla2_nonneg : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), 0 ≤ nabla2 (t : Real) x)
    (hreact_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), reaction (t : Real) x ≤ cReact * Real.sqrt (v (t : Real) x) * u (t : Real) x) :
    NablaRm04NormHeatBoundOn (D := D) u uLap v cReact := by
  intro t x
  obtain ⟨d, hderiv, hle⟩ :=
    nablaRm04NormHeatBoundSharp_scalar (D := D) u uLap nabla2 reaction v cReact
      h_heat hreact_bound t x
  refine ⟨d, hderiv, ?_⟩
  have hdrop : 0 ≤ 2 * nabla2 (t : Real) x := by
    have := hnabla2_nonneg t x; linarith
  linarith [hle, hdrop]

end ScalarProducer

/-! ## The Bochner-splice bridge into `NablaRm04NormHeatEquationOn`

The rank-uniform Bochner splice `multiNormHeatEquationOn_of_components`
(`Evolution/MultiNormHeat.lean`) produces, for a rank-`r` component array `A`
(`level`) with per-component time derivative (`MultiLevelTimeDerivOn`), squared
norm (`MultiNormSqDef`), and Bochner Laplacian split (`MultiNormLaplacianSplit`),
the heat equation `∂ₜ|A|² = Δ|A|² + (−2|∇A|² + 2⟨(∂ₜ − Δ)A, A⟩)`.  At rank `r = 5`
(`A = ∇Rm` is the `(0,5)` array `(Fin 5 → Idx) → ℝ` — one derivative slot plus the
four `Rm` slots; its covariant derivative `nextLevel = ∇²Rm` is rank `6 = 5 + 1`)
this is **exactly** the shape of the `k = 1` predicate
`NablaRm04NormHeatEquationOn` (whose `nablaRm04` carries five `Idx` arguments).
The bridge is essentially the identification of the two `HasDerivWithinAt`
shapes. -/

section BochnerBridge

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **The Bochner-splice bridge to the `k = 1` heat equation.**

From the rank-`r` Bochner-splice component data for `A = ∇Rm` (level array
`level`, time derivative `levelDt`, covariant Laplacian `levelLap`, covariant
derivative `nextLevel`), the assembled heat **equation** `NablaRm04NormHeatEquationOn`
holds with:

* `nablaRmNormSq = normSq = compNormSqMulti level` (`= |∇Rm|²`);
* `nablaRmNormLap = normLap`  (`= Δ|∇Rm|²`);
* `nabla2RmNormSq = nextNormSq = compNormSqMulti nextLevel` (`= |∇²Rm|²`);
* `reaction = multiReactionDown level levelDt levelLap`  (`= 2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`).

This is the `k = 1` analogue of `rm04NormHeatEquationOn_of_components` and shows
that the `Evolution/MultiNormHeat.lean` Bochner machinery directly produces the
producer's predicate; the genuinely geometric input is the Bochner Laplacian
split `h_lap` (the same status as `Rm04NormLaplacianComponentsOn` in the `k = 0`
producer). -/
theorem nablaRm04NormHeatEquationOn_of_multiBochner
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt levelLap : Real -> M -> (Fin 5 → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (5 + 1) → Idx) → Real)
    (normSq normLap nextNormSq : Real -> M -> Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (h_normSq : MultiNormSqDef (M := M) level normSq)
    (h_lap : MultiNormLaplacianSplit (M := M) level levelLap nextLevel
      normLap nextNormSq) :
    NablaRm04NormHeatEquationOn (D := D) normSq normLap nextNormSq
      (multiReactionDown level levelDt levelLap) := by
  intro t x
  exact multiNormHeatEquationOn_of_components (D := D) level levelDt levelLap
    nextLevel normSq normLap nextNormSq h_dt h_normSq h_lap t x

/-- **The assembled frame-independent `k = 1` producer from the Bochner splice and
the schematic residual.**

Combining

* the Bochner-splice component data (`h_dt`, `h_normSq`, `h_lap`) for `A = ∇Rm`,
* the schematic **heat residual identity** `(∂ₜ − Δ)∇Rm = star`
  (`hres`, the geometric content of eq 7.2 — supplied by the time-derivative side
  `Evolution/NablaRiemannTimeDeriv.lean` together with the spatial commutator
  `Evolution/NablaRiemannCommutator.lean`/`Evolution/NablaRiemannReactionBound.lean`),
* a frame-independent `∗`-bound on the contracted residual
  `2⟨star, ∇Rm⟩ ≤ cReact·√v·|∇Rm|²` (`hstar_bound`, Cauchy–Schwarz on the
  `Rm ∗ ∇Rm` residual), and
* `nextNormSq ≥ 0`,

yields the scalar heat inequality `NablaRm04NormHeatBoundOn normSq normLap v cReact`
consumed by `bernstein_first_derivative_estimate`.  No orthonormality is required;
the reaction's reduction to `2⟨star, ∇Rm⟩` is `multiReactionDown_eq_of_residual`. -/
theorem nablaRm04NormHeatBoundOn_of_multiBochner_residual
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt levelLap : Real -> M -> (Fin 5 → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (5 + 1) → Idx) → Real)
    (star : Real -> M -> (Fin 5 → Idx) → Real)
    (normSq normLap nextNormSq v : Real -> M -> Real) (cReact : Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (h_normSq : MultiNormSqDef (M := M) level normSq)
    (h_lap : MultiNormLaplacianSplit (M := M) level levelLap nextLevel
      normLap nextNormSq)
    (hres : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
      (m : Fin 5 → Idx),
      levelDt (t : Real) x m - levelLap (t : Real) x m = star (t : Real) x m)
    (hnext_nonneg : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), 0 ≤ nextNormSq (t : Real) x)
    (hstar_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M),
      2 * compPairMulti (star (t : Real) x) (level (t : Real) x) ≤
        cReact * Real.sqrt (v (t : Real) x) * normSq (t : Real) x) :
    NablaRm04NormHeatBoundOn (D := D) normSq normLap v cReact := by
  -- The heat equation from the Bochner splice.
  have h_heat :
      NablaRm04NormHeatEquationOn (D := D) normSq normLap nextNormSq
        (multiReactionDown level levelDt levelLap) :=
    nablaRm04NormHeatEquationOn_of_multiBochner (D := D) level levelDt levelLap
      nextLevel normSq normLap nextNormSq h_dt h_normSq h_lap
  -- The reaction reduces to `2⟨star, level⟩`, which the `∗`-bound controls.
  refine nablaRm04NormHeatBoundOn_scalar (D := D) normSq normLap nextNormSq
    (multiReactionDown level levelDt levelLap) v cReact h_heat hnext_nonneg ?_
  intro t x
  rw [multiReactionDown_eq_of_residual level levelDt levelLap star (t : Real) x
    (hres t x)]
  exact hstar_bound t x

end BochnerBridge

/-! ## Frontier: assembling the two scalar inputs from a bare `SolutionOn`

The producers above are `horth`-free and reduce the `k = 1` heat inequality to two
*frame-independent scalar* inputs:

1. the assembled heat **equation** `NablaRm04NormHeatEquationOn` (equivalently the
   Bochner-splice data `MultiLevelTimeDerivOn` + `MultiNormSqDef` +
   `MultiNormLaplacianSplit` and a residual identity `hres`), and
2. a frame-independent reaction bound `2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩ ≤ cReact·|Rm|·|∇Rm|²`.

These are the *same status* as the `k = 0` producer's hypotheses
(`rm04NormHeatEquationOn_of_solution` takes its raw-derivative,
contraction-simplification, and Bochner-split component identities as
hypotheses).

The remaining genuine frontier is assembling those two scalars **from a bare
`SolutionOn` in one frame**.  The two halves live in *different* frames:

* The **time-derivative** half `iteratedRmComp_one_hasDerivWithinAt`
  (`Evolution/NablaRiemannTimeDeriv.lean`) is stated for a **time-independent**
  frame (`coordinateFrameAt x₀`), where `∂ₜ` does not pick up a moving-frame term.
  Its three inputs `hrm`/`hchr`/`hswap` are now known to be solution-reachable:
  `hchr` (`∂ₜΓ`) is `coordGammaEvol`; `hrm` (`∂ₜRm04`) is the `(0,4)` analogue of
  the banked `coordRicciEvol` (`∂ₜRm13`
  `christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation` + lowering);
  and `hswap` is `hrm` + spacetime `C²` smoothness via
  `fixedBaseOnReg_of_timeDerivWithin` (`Bundle/PartialMfderiv/FixedBase.lean`)
  applied to the *smooth* `Rm04` component directly (no `∂ₜ∂²ₓΓ`).

* The **spatial reaction** bound `abs_spatialCommNablaRm_orthoFrame_le`
  (`Evolution/NablaRiemannReactionBound.lean`) is proved in a `g(t)`-orthonormal
  frame (`exists_orthoBasisFrameAt`), whose frame vectors depend on `t`.

The two scalar fields `|∇Rm|²`, `2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩` are intrinsic and equal in
both frames, but the codebase has **no** lemma identifying the contracted reaction
scalar across frames (a `coordinateFrameAt`-with-actual-`gInv` reaction bound, or
a scalar reaction frame-invariance), and **no** moving-frame `∂ₜ(frame)` correction
to `iteratedRmComp_one_hasDerivWithinAt` for a `t`-dependent orthonormal frame.
Either one closes the gap; both are framework-scale.  See
`Evolution/IteratedNablaRmTower.md` (eleventh follow-up) for the precise statement.
-/

end DifferentialGeometry.PDE.RicciFlow
