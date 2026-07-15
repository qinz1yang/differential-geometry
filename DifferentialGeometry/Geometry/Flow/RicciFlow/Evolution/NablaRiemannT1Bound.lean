import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutatorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannOrthoFrame
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The `T₁` summand of the `k = 1` reaction: reduction to `∇_a(curvature action)` and
the precise residual wall after the tensor-layer contraction-Leibniz (Step A)

`nablaLapCommReactionTerm = T₁ + T₂` (`Evolution/NablaRiemannCommutator.lean`).  The
`T₂` summand (the bare `(0,5)` curvature action `[∇_a,∇_c](∇_b Rm)`) is bounded by
`C(card)·|Rm|·|∇Rm|` in a genuine orthonormal frame in
`Evolution/NablaRiemannT2Bound.lean`; it does **not** need any covariant derivative
of the curvature.

The `T₁` summand is the harder one:
`T₁ = ∇_a([∇_b,∇_c]Rm) = ∇_a(Rm ∗ Rm)`, the covariant derivative of a curvature
action.  This file records the established **reduction** of `T₁` to that covariant
derivative (the `eval_C1_slots` form), and pins the precise residual obstruction to
its quantitative bound after the tensor-layer contraction-Leibniz of
`Tensor/RSTensor/ContractionLeibniz.lean` (Step A) is now available.

## What Step A now provides (`Tensor/RSTensor/ContractionLeibniz.lean`)

The general covariant tensor-product / contraction Leibniz rule for `nabla0SFun`
is now proved, sorry-free and axiom-clean:

* `nabla0SFun_product_eval` — `∇(A ⊗ B) = ∇A ⊗ B + A ⊗ ∇B` in evaluated form;
* `nabla_product_zero_of_zero` — the tensor product of two parallel tensors is
  parallel;
* `nabla_metricPow_zero` — the metric power `g^{⊗r}` is `∇`-parallel
  (`∇(g^{⊗r}) = 0`), from `nabla_metric_zero` by induction;
* `nabla0SFun_metricPow_contraction_eval` — the contraction-against-the-metric-power
  Leibniz: `∇(A ⊗ g^{⊗r}) = ∇A ⊗ g^{⊗r}` (the metric factor passes through `∇`).

This **refutes** the prior conclusion (recorded in `IteratedNablaRmTower.md`, third
follow-up) that "Step A is itself the wall": the `nabla0SFun` contraction-Leibniz
**is** assemblable from `nabla0SFun_eval_smooth_slots` + `nabla_metric_zero`, by the
same concrete-evaluation technique that proves `nabla_smul_metric`.

## What this file establishes

* `nablaLapComm_T1_eq_covDerivK` — `T₁ = ∇_a K` in the explicit tensorial-derivation
  form (`extDerivFun` of the scalar `(b,c)` curvature-action field minus the six
  `∇²Rm`-slot Christoffel corrections), where `K(y) = [∇_b,∇_c]Rm =
  curvatureAction0SAt (rm13 y)(Rm04 y) b c m`.  This is a thin re-export of
  `nablaLapComm_T1_eq_covDeriv_curvatureAction` under the name a downstream `T₁`
  bounder consumes.

## The two mechanisms for the `|T₁| ≤ C·|Rm|·|∇Rm|` bound: route 1 blocked, route 2 viable

`T₁ = ∇_a K`, `K = curvatureAction0SAt (rm13 ·)(Rm04 ·)`.  Bounding it by
`|Rm|·|∇Rm|` needs `∇K` exhibited as a `∇Rm ∗ Rm + Rm ∗ ∇Rm` contraction.  Two
distinct mechanisms could do this; route 1 hits a genuinely-absent rank-`≥1`
formalism bridge, but **route 2 is unblocked** — every tool it needs exists (see the
2026-06-06 seventh follow-up in `IteratedNablaRmTower.md`):

1. **Direct `(1,3)` route (`∇rm13`).**  Differentiating `K` as a contraction of the
   `(1,3)` field `rm13` against `Rm04` produces `∇rm13 ∗ Rm04 + rm13 ∗ ∇Rm04`.  The
   `∇Rm04` factor is `nablaRm04Field` (realized), but **`∇rm13` has no
   `totalNabla*RS` realization** for `S.base.rm13` (the only solution-curvature
   `totalNabla*` realizations are the *lowered* `nablaRm04Field`/`nabla2Rm04Field`/
   `nabla3Rm04Field`).  Step A's `nabla0SFun` Leibniz is for `(0,s) ⊗ (0,q)` tensor
   **products**; `K` is a `Hom`-**contraction** of a `(1,3)` tensor, which it does
   not cover.  Identifying `∇rm13` with `raise(∇Rm04)` is the `(1,3)`
   raising-parallelism `∇(raise rm04) = raise(∇ rm04)`, whose honest statement lives
   in the `tensorRSCovariantDerivative` / `lowerAllUpperIndicesEquiv` formalism
   (`Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`).  Step A's
   `∇(g^{⊗r}) = 0` is the metric-compatibility content of that intertwiner, **but in
   the `nabla0SFun` formalism**; transporting it to the `tensor0SCovariantDerivative`
   one used by `loweredCovDerivAt` needs a `nabla0SFun ↔ tensor0SCovariantDerivative`
   agreement at rank `r ≥ 1`, which is **absent** (the only such agreement is
   `tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative`, `(0,s) ↔ (r=0,s)`).

2. **Raise-form route (`g♯`) — the viable route, all tools now located.**
   `RmRaisingBridge.curvatureAction0SAt_eq_rm04_raise` rewrites
   `K = -Σ_q rm04(…, g♯ βq)` with `βq` the frozen-slot one-form of `Rm04` — using
   **only** `Rm04` (realized) and the metric raising `g♯`, with **no** `rm13`.
   Differentiating this with `nabla0SFun_eval_smooth_slots` for `nablaRm04Field` on
   the moving slot `g♯ βq` needs:
   (a) the **sharp-parallelism** `∇(g♯ β) = g♯(∇β)` —
       `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`
       (`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`), **now made public** (it
       was `private`); its `MDiffAt` hypothesis on the sharp field is discharged by
       `metricSharp_contMDiff_total` (`Geometry/Operator/MetricSharpSmooth.lean`);
   (b) a **frozen-slot covariant Leibniz** `∇(oneFormAtSlot0S Rm04 slots q)` in
       terms of `∇Rm04` — *not* absent: its exact template is `middleFreezeNabla`
       (`Tensor/RSTensor/MetricTrace/Higher.lean`), which differentiates a
       slot-frozen `(0,4)` field and rewrites the result through `nablaA` by
       choosing the frozen-slot sections covariantly constant at `x₀`
       (`TensorLieDeriv.exists_cov_zero_at_apply`,
       `Tensor/RSTensor/NablaOnTensors/Connection/OneJet.lean`).  The frozen
       one-form field itself is built like `freezeMiddle04Field`
       (`Tensor/RSTensor/MetricTrace/NablaTrace02.lean`).
   This route genuinely avoids `∇rm13`.  The earlier "absent" verdict on (b) was
   incorrect: the freeze/`∇` machinery exists and is reusable.

3. **Frame reconciliation — not a wall.**  The reduction `T₁ = ∇_a K`
   (`nablaLapComm_T1_eq_covDeriv_curvatureAction`) is proved at the **smooth** chart
   frame `coordinateFrameAt x₀` because differentiation needs a smooth frame, whereas
   the bound is wanted in the **`g`-orthonormal** frame of
   `NablaRiemannOrthoFrame.exists_orthoFrameAt` (pointwise at `x₀`).  But `∇_a K` is a
   genuine **tensor** value at `x₀` (`nabla3Rm04Field` antisymmetrised), frame-free:
   to bound it on orthonormal-frame vectors one realises *those* vectors by cov-zero
   smooth sections (again `exists_cov_zero_at_apply`) and applies the same Leibniz at
   `x₀`.  No smooth orthonormal field is needed.

So after Step A, the `T₁` bound is reachable by route 2: the sharp-parallelism (now
public) + the frozen-slot covariant Leibniz (template `middleFreezeNabla`) + the
sharp-field smoothness (`metricSharp_contMDiff_total`) + the orthonormal-basis
expansion and Cauchy–Schwarz of `NablaRiemannT2Bound.lean` (`abs_le_sqrt_compNormSq*`,
applied to the two `Rm04 ∗ ∇Rm04` raise-contraction summands).  The construction is
large (a bundled frozen one-form field with its `(0,1)` realization, the
`metricSharp ↔ cotangentSharp_gen` smoothness bridge, the assembled covariant
Leibniz, and the final estimate) but **no longer blocked**; the prior verdict that it
needed an *absent* `nabla0SFun ↔ tensorRS` `r ≥ 1` agreement applied only to the
`(1,3)` route (1), which route 2 sidesteps.  `T₂` is unaffected (no curvature
derivative) and is closed in `NablaRiemannT2Bound.lean`.

**UPDATE (2026-06-07): route 2 is now fully assembled in
`Evolution/NablaRiemannReactionBound.lean`.**  The K-Leibniz
`nablaLapComm_T1_eq_rm04_raise_leibniz`, the `T₁` bound
`abs_nablaLapComm_T1_orthoBasis_le`, the full reaction bound
`abs_nablaLapCommReactionTerm_diag_orthoBasis_le`, and the spatial-commutator bound
`abs_spatialCommNablaRm_orthoFrame_le` are all sorry-free and axiom-clean.
`nablaLapCommReactionTerm` is **fully bounded** by `C(card)·|Rm|·|∇Rm|`.  See the
tenth follow-up of `Evolution/IteratedNablaRmTower.md`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **The `T₁` summand as the covariant derivative of the curvature action.**

At the chart centre `x₀`, for a Ricci-flow solution at a regular time, the first
reaction summand

`T₁ = ∇³Rm(a,b,c,m) − ∇³Rm(a,c,b,m)`

of `nablaLapCommReactionTerm` (`Evolution/NablaRiemannCommutator.lean`) is the
covariant derivative `∇_a K` of the curvature-action field
`K(y) := [∇_b,∇_c]Rm = curvatureAction0SAt (rm13 y)(Rm04 y) b c m`, in the explicit
tensorial-derivation form: the directional derivative of the scalar curvature-action
field along `frame a`, minus the curvature action on each of the six `∇²Rm`-slot
Christoffel corrections (`nabla3CorrectedSlots`).

This is a re-export of `nablaLapComm_T1_eq_covDeriv_curvatureAction`
(`Evolution/NablaRiemannCommutatorBound.lean`) — the entry point a downstream `T₁`
bounder consumes.  The quantitative bound `|T₁| ≤ C·|Rm|·|∇Rm|` is *not* proved
here: see the file header for the precise residual wall after the Step A
contraction-Leibniz (`Tensor/RSTensor/ContractionLeibniz.lean`). -/
theorem nablaLapComm_T1_eq_covDerivK
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) =
      extDerivFun (I := I)
          (fun p : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (S.base.rm04 (t : Real) p)
              (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
              (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
            (fun r : Fin 4 =>
              nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r))) :=
  nablaLapComm_T1_eq_covDeriv_curvatureAction (I := I) S hS t x₀ a b c m

end DifferentialGeometry.PDE.RicciFlow
