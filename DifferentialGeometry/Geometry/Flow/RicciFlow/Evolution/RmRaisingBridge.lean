import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutator

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The pointwise `rm13 = raise(rm04)` bridge and the curvature action via `rm04`

This file builds the **pointwise metric raising bridge** between the solution
curvatures `S.base.rm13` (a `(1,3)` tensor) and `S.base.rm04` (its lowered
`(0,4)` form), and uses it to re-express the slotwise curvature action
`curvatureAction0SAt (rm13) α` entirely through the *all-lowered* tensor `rm04`.

This is step 1 (and the algebraic part of step 3) of the `k = 1` quantitative
producer plan in `Evolution/IteratedNablaRmTower.md`.

## What is available in the tree, and what this file adds

The pointwise lowering relation
`Rm04LowersRm13At g x (rm13 x) (rm04 x)` — i.e. `rm04(X,Y,Z,W) = rm13 (g♭ W)(X,Y,Z)`
— is *already proved* from the two shared connection realizations by
`rm04LowersRm13At_of_realizes` (`Geometry/Curvature/Components/Lowering.lean`),
and is instantiated for the *metric* curvatures `metricRm13`/`metricRm04` inside
`Geometry/Curvature/Metric.lean`.  Since `S.base.rm13 t = metricRm13 (g t)` and
`S.base.rm04 t = metricRm04 (g t)` definitionally, the lowering relation transfers
to the solution curvatures with no new realization input.

This file:

* `solution_rm04LowersRm13At` — the lowering relation for the *solution*
  curvatures `S.base.rm13`/`S.base.rm04`, at every flow time and point;
* `rm13_apply_eq_rm04_raise` — the **raising bridge**: inverting the lowering with
  the metric sharp map, `rm13 x β (X,Y,Z) = rm04 (X,Y,Z, g♯ β)` for *any* covector
  `β` (not only `β = g♭ W`).  This is the pointwise `rm13 = raise(rm04)` identity
  in the form the curvature action consumes;
* `curvatureAction0SAt_eq_rm04_raise` — the curvature action `curvatureAction0SAt
  (rm13) α X Y slots` expressed purely through the lowered tensor `rm04`:
  `-Σ_q rm04 (X, Y, slots_q, g♯(freezeSlot α slots q))`.  This removes every
  occurrence of the `(1,3)` tensor `rm13` from the curvature action; only the
  all-lowered `rm04` and the metric raising remain.

## Why this is the right layer (and what it does *not* do)

`curvatureAction0SAt` is the slotwise contraction appearing on the right of every
`(0,s)` Ricci identity (`rm04_ricciIdentityAt`, `nablaRm04_ricciIdentityAt`).  Its
*only* curvature dependence is through `rm13 x · (vec3 X Y ·)`; the bridge below
turns that into `rm04`, the tensor that carries a frame component norm
(`rm04Comp`, `compNormSq4`).  This is exactly what a downstream orthonormal-frame
norm bound for the **`T₂` summand** `curvatureAction0SAt (rm13)(∇Rm)` of
`nablaLapCommReactionTerm` needs: that summand is a curvature action contracting
`rm13` against `∇Rm`, and its bound by `|Rm|·|∇Rm|` requires `rm13`, *not* `∇rm13`.

It deliberately does **not** touch `∇rm13`.  The first reaction summand
`∇_a([∇_b,∇_c]Rm)` of `nablaLapCommReactionTerm` (see
`NablaRiemannCommutatorBound.lean`) is the covariant derivative of a curvature
action; differentiating the contraction above covariantly produces a
`∇(g♯) ∗ rm04 + g♯ ∗ ∇rm04` split whose `∇(g♯)` factor is the covariant
derivative of the metric raising.  The honest statement of `∇(g♯) = 0` is the
`(1,3)` index-raising parallelism, which is *not* available in the tree (the
proved parallelism `loweredCovDerivAt_eq_lower_tensorCovDerivAt[_gen]` is the
rank-`(0,s)` lowering, whose proof carries **no** `∇g = 0` content; there is no
`(1,3)` `totalNablaRS` realization either).  See the footer of
`NablaRiemannCommutatorBound.lean` for the precise remaining wall.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## The solution-level pointwise lowering relation -/

/-- **The lowering relation for the solution curvatures.**  At every flow time and
point, the solution's lowered `(0,4)` Riemann tensor is the metric lowering of its
`(1,3)` Riemann tensor:

`rm04(X,Y,Z,W) = rm13 (g♭ W) (X,Y,Z)`.

This is `rm04LowersRm13At_of_realizes` transported through the definitional
identities `S.base.rm13 t = metricRm13 (g t)` and `S.base.rm04 t = metricRm04 (g t)`;
the two shared connection realizations are supplied by `metricCurvData`. -/
theorem solution_rm04LowersRm13At
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I)
      (S.base.metric t) x (S.base.rm13 t x) (S.base.rm04 t x) := by
  have h :=
    rm04LowersRm13At_of_realizes
      (I := I) (S.base.metric t)
      (metricCov (I := I) (M := M) (S.base.metric t))
      (metricRm13 (I := I) (M := M) (S.base.metric t))
      (metricRm04 (I := I) (M := M) (S.base.metric t))
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
      x
  simpa [SolutionFamily.rm13, SolutionFamily.rm04] using h

/-! ## The raising bridge: `rm13 β = raise(rm04)` for an arbitrary covector

The lowering relation evaluates `rm13` only at lowered covectors `g♭ W`.  Inverting
with the metric sharp map `g♯` (`cotangentSharp_gen`) extends it to an *arbitrary*
covector `β`: writing `β` as `g♭ (g♯ β)` (`cotangentSharp_inner_eval`), the lowering
identity gives `rm13 x β (X,Y,Z) = rm04 (X,Y,Z, g♯ β)`. -/

/-- **The pointwise raising bridge.**  For any pointwise lowering relation
`Rm04LowersRm13At g x Rm13 Rm04`, the `(1,3)` tensor is recovered from the lowered
`(0,4)` tensor by raising the paired covector with the metric sharp map:

`Rm13 β (X,Y,Z) = Rm04 (X, Y, Z, g♯ β)`  for every covector `β`.

This is the metric raising `rm13 = raise(rm04)` in the pointwise evaluation form
the slotwise curvature action consumes. -/
theorem rm13_apply_eq_rm04_raise
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    Rm13 β (vec3 (I := I) X Y Z) =
      Rm04 (vec4 (I := I) X Y Z (cotangentSharp_gen (I := I) g x β)) := by
  -- `hLower` with `W := g♯ β`.
  have hL := hLower X Y Z (cotangentSharp_gen (I := I) g x β)
  -- `rm04(X,Y,Z, g♯β) = rm13 (g♭ (g♯β)) (X,Y,Z)`; show `g♭ (g♯β)` lowers back to `β`.
  rw [hL]
  -- The lowered raised covector `dualToCotangent (g♭ (g♯ β))` is `β` itself.
  have hβ :
      dualToCotangent_gen (I := I)
          ((tangentFlatLinear_gen (I := I) g x) (cotangentSharp_gen (I := I) g x β)) = β := by
    -- Apply the (injective) `cotangent → dual` map; the round-trip collapses the LHS.
    refine cotangentToDualLinear_injective_gen (I := I) (x := x) ?_
    rw [cotangentToDualLinear_apply_gen, cotangentToDualLinear_apply_gen,
      cotangentToDual_dualToCotangent_gen]
    -- `g♭ (g♯ β) = cotangentToDual β` as duals: both send `X ↦ β X`.
    ext X
    rw [tangentFlatLinear_apply_gen, cotangentToDual_apply_gen,
      cotangentSharp_inner_eval]
  rw [hβ]

/-! ## The curvature action expressed through `rm04`

The slotwise curvature action `curvatureAction0SAt Rm13 α X Y slots` pairs `Rm13`
against the frozen-slot one-forms of `α`.  Applying the raising bridge to each
pairing rewrites the whole action through the all-lowered `Rm04`. -/

/-- **The curvature action via the lowered tensor `rm04`.**  Using the raising
bridge on each slot, the slotwise curvature action is the all-lowered contraction

`curvatureAction0SAt Rm13 α X Y slots
  = -Σ_q Rm04 (X, Y, slots_q, g♯(freezeSlot α slots q))`,

with `g♯ = cotangentSharp_gen g x` the metric raising of the `q`-th frozen-slot
one-form of `α`.  Every occurrence of the `(1,3)` tensor `Rm13` is gone; only the
all-lowered `Rm04` and the metric raising remain.  This is the form whose
orthonormal-frame components carry the `rm04` component norm. -/
theorem curvatureAction0SAt_eq_rm04_raise
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    curvatureAction0SAt (I := I) Rm13 alpha X Y slots =
      -∑ q : Fin s,
        Rm04 (vec4 (I := I) X Y (slots q)
          (cotangentSharp_gen (I := I) g x
            (oneFormAtSlot0S (I := I) alpha slots q))) := by
  -- Unfold the curvature action and apply the raising bridge slotwise.
  change
    -∑ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
        (vec3 (I := I) X Y (slots q)) = _
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact rm13_apply_eq_rm04_raise (I := I) g (Rm13 x) Rm04 hLower
    (oneFormAtSlot0S (I := I) alpha slots q) X Y (slots q)

/-! ## The second reaction summand `T₂` expressed through `rm04` and `∇rm04`

The second summand of `nablaLapCommReactionTerm`
(`Evolution/NablaRiemannCommutator.lean`) is the `(0,5)` curvature action
`curvatureAction0SAt (rm13) (∇Rm)`, i.e. the curvature commutator `[∇_a,∇_c](∇_b Rm)`
on `∇Rm`.  Its only curvature dependence is through `rm13`; the raising bridge
removes it, leaving an all-lowered contraction of the solution's `rm04` and
`nablaRm04Field` (`= ∇rm04`).  No `∇rm13` is involved — this summand needs only the
*undifferentiated* curvature, so its bound by `|Rm|·|∇Rm|` does **not** hit the
`∇rm13` wall of the first summand. -/

/-- **The second reaction summand via `rm04`/`∇rm04`.**  At the chart centre `x₀`,
for a Ricci-flow solution, the second summand of `nablaLapCommReactionTerm` — the
`(0,5)` curvature action on `∇Rm` — is the all-lowered contraction

`curvatureAction0SAt (rm13) (∇Rm) a c (b::m)
  = -Σ_q rm04 (e_a, e_c, slots_q, g♯(freezeSlot (∇Rm) slots q))`,

with `slots = nabla3InnerSlots … b m` and `g♯` the metric raising.  Every `rm13`
is gone; the contraction is of the solution's lowered `rm04` against the lowered
`∇Rm` (`nablaRm04Field`) and the metric raising.  This is the `T₂`-half of the
`k = 1` reaction in a form carrying the `rm04` component norm. -/
theorem nablaLapComm_secondTerm_eq_rm04_raise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) (S.base.rm13 t)
        (nablaRm04Field (I := I) S t x₀)
        (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
        (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) =
      -∑ q : Fin 5,
        S.base.rm04 t x₀
          (vec4 (I := I) (coordinateFrameAt (I := I) x₀ a x₀)
            (coordinateFrameAt (I := I) x₀ c x₀)
            (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m q)
            (cotangentSharp_gen (I := I) (S.base.metric t) x₀
              (oneFormAtSlot0S (I := I) (nablaRm04Field (I := I) S t x₀)
                (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) q))) :=
  curvatureAction0SAt_eq_rm04_raise (I := I) (S.base.metric t) (S.base.rm13 t)
    (S.base.rm04 t x₀)
    (solution_rm04LowersRm13At (I := I) S t x₀)
    (nablaRm04Field (I := I) S t x₀)
    (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
    (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)

end DifferentialGeometry.PDE.RicciFlow
