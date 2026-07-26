import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The rank-uniform (all-`k`) `∇ᵏRm` realization bridge

This file generalizes the `k = 1`/`k = 2` curvature-derivative realization bridge
of `Evolution/RmRealizationBridge.lean`
(`iteratedRmComp_one_eq_nablaRm04Field`, `iteratedRmComp_two_eq_nabla2Rm04Field`)
to **every** order `k`, by induction on `k`.

The pieces, in order:

1. **The bundled iterated field** `nablaKRm04Field S t k : Tensor0SField ∞ (4+k)`
   — `k` iterations of `totalNabla0S` starting from `S.base.rm04 t`, the
   rank-uniform generalization of `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field`.
   Its canonical realization at each step (`nablaKRm04Field_realizes`) is read off
   from `totalNabla0S_realizes` directly.

2. **The rank-uniform bridge** `iteratedRmComp_eq_nablaKRm04Field` — at every point
   of the coordinate-frame neighbourhood of `x₀` and for every `k`, the level-`k`
   producer array of `Evolution/IteratedNablaRmTower.lean`, frame-evaluated, equals
   `nablaKRm04Field` at the frame vectors.  Proved **by induction on `k`**: the base
   `k = 0` is `realizedRmBase`; the step rewrites the inner level-`k` array via the
   inductive hypothesis on the whole neighbourhood (exactly as
   `iteratedRmComp_two_eq_nabla2Rm04Field` chains rank 5 → 6) and then applies the
   rank-uniform step bridge `covDerivStepComp_frameComp_eq`.

3. **The rank-uniform `(0,s)` Ricci identity** `nablaKRm04_nabla20SRealizesAt` and
   `nablaKRm04_ricciIdentityAt` — applying `tensor0S_ricciIdentity_of_torsionFree`
   at `s = 4 + k` for every `k`, via the discharged `Nabla20SRealizesAt` package
   (the rank-uniform generalization of `rm04_nabla20SRealizesAt` /
   `nablaRm04_nabla20SRealizesAt`).

No realization predicate is assumed: every `TotalNabla0SRealizes` /
`Nabla20SRealizesAt` witness is discharged from the canonical `totalNabla0S_realizes`,
by induction, with no axiomatization.  At `k = 0` and `k = 1` these statements reduce
to the concrete-rank bridge theorems of `RmRealizationBridge.lean`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## The bundled iterated field `∇ᵏRm`

The rank-uniform generalization of `nablaRm04Field` (`k = 1`), `nabla2Rm04Field`
(`k = 2`), `nabla3Rm04Field` (`k = 3`): `k` iterations of `totalNabla0S` starting
from the lowered Riemann tensor `S.base.rm04 t`, producing a rank-`(4+k)` field.

The arity step `4 + (k+1) = (4+k) + 1` is handled definitionally, exactly as the
component-level `iteratedRmComp` recursion does. -/

section Field

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- The canonical `k`-th covariant-derivative tensor field `∇ᵏRm` of the lowered
Riemann tensor (rank `4 + k`), built by `k` iterations of `totalNabla0S`.

* `k = 0`: the lowered Riemann tensor `S.base.rm04 t`.
* `k + 1`: one canonical total covariant derivative of level `k`.

This is the rank-uniform generalization of `nablaRm04Field` /
`nabla2Rm04Field` / `nabla3Rm04Field`. -/
def nablaKRm04Field
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (k : ℕ) →
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)
  | 0 => S.base.rm04 t
  | (k + 1) =>
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t) (nablaKRm04Field S t k)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t)
          (nablaKRm04Field S t k))

@[simp] theorem nablaKRm04Field_zero
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    nablaKRm04Field (I := I) S t 0 = S.base.rm04 t := rfl

theorem nablaKRm04Field_succ
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    nablaKRm04Field (I := I) S t (k + 1) =
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t)
          (nablaKRm04Field (I := I) S t k)) := rfl

/-- **The step realization for `∇ᵏRm`.**  The bundled `∇^{k+1}Rm` realizes the
canonical total covariant derivative of `∇ᵏRm`, read off from
`totalNabla0S_realizes` at rank `4 + k`.  This is the rank-uniform generalization
of `nablaRm04Field_realizes` / `nabla2Rm04Field_realizes` / `nabla3Rm04Field_realizes`. -/
theorem nablaKRm04Field_realizes
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
      (nablaKRm04Field (I := I) S t (k + 1)) := by
  rw [nablaKRm04Field_succ]
  exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (4 + k) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaKRm04Field (I := I) S t k))

end Field

/-! ## The rank-uniform bridge (all `k`)

At every point of the coordinate-frame neighbourhood of `x₀`, the level-`k`
producer array `iteratedRmComp (coordinateFrame) (realizedChr) (realizedRmBase) k`
equals the canonical bundled `∇ᵏRm` evaluated on the frame vectors.

The proof is by induction on `k`.  The base case `k = 0` is `realizedRmBase`.  The
step rewrites the inner level-`k` array as the frame-component array of the bundled
`∇ᵏRm` throughout the neighbourhood (the inductive hypothesis), then applies the
rank-uniform step bridge `covDerivStepComp_frameComp_eq` for the rank-`(4+k)` field
`∇ᵏRm` — exactly the chaining of `iteratedRmComp_two_eq_nabla2Rm04Field`. -/

section Bridge

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- **The rank-uniform `∇ᵏRm` bridge.**  For every `k`, at every point of the
coordinate-frame neighbourhood of `x₀`, the level-`k` iterated-derivative component
array equals the canonical bundled `∇ᵏRm` (`nablaKRm04Field`) evaluated on the frame
vectors.

This is the all-`k` generalization of `iteratedRmComp_one_eq_nablaRm04Field`
(`k = 1`) and `iteratedRmComp_two_eq_nabla2Rm04Field` (`k = 2`); both follow by
specialization. -/
theorem iteratedRmComp_eq_nablaKRm04Field
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) :
    ∀ (k : ℕ) {x : M}, x ∈ coordinateFrameSet (I := I) x₀ →
      ∀ n : Fin (4 + k) → CoordinateIdx (𝕜 := Real) E,
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
            (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t x n =
          nablaKRm04Field (I := I) S t k x
            (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  intro k
  induction k with
  | zero =>
      intro x hx n
      simp only [iteratedRmComp_zero, nablaKRm04Field_zero, realizedRmBase,
        frameComp0S, hframe_def]
  | succ k ih =>
      intro x hx n
      -- The inner level-`k` array equals the frame-component array of the bundled
      -- `∇ᵏRm` throughout the coordinate-frame neighbourhood (the IH).
      have hlevelk :
          (fun y : M =>
              iteratedRmComp (I := I) frame
                (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t y) =ᶠ[nhds x]
            fun y : M =>
              frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame y := by
        refine Filter.eventually_of_mem
          ((coordinateFrameSet_open (I := I) x₀).mem_nhds hx) ?_
        intro y hy
        funext m
        simpa [frameComp0S, hframe_def] using ih hy m
      -- Expand the level-`(k+1)` step.
      rw [iteratedRmComp_succ]
      -- Rewrite the `covDerivStepComp` inputs using the level-`k` identity near `x`.
      have hext :
          frameExtData (I := I) frame
              (fun y : M =>
                iteratedRmComp (I := I) frame
                  (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t y) x =
            frameExtData (I := I) frame
              (frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame) x := by
        funext m d
        simp only [frameExtData]
        refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
        exact hlevelk.mono fun y hy => congrFun hy m
      have hbase :
          iteratedRmComp (I := I) frame
              (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t x =
            frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame x :=
        hlevelk.self_of_nhds
      rw [hext, hbase]
      -- Apply the rank-uniform step bridge for the rank-`(4+k)` field `∇ᵏRm`.
      have hstep :=
        covDerivStepComp_frameComp_eq
          (I := I) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
          (nablaKRm04Field (I := I) S t (k + 1))
          (nablaKRm04Field_realizes (I := I) S t k)
          frame
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          (coordinateFrameSet_open (I := I) x₀) hx n
      -- `realizedChr` is exactly the in-frame Christoffel data.
      simpa [realizedChr, hframe_def] using hstep

/-- The `k = 1` specialization of the rank-uniform bridge recovers
`iteratedRmComp_one_eq_nablaRm04Field`. -/
theorem iteratedRmComp_one_eq_nablaKRm04Field
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (n : Fin (4 + 1) → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t x n =
      nablaKRm04Field (I := I) S t 1 x
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) :=
  iteratedRmComp_eq_nablaKRm04Field (I := I) S x₀ t 1 hx n

/-- **The rank-uniform `∇ᵏRm` bridge, arbitrary smooth local frame.**  The local-frame analogue of
`iteratedRmComp_eq_nablaKRm04Field`: for any smooth `IsLocalFrameOn` frame on an open `u`, the
level-`k` iterated-derivative component array with the solution's own in-frame Christoffel data
(`christoffelSymbolInFrame (S.family.connection ·) frame hframe`) and level-0 Riemann components
(`frameComp0S (S.base.rm04 ·) frame`) equals the canonical bundled `∇ᵏRm` (`nablaKRm04Field`)
evaluated on the frame vectors.

Proof is the same induction as the coordinate-frame version, with `coordinateFrameSet_open`/`hx`
replaced by `hu.mem_nhds hx` and the supplied `hframe`; the key step is the frame-general
`covDerivStepComp_frameComp_eq`.  This is the realization bridge the Brick 4 P3 endpoint
(`StarSum.TimeRecursion.residualStarSumLF`) consumes. -/
theorem iterRmLF_eq_nabla
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (frame : Idx → (y : M) → TangentSpace I y) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) :
    ∀ (k : ℕ) {x : M}, x ∈ u →
      ∀ n : Fin (4 + k) → Idx,
        iteratedRmComp (I := I) frame
            (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
            (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t x n =
          nablaKRm04Field (I := I) S t k x (frameTuple (I := I) frame x n) := by
  classical
  intro k
  induction k with
  | zero =>
      intro x _hx n
      simp only [iteratedRmComp_zero, nablaKRm04Field_zero, frameComp0S]
  | succ k ih =>
      intro x hx n
      -- The inner level-`k` array equals the frame-component array of the bundled `∇ᵏRm`
      -- throughout the open set `u` (the inductive hypothesis).
      have hlevelk :
          (fun y : M =>
              iteratedRmComp (I := I) frame
                (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
                (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t y) =ᶠ[nhds x]
            fun y : M =>
              frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame y := by
        refine Filter.eventually_of_mem (hu.mem_nhds hx) ?_
        intro y hy
        funext m
        simpa [frameComp0S] using ih hy m
      rw [iteratedRmComp_succ]
      have hext :
          frameExtData (I := I) frame
              (fun y : M =>
                iteratedRmComp (I := I) frame
                  (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
                  (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t y) x =
            frameExtData (I := I) frame
              (frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame) x := by
        funext m d
        simp only [frameExtData]
        refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
        exact hlevelk.mono fun y hy => congrFun hy m
      have hbase :
          iteratedRmComp (I := I) frame
              (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
              (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t x =
            frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame x :=
        hlevelk.self_of_nhds
      rw [hext, hbase]
      have hstep :=
        covDerivStepComp_frameComp_eq
          (I := I) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
          (nablaKRm04Field (I := I) S t (k + 1))
          (nablaKRm04Field_realizes (I := I) S t k)
          frame hframe hu hx n
      simpa using hstep

end Bridge

/-! ## The rank-uniform `(0,s)` Ricci identity instances

The discharged `Nabla20SRealizesAt` packages and the resulting
`Tensor0SRicciIdentityAt` instances at `s = 4 + k` for every `k`, applying
`tensor0S_ricciIdentity_of_torsionFree`.  These generalize `rm04_nabla20SRealizesAt`
/ `nablaRm04_nabla20SRealizesAt` and `rm04_ricciIdentityAt` /
`nablaRm04_ricciIdentityAt`. -/

section RicciIdentity

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- `Nabla0SSectionRealizes` for `∇ᵏRm`: the bundled `∇^{k+1}Rm` realizes the
covariant derivative of `∇ᵏRm` (the rank-`(4+k)` first-derivative realization). -/
theorem nablaKRm04_nabla0SSectionRealizes
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) (4 + k)
      (S.family.connection t) (nablaKRm04Field (I := I) S t k)
      (nablaKRm04Field (I := I) S t (k + 1)) := by
  intro y X slots
  exact nablaKRm04Field_realizes (I := I) S t k X y slots

/-- **`Nabla20SRealizesAt` for `∇ᵏRm` (s = 4 + k).**  The bundled
`∇^{k+1}Rm` / `∇^{k+2}Rm` realize the true first and second covariant derivatives of
`∇ᵏRm` at every point, discharging the hypothesis the `(0, 4+k)` Ricci identity
needs.  Rank-uniform generalization of `rm04_nabla20SRealizesAt` (`k = 0`) and
`nablaRm04_nabla20SRealizesAt` (`k = 1`). -/
theorem nablaKRm04_nabla20SRealizesAt
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (x : M) :
    DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) (4 + k)
      (S.family.connection t) (nablaKRm04Field (I := I) S t k)
      (nablaKRm04Field (I := I) S t (k + 1)) x
      (nablaKRm04Field (I := I) S t (k + 2) x) := by
  refine ⟨nablaKRm04_nabla0SSectionRealizes (I := I) S t k, ?_⟩
  intro X slots
  exact nablaKRm04Field_realizes (I := I) S t (k + 1) X x slots

/-- **The `(0, 4+k)` Ricci identity for `∇ᵏRm`.**  The Ricci-identity commutator of
the bundled `∇^{k+2}Rm` equals the slotwise curvature action on `∇ᵏRm`, at every
regular time and point — produced from the discharged realization package above.

Rank-uniform generalization of `rm04_ricciIdentityAt` (`k = 0`) and
`nablaRm04_ricciIdentityAt` (`k = 1`). -/
theorem nablaKRm04_ricciIdentityAt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (nablaKRm04Field (I := I) S (t : Real) k x)
      (nablaKRm04Field (I := I) S (t : Real) (k + 2) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S hS t)
    simpa [DifferentialGeometry.Integral.Connection.IsTorsionFreeAt] using htf x
  exact DifferentialGeometry.Integral.Connection.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (nablaKRm04Field (I := I) S (t : Real) k)
    (nablaKRm04Field (I := I) S (t : Real) (k + 1))
    (nablaKRm04Field (I := I) S (t : Real) k x)
    (nablaKRm04Field (I := I) S (t : Real) (k + 1) x)
    (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl
    (nablaKRm04_nabla20SRealizesAt (I := I) S (t : Real) k x) htor

end RicciIdentity

end DifferentialGeometry.PDE.RicciFlow
