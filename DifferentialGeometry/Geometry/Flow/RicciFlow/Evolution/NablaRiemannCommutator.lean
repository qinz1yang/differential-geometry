import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The spatial Laplacian–covariant-derivative commutator `[Δ, ∇] Rm = Rm ∗ ∇Rm`

This file builds the **spatial commutator identity** that the `k = 1`
Bernstein–Bando–Shi curvature-derivative producer
(`Evolution/NablaRiemannHeat.lean`, `Evolution/MultiNormHeat.lean`) needs in its
heat-residual reaction term.  It is the geometric heart of the `k = 1` estimate:
the rough Laplacian of `∇Rm` differs from the covariant derivative of the rough
Laplacian of `Rm` by an explicit `Rm ∗ ∇Rm` curvature term.

It is derived **with no axiomatized commutator** from the two `(0, s)` Ricci
identities packaged in `Evolution/RmRealizationBridge.lean`:

* `rm04_ricciIdentityAt` — the `(0, 4)` Ricci identity for `Rm`
  (`nabla2Rm04Field` antisymmetrized in its two derivative slots = curvature
  action on `Rm`);
* `nablaRm04_ricciIdentityAt` — the `(0, 5)` Ricci identity for `∇Rm`
  (`nabla3Rm04Field` antisymmetrized in its first two derivative slots =
  curvature action on `∇Rm`).

## The operator identity (worked at the chart centre, pointwise)

Writing `∇³Rm = nabla3Rm04Field` (rank `7`, slots `(d₀, d₁, d₂, i, j, k, l)`
with `d₀` the **outer**, `d₁` the **middle**, `d₂` the **inner** derivative
direction and `(i,j,k,l)` the four `Rm` slots) the Jacobi-style telescoping

`∇_a∇_b∇_c − ∇_c∇_a∇_b = (∇_a∇_b∇_c − ∇_a∇_c∇_b) + (∇_a∇_c∇_b − ∇_c∇_a∇_b)`
`                       = ∇_a([∇_b, ∇_c] Rm) + [∇_a, ∇_c](∇_b Rm)`

splits the third-derivative antisymmetrization into

* `∇_a([∇_b, ∇_c] Rm)` — the covariant derivative of the `(b,c)` curvature
  commutator on `Rm` (`= ∇(Rm ∗ Rm) = Rm ∗ ∇Rm`); component-wise this is the
  `nabla3Rm04Field` difference `nabla3(a,b,c) − nabla3(a,c,b)`, whose bracketed
  factor `[∇_b, ∇_c] Rm` is `rm04_ricciIdentityAt`;
* `[∇_a, ∇_c](∇_b Rm)` — the curvature commutator acting on `∇Rm`
  (`= Rm ∗ ∇Rm`); this is **exactly** `nablaRm04_ricciIdentityAt` applied with
  derivative directions `a, c` and tensor slots `(b, i, j, k, l)`.

Tracing the outer pair `(a, b)` against the inverse metric `g^{ab}` and using
metric parallelism (so `∇` and `Δ` pass through the trace) turns the left side
into the **spatial commutator**

`[Δ, ∇_c] Rm = g^{ab}(∇_a∇_b∇_c − ∇_c∇_a∇_b) Rm = Δ(∇Rm) − ∇(ΔRm)`.

## What this file produces

* `nabla3FrameTuple` — the `Fin 7` frame tuple assembling three derivative
  directions and a `Fin 4` `Rm`-slot multi-index;
* `nablaLapCommReactionTerm` — the **explicit `Rm ∗ ∇Rm` array**: the sum of the
  two curvature contributions above, one a `nabla3Rm04Field` antisymmetrization
  (`∇([∇,∇]Rm)`) and one the `nablaRm04_ricciIdentityAt` curvature action
  (`[∇,∇]∇Rm`);
* `nablaLapComm_pointwise` — the **per-direction** spatial commutator: for every
  pair of frame directions `a, b`,
  `nabla3(a,b,c) − nabla3(c,a,b) = nablaLapCommReactionTerm a b c rest`,
  derived from the telescoping identity and `nablaRm04_ricciIdentityAt`;
* `nablaLapComm_trace` — the **`g^{ab}`-traced** form
  `Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_{a,b} g^{ab} · nablaLapCommReactionTerm a b c rest`,
  the shape a downstream assembler pairs against `∇Rm` to obtain the
  `nablaRmReactionInFrame` heat-residual reaction;
* `nablaLapComm_orthonormalTrace` — the same in the orthonormal-frame `g^{ab}=δ`
  convention of the producer, where the trace collapses to `Σ_a`.

Everything is at the **component/scalar level** demanded by the Ricci-identity
interface (`curvatureAction0SAt` is a scalar); there is no field-level `⋆` or
`totalNablaRS`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## Frame tuples for `∇³Rm`

`nabla3Rm04Field S t x` is a rank-`7` covariant tensor: the first three slots are
the (outer, middle, inner) derivative directions and the last four are the `Rm`
slots.  `nabla3FrameTuple` assembles such an input from three frame directions
`d₀ d₁ d₂` and a `Fin 4` `Rm`-slot multi-index `m`, in the exact
`metricTraceInput` shape the `(0, 5)` Ricci identity consumes:
`d₀ :: d₁ :: (d₂ :: m-frame-tuple)`. -/

/-- The `Fin 5` "tensor-slot" tuple for the `(0, 5)` Ricci identity applied to
`∇Rm`: the inner derivative direction `d₂` followed by the four `Rm` slots. -/
def nabla3InnerSlots
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 5 → TangentSpace I x :=
  Fin.cons (frame d₂ x) (frameTuple (I := I) frame x m)

/-- The `Fin 7` frame tuple feeding `nabla3Rm04Field`: derivative directions
`d₀, d₁, d₂` in the first three slots, then the four `Rm` slots selected by the
multi-index `m`.  Equivalently `d₀ :: d₁ :: d₂ :: (frame ∘ m)`. -/
def nabla3FrameTuple
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 7 → TangentSpace I x :=
  metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
    (nabla3InnerSlots (I := I) frame x d₂ m)

@[simp] theorem nabla3FrameTuple_eq_metricTraceInput
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3FrameTuple (I := I) frame x d₀ d₁ d₂ m =
      metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
        (nabla3InnerSlots (I := I) frame x d₂ m) := rfl

/-! ## The explicit `Rm ∗ ∇Rm` reaction array and the per-direction commutator

For derivative directions `a, b, c` (with `(a, b)` the trace pair eventually
contracted by `g^{ab}` and `c` the free `∇`-direction) and a `Fin 4` `Rm`-slot
multi-index `m`, the spatial commutator reaction is the sum of the two
`Rm ∗ ∇Rm` contributions of the operator identity:

* `nabla3(a,b,c) − nabla3(a,c,b)`, the `∇_a([∇_b,∇_c] Rm)` term (`∇(Rm ∗ Rm)`);
* the `(0, 5)` curvature action `[∇_a, ∇_c] (∇_b Rm)` on `∇Rm` (`Rm ∗ ∇Rm`). -/

/-- The explicit `Rm ∗ ∇Rm` reaction array at the chart centre `x₀`, the sum of
the two curvature contributions of the operator identity
`∇_a∇_b∇_c − ∇_c∇_a∇_b = ∇_a([∇_b,∇_c]Rm) + [∇_a,∇_c](∇_b Rm)`.  The first
summand is the `nabla3Rm04Field` antisymmetrization realizing `∇_a([∇_b,∇_c]Rm)`
(`= ∇(Rm ∗ Rm)`); the second is the `(0,5)` curvature action on `∇Rm`
(`= Rm ∗ ∇Rm`, the content of `nablaRm04_ricciIdentityAt`). -/
def nablaLapCommReactionTerm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  (nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m)) +
    curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)

/-- **The per-direction spatial commutator identity.**  At the chart centre `x₀`,
for every pair of trace directions `a, b`, free direction `c`, and `Rm`-slot
multi-index `m`, the third-derivative antisymmetrization

`(∇_a∇_b∇_c − ∇_c∇_a∇_b) Rm = nabla3(a,b,c) − nabla3(c,a,b)`

equals the explicit `Rm ∗ ∇Rm` reaction array `nablaLapCommReactionTerm`.

Derived from the Jacobi telescoping `X − Y = (X − Z) + (Z − Y)` and the `(0, 5)`
Ricci identity `nablaRm04_ricciIdentityAt` (which discharges the `Z − Y` bracket
as the curvature action on `∇Rm`).  No commutator is assumed. -/
theorem nablaLapComm_pointwise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) =
      nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m := by
  classical
  -- The `(0, 5)` Ricci identity for `∇Rm`, specialized to the directions `a, c`
  -- and the inner slots `(b, m)`.  Its two metric-trace inputs are exactly the
  -- `nabla3` permutations `a :: c :: (b :: m)` and `c :: a :: (b :: m)`.
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S hS t x₀
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)
  -- `hR2 : nabla3(a,c,b) − nabla3(c,a,b) = curvatureAction …` (in metricTraceInput form).
  -- Unfold the reaction term and the frame tuples to the bare metric-trace inputs,
  -- so the goal is a pure linear identity over `nabla3` values closed by `hR2`.
  rw [nablaLapCommReactionTerm]
  simp only [nabla3FrameTuple, nabla3InnerSlots] at hR2 ⊢
  -- Telescoping `X − Y = (X − Z) + (Z − Y)` with the middle permutation `Z`.
  linarith [hR2]

/-! ## The `g^{ab}`-traced spatial commutator

Contracting the trace pair `(a, b)` against an arbitrary inverse-metric component
array `gInv` turns the per-direction identity into the spatial commutator
`Δ(∇Rm) − ∇(ΔRm)` paired against an explicit `Rm ∗ ∇Rm` array.

* `roughLapNablaRmComp` traces the **outer** derivative pair of `∇³Rm`, the
  rough Laplacian of `∇Rm`: `Δ(∇Rm)(c, m) = g^{ab} ∇_a∇_b∇_c Rm`.
* `nablaRoughLapRmComp` traces the **inner** derivative pair of `∇³Rm`, the
  covariant derivative of the rough Laplacian of `Rm`:
  `∇(ΔRm)(c, m) = g^{ab} ∇_c∇_a∇_b Rm` (using metric parallelism, so `∇`
  passes through the `g^{ab}` trace). -/

/-- The component-level rough Laplacian of `∇Rm` at the chart centre: the
`g^{ab}`-trace of the **outer** derivative pair of `∇³Rm`.  This is the producer's
`Δ(∇Rm)(c, m)`. -/
def roughLapNablaRmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m)

/-- The component-level covariant derivative of the rough Laplacian of `Rm` at the
chart centre: the `g^{ab}`-trace of the **inner** derivative pair of `∇³Rm`.  This
is the producer's `∇(ΔRm)(c, m)`. -/
def nablaRoughLapRmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m)

/-- **The `g^{ab}`-traced spatial commutator identity.**  At the chart centre, for
any inverse-metric array `gInv`,

`Δ(∇Rm)(c, m) − ∇(ΔRm)(c, m) = Σ_{a,b} g^{ab} · nablaLapCommReactionTerm a b c m`,

i.e. the spatial commutator `[Δ, ∇_c] Rm` equals the `g^{ab}`-trace of the
explicit `Rm ∗ ∇Rm` reaction array.  This is the form a downstream assembler
pairs against `∇Rm` (as `nablaRmReactionInFrame`'s heat-residual reaction).

Obtained by summing the per-direction identity `nablaLapComm_pointwise` weighted
by `gInv a b`. -/
theorem nablaLapComm_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    roughLapNablaRmComp (I := I) S (t : Real) x₀ gInv c m -
        nablaRoughLapRmComp (I := I) S (t : Real) x₀ gInv c m =
      ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
        gInv a b * nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m := by
  classical
  rw [roughLapNablaRmComp, nablaRoughLapRmComp]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub, nablaLapComm_pointwise (I := I) S hS t x₀ a b c m]

/-! ## The orthonormal-frame form (producer convention)

In the orthonormal frame `g^{ab} = δ^{ab}` of the producer
(`InverseMetricOrthonormalAt`), the double `g^{ab}` trace collapses to the single
diagonal sum `Σ_a`, matching `compNormSq*`/`nablaRmReactionInFrame`. -/

/-- **The orthonormal-frame spatial commutator identity.**  When the inverse
metric is the Kronecker delta (the producer's `InverseMetricOrthonormalAt`
convention), the spatial commutator collapses to the diagonal trace

`Δ(∇Rm)(c, m) − ∇(ΔRm)(c, m) = Σ_a nablaLapCommReactionTerm a a c m`.

This is the exact orthonormal shape the `k = 1` producer
(`nablaRm04NormHeatBoundOn_of_components`, via the heat residual `(∂ₜ − Δ)∇Rm`)
consumes after pairing against `∇Rm`. -/
theorem nablaLapComm_orthonormalTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (horth : ∀ i j : CoordinateIdx (𝕜 := Real) E, gInv i j = if i = j then 1 else 0)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    roughLapNablaRmComp (I := I) S (t : Real) x₀ gInv c m -
        nablaRoughLapRmComp (I := I) S (t : Real) x₀ gInv c m =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a a c m := by
  classical
  rw [nablaLapComm_trace (I := I) S hS t x₀ gInv c m]
  -- Collapse the inner `b`-sum against the Kronecker delta `gInv a b`.
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, one_mul]
  · intro b _ hb
    rw [horth a b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## Identification of the two reaction summands (for the assembler's bound)

The reaction array splits into the two `Rm ∗ ∇Rm` pieces of the operator
identity.  These lemmas record each piece as a `∇³Rm` antisymmetrization, the
form a downstream assembler bounds by Cauchy–Schwarz.

* `nablaLapComm_secondTerm_eq` certifies the **second** summand
  (`[∇_a, ∇_c](∇_b Rm)`) is the `nabla3` antisymmetrization
  `nabla3(a,c,b) − nabla3(c,a,b)` (the content of `nablaRm04_ricciIdentityAt`),
  manifestly `Rm ∗ ∇Rm` (a curvature factor contracted into `∇Rm`).
* `nablaLapCommReactionTerm_eq_nabla3` re-expresses the whole reaction array as a
  pure `∇³Rm` antisymmetrization difference, the rawest concrete form.

The **first** summand `nabla3(a,b,c) − nabla3(a,c,b)` is `∇_a([∇_b, ∇_c] Rm)`
by construction (`nabla3 = ∇(nabla2)` and `rm04_ricciIdentityAt`); its further
expansion into separated `∇Rm ∗ Rm + Rm ∗ ∇Rm` factors is the remaining wall —
see the file footer. -/

/-- The second reaction summand is the `(0, 5)` curvature commutator value on
`∇Rm`, i.e. the `∇³Rm` antisymmetrization `nabla3(a,c,b) − nabla3(c,a,b)`.  This
is `nablaRm04_ricciIdentityAt` read right-to-left. -/
theorem nablaLapComm_secondTerm_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
        (nablaRm04Field (I := I) S (t : Real) x₀)
        (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
        (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) =
      nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) := by
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S hS t x₀
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)
  simp only [nabla3FrameTuple, nabla3InnerSlots] at hR2 ⊢
  exact hR2.symm

/-- The whole reaction array, as a pure `∇³Rm` antisymmetrization difference:
`nablaLapCommReactionTerm a b c m = nabla3(a,b,c) − nabla3(c,a,b)`.  This is the
rawest concrete `Rm ∗ ∇Rm` component form and is exactly the left-hand side of
`nablaLapComm_pointwise`. -/
theorem nablaLapCommReactionTerm_eq_nabla3
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m =
      nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) :=
  (nablaLapComm_pointwise (I := I) S hS t x₀ a b c m).symm

/-! ## Produced shape and the remaining wall

**Produced (sorry-free, no axiomatized commutator).**  At the chart centre `x₀`,
for a Ricci-flow solution at a regular time:

* `nablaLapComm_pointwise` :
  `∇³Rm(a,b,c) − ∇³Rm(c,a,b) = nablaLapCommReactionTerm a b c m`
  — the per-direction spatial commutator, from telescoping +
  `nablaRm04_ricciIdentityAt`.
* `nablaLapComm_trace` :
  `Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_{a,b} g^{ab} · nablaLapCommReactionTerm a b c m`
  — the `g^{ab}`-traced form, summing the per-direction identity.
* `nablaLapComm_orthonormalTrace` :
  the orthonormal `g^{ab}=δ` collapse `= Σ_a nablaLapCommReactionTerm a a c m`,
  the producer's convention.

`nablaLapCommReactionTerm a b c m` is the explicit `Rm ∗ ∇Rm` array, the sum of:
1. `∇_a([∇_b,∇_c] Rm) = ∇³Rm(a,b,c) − ∇³Rm(a,c,b)` (`= ∇(Rm ∗ Rm)`), and
2. `[∇_a,∇_c](∇_b Rm) = ∇³Rm(a,c,b) − ∇³Rm(c,a,b)` (`= Rm ∗ ∇Rm`, the curvature
   action `curvatureAction0SAt (rm13) (∇Rm) …`, `nablaLapComm_secondTerm_eq`).

**Cited lemmas:** `nablaRm04_ricciIdentityAt`, `rm04_ricciIdentityAt` (for the
meaning of summand 1), and the bundled fields/bridges of
`Evolution/RmRealizationBridge.lean`.

**Remaining wall (reported, not worked around).**  Expanding summand 1,
`∇_a([∇_b,∇_c] Rm)`, into *separated* `∇Rm ∗ Rm + Rm ∗ ∇Rm` component factors
needs the **bundled covariant-derivative Leibniz rule for a curvature action**,
`∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm`.  Concretely, one must differentiate the
scalar field `y ↦ curvatureAction0SAt (rm13 y) (Rm04 y) (frame b)(frame c)(m)`
covariantly: the `extDerivFun` part is handled by `extDerivFun_sub` +
`rm04_ricciIdentityAt` as a *field* equation, but the Christoffel-correction part
of the `nabla3 = ∇(nabla2)` realization does **not** cancel between the
`(b,c)` and `(c,b)` slot orderings, so `∇³Rm(a,b,c) − ∇³Rm(a,c,b)` is the
covariant (not merely the `extDerivFun`) derivative of the curvature-action
tensor field.  No `∇(curvatureAction)` / `∇(Rm ∗ Rm)` Leibniz lemma exists in the
tree (searched: `Synthetic/Algebra/TensorAlgebra.lean`, the `CovGradRoughLap`
and `RicciIdentity` namespaces).  Summand 1 is therefore left as the explicit
`∇³Rm` antisymmetrization (a concrete component array of the correct `Rm ∗ ∇Rm`
degree).  The downstream assembler can either (a) bound summand 1 directly via
the curvature-action route once that Leibniz lemma is added, or (b) carry it as
the `∇³Rm`-difference and bound it together with the heat-residual machinery. -/

end DifferentialGeometry.PDE.RicciFlow
