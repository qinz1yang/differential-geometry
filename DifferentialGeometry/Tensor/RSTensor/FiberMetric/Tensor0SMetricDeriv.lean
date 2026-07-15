import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The general Bochner-type time derivative of a covariant-tensor norm

This file proves the **rank-uniform, intrinsic, moving-metric** time derivative of
the squared fibre norm `normSq0S g x s T` of a `(0,s)` tensor — the abstraction
that closes the standing per-case raw time-derivative hypothesis of the
Bernstein–Bando–Shi architecture (`Rm04NormRawDerivativeEquationOn` for `k = 0`,
and the `k = 1` / all-`k` analogues) in one frame-free lemma.

The intrinsic squared norm equals, in any tangent basis with `MetricInverseInBasis`,
the `gInv`-raised contraction (`normSq0S_eq_coord`):

`normSq0S (g t) x s (T t) = coordInner0S (gInv t) (T t) (T t) basis`
`  = Σ_{I0,J0 : Fin s → Idx} (∏_a gInv t (I0 a)(J0 a)) · (T t)(basis∘I0) · (T t)(basis∘J0)`.

Differentiating this finite sum in `t` by the product rule gives three groups of
terms:

* the `gInv`-factor derivatives, assembled into the **metric-derivative term**
  `coordContractDt`, the derivative of the contraction through the inverse metric;
* the two `T`-factor derivatives, which assemble into
  `inner0S (∂ₜT) T + inner0S T (∂ₜT) = 2 · inner0S (∂ₜT) T`.

So, with the pointwise time derivatives `∂ₜgInv` (inverse-metric component
derivatives) and `∂ₜT` (tensor component derivatives) supplied as
`HasDerivWithinAt` hypotheses:

`∂ₜ ( normSq0S (g t) x s (T t) ) = (metric term in ∂ₜgInv) + 2 · inner0S (g t) (∂ₜT) (T)`.

The statement is **completely general**: `T` and `g` are arbitrary time-dependent;
nothing here depends on curvature, metric compatibility, or a Ricci-flow
hypothesis.  The metric term is the inverse-metric-derivative contraction; under
Ricci flow `∂ₜgInv = 2 gInv gInv Ric` (`inverseMetric_derivative_solve`) it becomes
the `Ric ∗ T²` reaction piece — the instantiation recorded at the foot of the file.

This is the `MultiNormHeat.lean:158` fixed-metric product rule
(`hasDerivWithinAt_compNormSqMulti`, the `∂ₜgInv = 0` specialisation) generalised
to a moving metric: it mirrors that product-rule structure and **adds** the metric
term.

`#print axioms` for every public theorem is `[propext, Classical.choice, Quot.sound]`.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Pure coordinate contraction of component arrays

We work first at the assumption-free level of real component arrays
`(Fin s → Idx) → Real` and inverse-metric components `Idx → Idx → Real`, so the
product-rule calculation carries no geometric content.  `coordContract` is the
`gInv`-raised contraction; it specialises to `coordInner0S` on tensor components. -/

section Coord

variable {Idx : Type*} [Fintype Idx]

/-- The `gInv`-raised contraction of two rank-`s` real component arrays,
`Σ_{I0,J0} (∏_a gInv (I0 a)(J0 a)) · cA I0 · cB J0`.  This is `coordInner0S`
written on raw component arrays; see `coordContract_eq_coordInner0S`. -/
def coordContract {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 * cB J0

/-- The **metric-derivative term**: the derivative of `coordContract` through the
inverse metric, with each `gInv` factor differentiated in turn,
`Σ_{I0,J0} (Σ_b (∏_{a≠b} gInv (I0 a)(J0 a)) · gInvDt (I0 b)(J0 b)) · cA I0 · cB J0`.
This is the coordinate form of the `∂ₜgInv`-contraction `−Σ_a ⟨∂ₜg raised on slot
a⟩(A,B)`. -/
def coordContractDt {s : Nat}
    (gInv gInvDt : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∑ b : Fin s,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
          gInvDt (I0 b) (J0 b)) *
      cA I0 * cB J0

/-- **The product-rule time derivative of the coordinate contraction.**

For time-dependent inverse-metric components `gInv t` and rank-`s` component arrays
`cA t`, `cB t`, with the pointwise derivatives `gInvDt`, `cAdt`, `cBdt` supplied as
`HasDerivWithinAt` data, the contraction `t ↦ coordContract (gInv t) (cA t) (cB t)`
is differentiable with derivative

`coordContractDt + coordContract gInv cAdt cB + coordContract gInv cA cBdt`,

i.e. the metric-derivative term plus the two component-derivative contractions.
Pure real product-rule algebra on a finite double sum; no geometric hypothesis. -/
theorem hasDerivWithinAt_coordContract {s : Nat}
    {u : Set Real} {t : Real}
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt : Idx -> Idx -> Real)
    (cA cB : Real -> (Fin s -> Idx) -> Real)
    (cAdt cBdt : (Fin s -> Idx) -> Real)
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hcA : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt (fun r : Real => cA r I0) (cAdt I0) u t)
    (hcB : ∀ J0 : Fin s -> Idx,
      HasDerivWithinAt (fun r : Real => cB r J0) (cBdt J0) u t) :
    HasDerivWithinAt
      (fun r : Real => coordContract (gInv r) (cA r) (cB r))
      (coordContractDt (gInv t) gInvDt (cA t) (cB t) +
        coordContract (gInv t) cAdt (cB t) +
        coordContract (gInv t) (cA t) cBdt)
      u t := by
  classical
  unfold coordContract coordContractDt
  -- The whole thing is a double finite sum of per-`(I0, J0)` summands; the value
  -- splits termwise, so it suffices to differentiate each summand and pair the
  -- derivative values back up.
  rw [show
      (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv t (I0 a) (J0 a)) *
                gInvDt (I0 b) (J0 b)) *
            cA t I0 * cB t J0) +
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, gInv t (I0 a) (J0 a)) * cAdt I0 * cB t J0) +
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, gInv t (I0 a) (J0 a)) * cA t I0 * cBdt J0) =
      ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
        ((∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv t (I0 a) (J0 a)) *
                gInvDt (I0 b) (J0 b)) *
            cA t I0 * cB t J0 +
          ((∏ a : Fin s, gInv t (I0 a) (J0 a)) * cAdt I0 * cB t J0 +
            (∏ a : Fin s, gInv t (I0 a) (J0 a)) * cA t I0 * cBdt J0)) by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    ring]
  refine HasDerivWithinAt.fun_sum ?_
  intro I0 _
  refine HasDerivWithinAt.fun_sum ?_
  intro J0 _
  -- Differentiate the single summand `P r * cA r I0 * cB r J0` with
  -- `P r = ∏_a gInv r (I0 a)(J0 a)`.
  have hP :
      HasDerivWithinAt
        (fun r : Real => ∏ a : Fin s, gInv r (I0 a) (J0 a))
        (∑ b : Fin s,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv t (I0 a) (J0 a)) *
            gInvDt (I0 b) (J0 b))
        u t := by
    have h :=
      HasDerivWithinAt.fun_finset_prod
        (u := (Finset.univ : Finset (Fin s)))
        (f := fun a r => gInv r (I0 a) (J0 a))
        (f' := fun a => gInvDt (I0 a) (J0 a))
        (x := t) (s := u)
        (fun a _ => hgInv (I0 a) (J0 a))
    simpa [smul_eq_mul, mul_comm] using h
  -- Product rule: `(P · cA) · cB`.
  have hprodA := hP.mul (hcA I0)
  have hfull := hprodA.mul (hcB J0)
  refine hfull.congr_deriv ?_
  -- Match the Leibniz value to the named summand value (beta-reduce the
  -- pointwise products evaluated at `t`, then it is pure ring algebra).
  simp only [Pi.mul_apply]
  ring

/-- `coordContract` on tensor components is exactly the metric coordinate
contraction `coordInner0S`. -/
theorem coordContract_eq_coordInner0S {s : Nat} {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordContract gInv
        (fun I0 => tensor0SComponent (I := I) A (fun i => basis i) I0)
        (fun J0 => tensor0SComponent (I := I) B (fun i => basis i) J0) =
      coordInner0S (I := I) (x := x) s gInv A B basis := by
  rfl

/-! ### The metric term under the Ricci-flow inverse-metric derivative

When `gInvDt` is the inverse-metric time derivative of a Ricci flow, it satisfies
the algebraic relation produced by `inverseMetric_derivative_solve`:
`gInvDt i j = 2 · Σ_{p,q} gInv i p · gInv j q · ric p q`
(the raised Ricci `2 Ric^{ij}`, coming from `∂ₜg = −2 Ric`).  Substituted into the
metric-derivative term, this turns the abstract `coordContractDt` into the explicit
**Ricci reaction** `ricReactionContract`: on every slot `b`, the inverse metric on
that slot is replaced by a doubled Ricci-raised contraction.  This is pure algebra
in an abstract `ric` (no curvature hypothesis); the geometric content — that this
`ric` is the Ricci tensor and the relation holds — is exactly what
`inverseMetric_derivative_solve` supplies for a flow. -/

/-- The Ricci reaction contraction obtained from the metric-derivative term under
Ricci flow: twice the sum over slots `b` of the contraction with the `b`-slot
inverse metric replaced by the Ricci-raised `Σ_{p,q} gInv (I0 b) p · gInv (J0 b) q
· ric p q`. -/
def ricReactionContract {s : Nat}
    (gInv ric : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) : Real :=
  2 * ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∑ b : Fin s,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
          (∑ p : Idx, ∑ q : Idx, gInv (I0 b) p * gInv (J0 b) q * ric p q)) *
      cA I0 * cB J0

/-- **The metric-derivative term is the Ricci reaction under Ricci flow.**  If the
inverse-metric time derivative satisfies the Ricci-flow relation
`gInvDt i j = 2 · Σ_{p,q} gInv i p · gInv j q · ric p q`
(the conclusion of `inverseMetric_derivative_solve`), then the abstract
metric-derivative term `coordContractDt` equals the explicit Ricci reaction
`ricReactionContract`.  Pure finite-sum algebra. -/
theorem coordContractDt_eq_ricReactionContract {s : Nat}
    (gInv gInvDt ric : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real)
    (hflow : ∀ i j : Idx,
      gInvDt i j = 2 * (∑ p : Idx, ∑ q : Idx, gInv i p * gInv j q * ric p q)) :
    coordContractDt gInv gInvDt cA cB =
      ricReactionContract gInv ric cA cB := by
  classical
  unfold coordContractDt ricReactionContract
  -- Substitute the flow relation slotwise inside the metric-derivative term, then
  -- the leading `2` factors out of the whole double sum by `Finset.mul_sum`.
  have hsub :
      (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                gInvDt (I0 b) (J0 b)) *
            cA I0 * cB J0) =
        ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          2 *
            ((∑ b : Fin s,
                (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                  (∑ p : Idx, ∑ q : Idx, gInv (I0 b) p * gInv (J0 b) q * ric p q)) *
              cA I0 * cB J0) := by
    refine Finset.sum_congr rfl fun I0 _ => ?_
    refine Finset.sum_congr rfl fun J0 _ => ?_
    -- Rewrite each slot via the flow relation, then pull `2` out of the slot sum.
    rw [show
        (∑ b : Fin s,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
              gInvDt (I0 b) (J0 b)) =
          ∑ b : Fin s,
            2 *
              ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                (∑ p : Idx, ∑ q : Idx, gInv (I0 b) p * gInv (J0 b) q * ric p q)) from ?_]
    · rw [← Finset.mul_sum]; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hflow (I0 b) (J0 b)]; ring
  rw [hsub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I0 _ => ?_
  rw [Finset.mul_sum]

end Coord

/-! ## The intrinsic moving-metric time derivative of `normSq0S`

We now restate the coordinate product rule through the intrinsic fibre metric.
Working at a fixed point `x` in a fixed tangent basis (so the fibre type
`Tensor0SSpace s I x` is constant in `t`), with a time-dependent inverse-metric
component family `gInv t` that is genuinely the inverse of `g t` at each time
(`MetricInverseInBasis (g t) x basis (gInv t)`), the intrinsic norm
`normSq0S (g t) x s (T t)` equals `coordInner0S (gInv t) (T t) (T t) basis`, and
differentiating gives the metric term plus `2 · inner0S (∂ₜT) T`. -/

section Intrinsic

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **The general Bochner-type time derivative of a covariant-tensor norm.**

Let `x : M`, let `basis` be a tangent basis at `x`, let `g : Real → SmoothMetric`
be a time-dependent metric whose inverse components in `basis` are `gInv t`
(genuinely two-sided inverse at the base time `t`, `hinv`), and let
`T : Real → Tensor0SSpace s I x` be a time-dependent `(0,s)` tensor at `x`.  Suppose

* the inverse-metric components are differentiable in time: for all `i j`,
  `∂ₜ (gInv · i j) = gInvDt i j` (`hgInv`);
* the tensor components are differentiable in time: for all slot tuples `I0`,
  `∂ₜ ((T ·)(basis∘I0)) = Tdt I0` (`hT`).

Then the intrinsic squared fibre norm is differentiable in time with

`∂ₜ (normSq0S (g t) x s (T t)) =`
`    coordContractDt (gInv t) gInvDt (comps (T t)) (comps (T t))`
`  + coordContract (gInv t) Tdt (comps (T t))`
`  + coordContract (gInv t) (comps (T t)) Tdt`,

the metric-derivative term (the `∂ₜgInv`-contraction) plus the two
component-derivative contractions.  Completely general in `T` and `g`; no
curvature, metric-compatibility, or flow hypothesis enters.  The cleaner
"`metric term + 2 · inner0S (∂ₜT) (T)`" packaging is `hasDerivWithinAt_normSq0S`
below, which uses the symmetry of `inner0S`. -/
theorem hasDerivWithinAt_normSq0S_coord {s : Nat} {x : M}
    {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt : Idx -> Idx -> Real)
    (T : Real -> Tensor0SSpace s I x)
    (Tdt : (Fin s -> Idx) -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gInv r))
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hT : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) u t) :
    HasDerivWithinAt
      (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (coordContractDt (gInv t) gInvDt
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        coordContract (gInv t) Tdt
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        coordContract (gInv t)
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0) Tdt)
      u t := by
  classical
  -- Rewrite the intrinsic norm as the coordinate contraction at every time.
  have hpt : ∀ r : Real,
      normSq0S (I := I) (g r) x s (T r) =
        coordContract (gInv r)
          (fun I0 => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T r) (fun i => basis i) J0) := by
    intro r
    rw [coordContract_eq_coordInner0S (I := I) (gInv r) (T r) (T r) basis]
    rw [normSq0S_eq_coord (I := I) (g r) x s basis (gInv r) (hinvAll r) (T r)]
  -- Differentiate the coordinate contraction by the product rule.
  have hderiv :=
    hasDerivWithinAt_coordContract (s := s) (u := u) (t := t)
      (gInv := gInv) (gInvDt := gInvDt)
      (cA := fun r I0 => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
      (cB := fun r J0 => tensor0SComponent (I := I) (T r) (fun i => basis i) J0)
      (cAdt := Tdt) (cBdt := Tdt)
      hgInv hT hT
  -- Transport across the pointwise norm = contraction identity.
  refine hderiv.congr ?_ ?_
  · intro r _; exact hpt r
  · exact hpt t

/-- **The general Bochner-type time derivative of a covariant-tensor norm, in
intrinsic inner-product form.**

This is `hasDerivWithinAt_normSq0S_coord` with the two component-derivative
contractions collapsed, using the symmetry of the fibre inner product, to the
single term `2 · inner0S (g t) (∂ₜT) (T)`:

`∂ₜ (normSq0S (g t) x s (T t)) = (metric term) + 2 · inner0S (g t) x s (∂ₜT) (T)`,

where the metric term `coordContractDt (gInv t) gInvDt …` is the
inverse-metric-derivative contraction (`= −Σ_a ⟨∂ₜg raised on slot a⟩(T,T)`; under
Ricci flow `∂ₜgInv = 2 gInv gInv Ric`, it is the `Ric ∗ T²` reaction).

The tensor `∂ₜT` is supplied as the abstract fibre element `Tdot` whose components
in `basis` are the supplied component derivatives `Tdt` (`hTdot`).  Completely
general in `T`, `g`, `Tdot`; no curvature/compatibility/flow hypothesis. -/
theorem hasDerivWithinAt_normSq0S {s : Nat} {x : M}
    {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt : Idx -> Idx -> Real)
    (T : Real -> Tensor0SSpace s I x)
    (Tdt : (Fin s -> Idx) -> Real)
    (Tdot : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gInv r))
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hT : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) u t)
    (hTdot : ∀ I0 : Fin s -> Idx,
      tensor0SComponent (I := I) Tdot (fun i => basis i) I0 = Tdt I0) :
    HasDerivWithinAt
      (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (coordContractDt (gInv t) gInvDt
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        2 * inner0S (I := I) (g t) x s Tdot (T t))
      u t := by
  classical
  -- Start from the coordinate form.
  have hderiv :=
    hasDerivWithinAt_normSq0S_coord (s := s) (u := u) (t := t)
      g gInv gInvDt T Tdt basis hinvAll hgInv hT
  refine hderiv.congr_deriv ?_
  -- The two component-derivative contractions both equal `inner0S Tdot (T t)`.
  -- `coordContract gInv Tdt (comps (T t)) = coordInner0S gInv Tdot (T t) basis
  --   = inner0S Tdot (T t)`; symmetrically for the other order via inner symmetry.
  have hcompTdot :
      (fun I0 => tensor0SComponent (I := I) Tdot (fun i => basis i) I0) = Tdt := by
    funext I0; exact hTdot I0
  -- Left contraction `coordContract gInv Tdt (comps T) = inner0S Tdot (T t)`.
  have hleft :
      coordContract (gInv t) Tdt
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) =
        inner0S (I := I) (g t) x s Tdot (T t) := by
    rw [← hcompTdot]
    rw [coordContract_eq_coordInner0S (I := I) (gInv t) Tdot (T t) basis]
    rw [← inner0S_eq_coord (I := I) (g t) x s basis (gInv t) (hinvAll t) Tdot (T t)]
  -- Right contraction `coordContract gInv (comps T) Tdt = inner0S (T t) Tdot`.
  have hright :
      coordContract (gInv t)
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0) Tdt =
        inner0S (I := I) (g t) x s (T t) Tdot := by
    rw [← hcompTdot]
    rw [coordContract_eq_coordInner0S (I := I) (gInv t) (T t) Tdot basis]
    rw [← inner0S_eq_coord (I := I) (g t) x s basis (gInv t) (hinvAll t) (T t) Tdot]
  rw [hleft, hright]
  -- `inner0S (T t) Tdot = inner0S Tdot (T t)` by symmetry of the fibre inner
  -- product, so the two contractions sum to `2 · inner0S Tdot (T t)`.
  have hsymm :
      inner0S (I := I) (g t) x s (T t) Tdot =
        inner0S (I := I) (g t) x s Tdot (T t) := by
    unfold inner0S MetricFiberData.inner
    exact (tensor0SMetricData (I := I) (g t) x s).symm (T t) Tdot
  rw [hsymm]; ring

/-- **The Bochner-type norm time derivative under Ricci flow.**

This is `hasDerivWithinAt_normSq0S` with the metric-derivative term identified, via
the Ricci-flow inverse-metric-derivative relation `gInvDt i j = 2 Σ_{p,q} gInv i p ·
gInv j q · ric p q` (the conclusion of `inverseMetric_derivative_solve` for a flow
with Ricci `ric`), as the explicit **Ricci reaction** `ricReactionContract`:

`∂ₜ (normSq0S (g t) x s (T t)) = ricReactionContract (gInv t) ric (comps T) (comps T)`
`                                  + 2 · inner0S (g t) x s (∂ₜT) (T)`.

This is exactly the architecture's raw curvature-norm time derivative
`∂ₜ|T|² = (Ric ∗ T²) + 2⟨∂ₜT, T⟩` for `T = ∇ᵏRm` (rank `s = 4 + k`), now **derived**
from the product rule rather than assumed.  The remaining input is the tensor
component time derivative `∂ₜT` (`hT`/`hTdot`) — the same hypothesis-status data the
`k = 0`/`k = 1` producers already take (`Rm04NormRawDerivativeEquationOn` and its
analogues); supplying it here closes the metric (reaction) half generically.  `ric`
is an abstract symmetric component array; for a flow it is the Ricci tensor and
`hflow` is `inverseMetric_derivative_solve`. -/
theorem hasDerivWithinAt_normSq0S_ricciFlow {s : Nat} {x : M}
    {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt ric : Idx -> Idx -> Real)
    (T : Real -> Tensor0SSpace s I x)
    (Tdt : (Fin s -> Idx) -> Real)
    (Tdot : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gInv r))
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hT : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) u t)
    (hTdot : ∀ I0 : Fin s -> Idx,
      tensor0SComponent (I := I) Tdot (fun i => basis i) I0 = Tdt I0)
    (hflow : ∀ i j : Idx,
      gInvDt i j = 2 * (∑ p : Idx, ∑ q : Idx, gInv t i p * gInv t j q * ric p q)) :
    HasDerivWithinAt
      (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (ricReactionContract (gInv t) ric
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        2 * inner0S (I := I) (g t) x s Tdot (T t))
      u t := by
  have hbase :=
    hasDerivWithinAt_normSq0S (s := s) (u := u) (t := t)
      g gInv gInvDt T Tdt Tdot basis hinvAll hgInv hT hTdot
  rw [coordContractDt_eq_ricReactionContract (gInv t) gInvDt ric
      (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
      (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) hflow]
    at hbase
  exact hbase

end Intrinsic

end

end Tensor0SBundle
