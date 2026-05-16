import RicciFlower.RicciFlow.Evolution.Metric
import RicciFlower.Coordinates.Christoffel
import RicciFlower.Realized.CurvatureComponents
import RicciFlower.Connection.MetricCompatibility
import RicciFlower.LeviCivita.Torsion
import RicciFlower.VectorBundle.PartialMfderiv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Ricci-Flow Connection Evolution in a Fixed Frame

The geometric calculation is the lowered pairing formula

`partial_t g_t(d/ds nabla^s_i e_j, e_l)
  = -nabla_i Ric_jl - nabla_j Ric_il + nabla_l Ric_ij`.

This file turns that pairing statement into raised Christoffel components by
the fixed-frame coefficient identity
`coeff_k V = sum_l g^{kl} g(e_l,V)`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- Lowered Ricci-flow Christoffel variation term:
`-nabla_i Ric_jl - nabla_j Ric_il + nabla_l Ric_ij`. -/
def christoffelVariationLoweredRHSInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j l : Idx) : Real :=
  -nablaRic t x i j l - nablaRic t x j i l + nablaRic t x l i j

/-- `g^{kl} (nabla_i Ric)_{jl}`. -/
def nablaRicLastRaisedInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * nablaRic t x i j l

/-- `g^{kl} (nabla_l Ric)_{ij}`. -/
def nablaRicDirectionRaisedInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * nablaRic t x l i j

/-- Raised Ricci-flow Christoffel RHS in the convention of
`Coordinates.ricciFlowChristoffelEvolutionRHSInFrame`. -/
def christoffelEvolutionRHSInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx,
    gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l

/-- Raise an arbitrary lowered connection-variation RHS to Christoffel
components using the inverse metric in the chosen frame. -/
def christoffelVariationRHSFromLoweredInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (loweredRHS : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * loweredRHS t x i j l

theorem christoffelEvolutionRHSInFrame_eq_coordinates_rhs
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) :
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
      RicciFlower.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        t x i j k := by
  let A : Idx -> Real := fun l => gInv t x k l * nablaRic t x i j l
  let B : Idx -> Real := fun l => gInv t x k l * nablaRic t x j i l
  let C : Idx -> Real := fun l => gInv t x k l * nablaRic t x l i j
  change (∑ l : Idx,
      gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l) =
    - (∑ l : Idx, A l) - (∑ l : Idx, B l) + ∑ l : Idx, C l
  calc
    (∑ l : Idx,
        gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l)
        = ∑ l : Idx, (-A l - B l + C l) := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            simp [A, B, C, christoffelVariationLoweredRHSInFrame]
            ring
    _ = - (∑ l : Idx, A l) - (∑ l : Idx, B l) + ∑ l : Idx, C l := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- A component family realizes the covariant derivative of Ricci in a frame
when it is obtained by evaluating a supplied `(0,3)` tensor section on the
frame vectors.  The geometric statement that the supplied tensor section is
actually `∇ Ric` is intentionally separate. -/
def NablaRicciTensorComponentsInFrameOn
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRicTensor : Real ->
      Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ⊤ 3)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j l,
    nablaRic t x i j l =
      nablaRicTensor t x
        (Realized.vec3 (frame i x) (frame j x) (frame l x))

/-- Difference of two time-slice connections evaluated on the local frame:
`(nabla^var_i e_j - nabla^base_i e_j)(x)`. -/
def connectionDiffVectorInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j : Idx) : TangentSpace I x :=
  (S.family.connection var (frame j) x) (frame i x) -
    (S.family.connection base (frame j) x) (frame i x)

/-- Lowered connection-difference component with an explicitly chosen metric
time.  The finite-difference Koszul formula uses `metricTime = var`; the time
derivative target uses `metricTime = base`. -/
def connectionDiffLoweredInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base var : Real) (x : M) (i j l : Idx) : Real :=
  (S.family.metric metricTime).inner x
    (connectionDiffVectorInFrame (I := I) S frame base var x i j)
    (frame l x)

@[simp] theorem connectionDiffVectorInFrame_self
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j : Idx) :
    connectionDiffVectorInFrame (I := I) S frame base base x i j = 0 := by
  simp [connectionDiffVectorInFrame]

@[simp] theorem connectionDiffLoweredInFrame_self
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base : Real) (x : M) (i j l : Idx) :
    connectionDiffLoweredInFrame (I := I) S frame metricTime base base x i j l = 0 := by
  simp [connectionDiffLoweredInFrame]

/-- Covariant derivative of the metric at time `var`, using the connection at
time `base`, in the chosen frame:
`(nabla^base_d g_var)_{ab}`. -/
def metricCovDerivCompInFrameAtBase
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => (S.family.metric var).inner y (frame a y) (frame b y))
      x (frame d x) -
    (S.family.metric var).inner x
      ((S.family.connection base (frame a) x) (frame d x)) (frame b x) -
    (S.family.metric var).inner x (frame a x)
      ((S.family.connection base (frame b) x) (frame d x))

/-- Finite-difference Koszul RHS:
`(nabla^base_i g_var)_{jl} + (nabla^base_j g_var)_{il}
  - (nabla^base_l g_var)_{ij}`. -/
def finiteDifferenceKoszulRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j l : Idx) : Real :=
  metricCovDerivCompInFrameAtBase (I := I) S frame base var x i j l +
    metricCovDerivCompInFrameAtBase (I := I) S frame base var x j i l -
      metricCovDerivCompInFrameAtBase (I := I) S frame base var x l i j

private theorem localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

private theorem connectionDiffVectorInFrame_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {base var : Real} (hbase : base ∈ D.carrier) (hvar : var ∈ D.carrier)
    (i j : Idx) :
    connectionDiffVectorInFrame (I := I) S frame base var x i j =
      connectionDiffVectorInFrame (I := I) S frame base var x j i := by
  have hfi : MDiffAt (T% (frame i)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hfj : MDiffAt (T% (frame j)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx j
  have hvar_torsion :=
    RicciFlower.LeviCivita.torsion_free_apply
      (I := I) (hS.leviCivita.2 ⟨var, hvar⟩) (hX := hfi) (hY := hfj)
  have hbase_torsion :=
    RicciFlower.LeviCivita.torsion_free_apply
      (I := I) (hS.leviCivita.2 ⟨base, hbase⟩) (hX := hfi) (hY := hfj)
  have hdiff :
      (S.family.connection var (frame j) x) (frame i x) -
          (S.family.connection var (frame i) x) (frame j x) =
        (S.family.connection base (frame j) x) (frame i x) -
          (S.family.connection base (frame i) x) (frame j x) := by
    exact hvar_torsion.trans hbase_torsion.symm
  unfold connectionDiffVectorInFrame
  apply sub_eq_zero.mp
  calc
    ((S.family.connection var (frame j) x) (frame i x) -
          (S.family.connection base (frame j) x) (frame i x)) -
        ((S.family.connection var (frame i) x) (frame j x) -
          (S.family.connection base (frame i) x) (frame j x))
        =
      ((S.family.connection var (frame j) x) (frame i x) -
          (S.family.connection var (frame i) x) (frame j x)) -
        ((S.family.connection base (frame j) x) (frame i x) -
          (S.family.connection base (frame i) x) (frame j x)) := by
        abel
    _ = 0 := by
        rw [hdiff, sub_self]

private theorem connectionDiffLoweredInFrame_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {metricTime base var : Real} (hbase : base ∈ D.carrier) (hvar : var ∈ D.carrier)
    (i j l : Idx) :
    connectionDiffLoweredInFrame (I := I) S frame metricTime base var x i j l =
      connectionDiffLoweredInFrame (I := I) S frame metricTime base var x j i l := by
  unfold connectionDiffLoweredInFrame
  rw [connectionDiffVectorInFrame_symm
    (I := I) S hS frame hframe hu hx hbase hvar i j]

/-- Metric compatibility rewrites `(nabla^base_d g_var)_{ab}` as the two
connection-difference terms produced by changing the Levi-Civita connection
from `base` to `var`. -/
theorem metricCovDerivCompInFrameAtBase_eq_connectionDiff
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {base var : Real} (hvar : var ∈ D.carrier)
    (d a b : Idx) :
    metricCovDerivCompInFrameAtBase (I := I) S frame base var x d a b =
      connectionDiffLoweredInFrame (I := I) S frame var base var x d a b +
        (S.family.metric var).inner x (frame a x)
          (connectionDiffVectorInFrame (I := I) S frame base var x d b) := by
  have hfd : MDiffAt (T% (frame d)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx d
  have hfa : MDiffAt (T% (frame a)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hfb : MDiffAt (T% (frame b)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmc :=
    RicciFlower.Connection.metric_compatible_apply
      (I := I) (hS.leviCivita.1 ⟨var, hvar⟩)
      (frame d) (frame a) (frame b) hfd hfa hfb
  unfold metricCovDerivCompInFrameAtBase connectionDiffLoweredInFrame
    connectionDiffVectorInFrame
  have hmc' :
      extDerivFun (I := I)
          (fun y : M => (S.family.metric var).inner y (frame a y) (frame b y))
          x (frame d x) =
        (S.family.metric var).inner x
            ((S.family.connection var (frame a) x) (frame d x)) (frame b x) +
          (S.family.metric var).inner x (frame a x)
            ((S.family.connection var (frame b) x) (frame d x)) := by
    simpa [extDerivFun] using hmc
  rw [hmc']
  simp
  ring

/-- Finite-difference Koszul formula for two Levi-Civita connections in the
same local frame. -/
theorem finiteDifferenceKoszulInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {base var : Real} (hbase : base ∈ D.carrier) (hvar : var ∈ D.carrier)
    (i j l : Idx) :
    2 * connectionDiffLoweredInFrame (I := I) S frame var base var x i j l =
      finiteDifferenceKoszulRHSInFrame (I := I) S frame base var x i j l := by
  rw [finiteDifferenceKoszulRHSInFrame]
  rw [metricCovDerivCompInFrameAtBase_eq_connectionDiff
    (I := I) S hS frame hframe hu hx hvar i j l]
  rw [metricCovDerivCompInFrameAtBase_eq_connectionDiff
    (I := I) S hS frame hframe hu hx hvar j i l]
  rw [metricCovDerivCompInFrameAtBase_eq_connectionDiff
    (I := I) S hS frame hframe hu hx hvar l i j]
  have hji := connectionDiffLoweredInFrame_symm
    (I := I) S hS frame hframe hu hx (metricTime := var) hbase hvar j i l
  have hli := connectionDiffLoweredInFrame_symm
    (I := I) S hS frame hframe hu hx (metricTime := var) hbase hvar l i j
  have hlj := connectionDiffVectorInFrame_symm
    (I := I) S hS frame hframe hu hx hbase hvar l j
  have hsym1 :
      (S.family.metric var).inner x (frame j x)
          (connectionDiffVectorInFrame (I := I) S frame base var x i l) =
        connectionDiffLoweredInFrame (I := I) S frame var base var x i l j := by
    unfold connectionDiffLoweredInFrame
    exact (S.family.metric var).symm x (frame j x)
      (connectionDiffVectorInFrame (I := I) S frame base var x i l)
  rw [hji, hli, hlj, hsym1]
  ring

/-- The raw lowered connection-pairing time derivative
`∂t g_t(e_l, ∇^s_i e_j)|_{s=t}` with the metric frozen at `t`.

This is the regularity side of Lemma 6.2, before identifying the derivative
with the Ricci-flow Koszul expression. -/
def ConnectionPairingDerivativeInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (pairDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j l : Idx),
    HasDerivWithinAt
      (fun s : Real =>
        (S.family.metric (t : Real)).inner x (frame l x)
          ((S.family.connection s (frame j) x) (frame i x)))
      (pairDt (t : Real) x i j l)
      D.carrier
      (t : Real)

/-- Local version of `ConnectionPairingDerivativeInFrameOn`, restricted to
the base set where the chosen local frame is known to be differentiable. -/
def ConnectionPairingDerivativeInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (pairDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          (S.family.metric (t : Real)).inner x (frame l x)
            ((S.family.connection s (frame j) x) (frame i x)))
        (pairDt (t : Real) x i j l)
        D.carrier
        (t : Real)

/-- Time derivative of the variable-metric finite connection difference
`g_s((nabla^s - nabla^t)_i e_j, e_l)`.  This records the product-rule fact
that the derivative agrees with the frozen pairing derivative because the
connection difference vanishes at `s = t`. -/
def VariableMetricConnectionDiffDerivativeInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (pairDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (pairDt (t : Real) x i j l)
        D.carrier
        (t : Real)

/-- Time derivative of the fixed-base covariant metric derivative
`(nabla^t g_s)_{ij}`. -/
def MetricCovDerivDerivativeComponentsInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall d a b : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          metricCovDerivCompInFrameAtBase (I := I) S frame (t : Real) s x d a b)
        (metricCovDerivDt (t : Real) x d a b)
        D.carrier
        (t : Real)

/-- General first variation RHS for the lowered connection pairing:
`1/2 (nabla_i h_jl + nabla_j h_il - nabla_l h_ij)`. -/
def connectionVariationLoweredRHSFromMetricVariationInFrame
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j l : Idx) : Real :=
  (1 / 2 : Real) *
    (metricCovDerivDt t x i j l + metricCovDerivDt t x j i l -
      metricCovDerivDt t x l i j)

/-- General metric-variation Christoffel RHS:
`1/2 g^{kl} (nabla_i h_jl + nabla_j h_il - nabla_l h_ij)`. -/
def christoffelVariationRHSFromMetricVariationInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  christoffelVariationRHSFromLoweredInFrame (M := M) gInv
    (connectionVariationLoweredRHSFromMetricVariationInFrame metricCovDerivDt)
    t x i j k

/-- The metric-variation components are the covariant derivative of
`h = partial_t g = -2 Ric`. -/
def MetricCovDerivDerivativeIsRicciFlowInFrame
    (metricCovDerivDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) :
    Prop :=
  forall t x i j l,
    metricCovDerivDt t x i j l = (-2 : Real) * nablaRic t x i j l

/-- Fixed-frame components of the covariant derivative of the Ricci tensor,
computed from the connection at the same time:
`(∇_d Ric)_{ab} = d(Ric_ab)(e_d) - Ric(∇_d e_a,e_b) - Ric(e_a,∇_d e_b)`. -/
def ricciCovDerivCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => ricciCompInFrame (I := I) S frame t y a b)
      x (frame d x) -
    S.ricci t x
      (Realized.vec2
        ((S.family.connection t (frame a) x) (frame d x))
        (frame b x)) -
    S.ricci t x
      (Realized.vec2
        (frame a x)
        ((S.family.connection t (frame b) x) (frame d x)))

/-- A supplied component family is the covariant derivative of Ricci in the
chosen local frame. -/
def NablaRicciComponentsByConnectionInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M), x ∈ u ->
    forall d a b : Idx,
      nablaRic t x d a b =
        ricciCovDerivCompInFrame (I := I) S frame t x d a b

/-- Regular component package for fixed-frame components of `∇ Ric`.

The raw predicate `NablaRicciComponentsByConnectionInFrameOn` is intentionally
pointwise-only.  This package is for coordinate calculus that differentiates
the supplied component functions. -/
structure NablaRicciComponentsRegularInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop where
  realizes :
    NablaRicciComponentsByConnectionInFrameOn
      (I := I) S frame u nablaRic
  mdiffAt :
    forall (t : Real) (x : M), x ∈ u ->
      forall d i j : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => nablaRic t y d i j) x

/-- Fixed-frame components of the second covariant derivative of the Ricci
tensor, computed from supplied first covariant derivative components.

The slot order is `(nabla_d nabla_a Ric)_{ij}`. -/
def ricciSecondCovDerivCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d a i j : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => nablaRic t y a i j) x
      (frame d x) -
    (∑ p : Idx,
      RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection t) frame hframe x d a p *
        nablaRic t x p i j) -
    (∑ p : Idx,
      RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection t) frame hframe x d i p *
        nablaRic t x a p j) -
    (∑ p : Idx,
      RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection t) frame hframe x d j p *
        nablaRic t x a i p)

/-- A supplied component family is the second covariant derivative of Ricci in
the chosen local frame. -/
def Nabla2RicciComponentsByConnectionInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M), x ∈ u ->
    forall d a i j : Idx,
      nabla2Ric t x d a i j =
        ricciSecondCovDerivCompInFrame
          (I := I) S frame hframe nablaRic t x d a i j

/-- Regular component package for fixed-frame components of `∇² Ric`.

This bundles the regular first-derivative component package with the existing
pointwise second-derivative realization. -/
structure Nabla2RicciComponentsRegularInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop where
  first :
    NablaRicciComponentsRegularInFrameOnLocal
      (I := I) S frame u nablaRic
  second :
    Nabla2RicciComponentsByConnectionInFrameOn
      (I := I) S frame u hframe nablaRic nabla2Ric

theorem metricCovDerivDerivativeIsRicciFlowInFrame_neg_two
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) :
    MetricCovDerivDerivativeIsRicciFlowInFrame
      (fun t x d a b => (-2 : Real) * nablaRic t x d a b)
      nablaRic := by
  intro t x i j l
  rfl

/-- Differentiate the fixed-base metric covariant derivative along Ricci flow.

This is the coordinate statement
`∂s (∇^t_d g_s)_{ab}|_{s=t} = -2 (∇^t_d Ric_t)_{ab}`.  The spatial
connection is frozen at `t`, so the only mixed-derivative input is the scalar
fixed-base exterior derivative of the frame metric components. -/
theorem metricCovDerivDerivativeComponents_of_ricciFlow
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic) :
    MetricCovDerivDerivativeComponentsInFrameOnLocal
      (I := I) S frame u
      (fun t x d a b => (-2 : Real) * nablaRic t x d a b) := by
  intro t x hx d a b
  let Ca : TangentSpace I x :=
    (S.family.connection (t : Real) (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (S.family.connection (t : Real) (frame b) x) (frame d x)
  have hExt :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => metricCompInFrame (I := I) S frame s y a b)
            x (frame d x))
        ((-2 : Real) *
          extDerivFun (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
            x (frame d x))
        D.carrier
        (t : Real) :=
    hreg.frameMetricExtDerivTimeDerivative t x hx d a b
  have hCa :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x Ca (frame b x))
        ((-2 : Real) *
          S.ricci (t : Real) x (Realized.vec2 Ca (frame b x)))
        D.carrier
        (t : Real) := by
    simpa [Ca, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x Ca (frame b x)
  have hCb :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x (frame a x) Cb)
        ((-2 : Real) *
          S.ricci (t : Real) x (Realized.vec2 (frame a x) Cb))
        D.carrier
        (t : Real) := by
    simpa [Cb, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x (frame a x) Cb
  have hDeriv :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x) -
            (S.family.metric s).inner x Ca (frame b x) -
            (S.family.metric s).inner x (frame a x) Cb)
        (((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x)) -
          ((-2 : Real) *
            S.ricci (t : Real) x (Realized.vec2 Ca (frame b x))) -
          ((-2 : Real) *
            S.ricci (t : Real) x (Realized.vec2 (frame a x) Cb)))
        D.carrier
        (t : Real) :=
    (hExt.sub hCa).sub hCb
  refine hDeriv.congr ?_ ?_ |>.congr_deriv ?_
  · intro s _hs
    simp [metricCovDerivCompInFrameAtBase, metricCompInFrame, Ca, Cb]
  · simp [metricCovDerivCompInFrameAtBase, metricCompInFrame, Ca, Cb]
  · have hn := hnabla (t : Real) x hx d a b
    unfold ricciCovDerivCompInFrame at hn
    change
      (-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x) -
          (-2 : Real) *
            S.ricci (t : Real) x (Realized.vec2 Ca (frame b x)) -
          (-2 : Real) *
            S.ricci (t : Real) x (Realized.vec2 (frame a x) Cb) =
        (-2 : Real) * nablaRic (t : Real) x d a b
    rw [hn]
    simp [Ca, Cb]
    ring

/-- The only analytic frontier for the Christoffel variation: if time
differentiation commutes with the fixed-base covariant derivative of the metric,
then the finite-difference Koszul identity gives the variable-metric connection
difference derivative. -/
theorem variableMetricConnectionDiffDerivative_of_metricCovDeriv
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic)
    (_hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    VariableMetricConnectionDiffDerivativeInFrameOnLocal
      (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) := by
  intro t x hx i j l
  have htcarrier : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hR :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j)
        D.carrier
        (t : Real) := by
    unfold finiteDifferenceKoszulRHSInFrame
    exact ((hmetric t x hx i j l).add (hmetric t x hx j i l)).sub
      (hmetric t x hx l i j)
  have hTwoDiff :
      HasDerivWithinAt
        (fun s : Real =>
          2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j)
        D.carrier
        (t : Real) := by
    refine hR.congr ?_ ?_
    · intro s hs
      exact finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier hs i j l
    · exact finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier htcarrier i j l
  have hHalf :
      HasDerivWithinAt
        (fun s : Real =>
          (1 / 2 : Real) *
            (2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l))
        ((1 / 2 : Real) *
          (metricCovDerivDt (t : Real) x i j l +
            metricCovDerivDt (t : Real) x j i l -
              metricCovDerivDt (t : Real) x l i j))
        D.carrier
        (t : Real) :=
    HasDerivWithinAt.const_mul (1 / 2 : Real) hTwoDiff
  have hDiff :
      HasDerivWithinAt
        (fun s : Real =>
          connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        ((1 / 2 : Real) *
          (metricCovDerivDt (t : Real) x i j l +
            metricCovDerivDt (t : Real) x j i l -
              metricCovDerivDt (t : Real) x l i j))
        D.carrier
        (t : Real) := by
    refine hHalf.congr ?_ ?_
    · intro s _hs
      ring
    · ring
  refine hDiff.congr_deriv ?_
  unfold christoffelVariationLoweredRHSInFrame
  rw [hmetricRicci (t : Real) x i j l,
    hmetricRicci (t : Real) x j i l,
    hmetricRicci (t : Real) x l i j]
  ring

/-- The Koszul/Levi-Civita variation identity specialized to Ricci flow:
the lowered connection derivative is
`-∇_i Ric_jl - ∇_j Ric_il + ∇_l Ric_ij`. -/
def KoszulConnectionVariationInFrame
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j l,
    pairDt t x i j l =
      christoffelVariationLoweredRHSInFrame nablaRic t x i j l

/-- The lowered pairing variation formula for the connection along Ricci flow.

The metric is frozen at the differentiating time `t`; only the connection
family varies in the scalar function. -/
def ConnectionVariationPairingEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j l : Idx),
    HasDerivWithinAt
      (fun s : Real =>
        (S.family.metric (t : Real)).inner x (frame l x)
          ((S.family.connection s (frame j) x) (frame i x)))
      (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
      D.carrier
      (t : Real)

/-- Local lowered pairing variation equation. -/
def ConnectionVariationPairingEquationInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          (S.family.metric (t : Real)).inner x (frame l x)
            ((S.family.connection s (frame j) x) (frame i x)))
        (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real)

/-- Component identity behind the general first variation formula, obtained
by differentiating the finite-difference Koszul identity in time. -/
theorem connectionPairDt_eq_metricVariationRHS
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j l : Idx) :
    pairDt (t : Real) x i j l =
      connectionVariationLoweredRHSFromMetricVariationInFrame
        metricCovDerivDt (t : Real) x i j l := by
  have htcarrier : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hL :
      HasDerivWithinAt
        (fun s : Real =>
          2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (2 * pairDt (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa using
      HasDerivWithinAt.const_mul (2 : Real) (hvarDiff t x hx i j l)
  have hL_as_R :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (2 * pairDt (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    refine hL.congr ?_ ?_
    · intro s hs
      exact (finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier hs i j l
        ).symm
    · exact (finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier htcarrier i j l).symm
  have hR :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j)
        D.carrier
        (t : Real) := by
    unfold finiteDifferenceKoszulRHSInFrame
    exact ((hmetric t x hx i j l).add (hmetric t x hx j i l)).sub
      (hmetric t x hx l i j)
  have hderiv :
      2 * pairDt (t : Real) x i j l =
        metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j := by
    exact (hL_as_R.derivWithin (hunique t)).symm.trans
      (hR.derivWithin (hunique t))
  unfold connectionVariationLoweredRHSFromMetricVariationInFrame
  linarith

/-- General first variation of Christoffel symbols in lowered-pairing form:
`pairDt = 1/2 (nabla_i h_jl + nabla_j h_il - nabla_l h_ij)`. -/
theorem connectionVariationPairing_of_metricVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall i j l : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            (S.family.metric (t : Real)).inner x (frame l x)
              ((S.family.connection s (frame j) x) (frame i x)))
          (connectionVariationLoweredRHSFromMetricVariationInFrame
            metricCovDerivDt (t : Real) x i j l)
          D.carrier
          (t : Real) := by
  intro t x hx i j l
  exact (hpair t x hx i j l).congr_deriv
    (connectionPairDt_eq_metricVariationRHS
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hvarDiff hmetric hunique t x hx i j l)

/-- Ricci-flow specialization of the general Christoffel first variation,
using `partial_t g = -2 Ric`. -/
theorem connectionVariationPairing_of_ricciFlow
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ConnectionVariationPairingEquationInFrameOnLocal
      (I := I) S frame u nablaRic := by
  intro t x hx i j l
  have hmetricVar :=
    connectionVariationPairing_of_metricVariation
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hpair hvarDiff hmetric hunique t x hx i j l
  refine hmetricVar.congr_deriv ?_
  unfold connectionVariationLoweredRHSFromMetricVariationInFrame
    christoffelVariationLoweredRHSInFrame
  rw [hmetricRicci (t : Real) x i j l,
    hmetricRicci (t : Real) x j i l,
    hmetricRicci (t : Real) x l i j]
  ring

/-- Lemma 6.2, lowered-pairing form, from the connection derivative and the
Ricci-flow Koszul variation identity. -/
theorem connectionVariationPairing_of_koszul
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hdt : ConnectionPairingDerivativeInFrameOn (I := I) S frame pairDt)
    (hkoszul : KoszulConnectionVariationInFrame (M := M) pairDt nablaRic) :
    ConnectionVariationPairingEquationInFrameOn
      (I := I) S frame nablaRic := by
  intro t x i j l
  exact (hdt t x i j l).congr_deriv (hkoszul (t : Real) x i j l)

/-- Interval Christoffel component evolution in a local frame. -/
def ChristoffelVariationEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection s) frame hframe x i j k)
        (rhs (t : Real) x i j k)
        D.carrier
        (t : Real)

/-- Mixed time/spatial derivative regularity for a Christoffel component
variation formula.

For fixed frame components, this says that differentiating
`Γ^k_{ij}(s, -)` spatially at a fixed base point and then in time gives the
spatial derivative of the supplied variation RHS. This is the exact regularity
needed to differentiate the coordinate curvature formula. -/
def ChristoffelVariationMixedDerivativeInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall i j k : Idx,
    FixedBaseExtDerivTimeDerivativeOn (I := I) D.carrier u
      (fun s x =>
        RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (fun s x => rhs s x i j k)

/-- Regular-time version of
`ChristoffelVariationMixedDerivativeInFrameOn`.

Ricci-flow evolution identities are only stated at regular times of the time
interval, while the derivative remains a derivative within the full carrier. -/
def ChristoffelVariationMixedDerivativeInFrameOnRegular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall i j k : Idx,
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
      D.carrier D.regular u
      (fun s x =>
        RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (fun s x => rhs s x i j k)

/-- The old all-times mixed-Christoffel predicate implies the regular-time
predicate used by Ricci-flow evolution statements. -/
theorem ChristoffelVariationMixedDerivativeInFrameOn.toRegular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h :
      ChristoffelVariationMixedDerivativeInFrameOn
        (I := I) S frame hframe rhs) :
    ChristoffelVariationMixedDerivativeInFrameOnRegular
      (I := I) S frame hframe rhs := by
  intro i j k
  exact (h i j k).toRegular (I := I) (regularSet := D.regular)

/-- General metric-variation Christoffel component formula in a local frame. -/
def ChristoffelMetricVariationEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ChristoffelVariationEquationInFrameOn (I := I) S frame hframe
    (christoffelVariationRHSFromMetricVariationInFrame (M := M) gInv metricCovDerivDt)

/-- Pointwise use of `ChristoffelMetricVariationEquationInFrameOn`. -/
theorem christoffelMetricVariation_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h :
      ChristoffelMetricVariationEquationInFrameOn
        (I := I) S gInv frame hframe metricCovDerivDt)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (christoffelVariationRHSFromMetricVariationInFrame
        (M := M) gInv metricCovDerivDt (t : Real) x i j k)
      D.carrier
      (t : Real) :=
  h t x hx i j k

/-- Ricci-flow-specific Christoffel component evolution in a local frame. -/
def ChristoffelEvolutionEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection s) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
          (t : Real) x i j k)
        D.carrier
        (t : Real)

theorem frameCoeff_eq_sum_inv_metricPairing
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
    intro i j
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).2
  calc
    hframe.coeff k x V = (hframe.toBasisAt hx).repr V k := by
        simp [IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
        simpa [IsLocalFrameOn.toBasisAt_coe] using
          Realized.basis_coord_eq_sum_inv_inner
            (I := I) (M := M) (S.family.metric t) (hframe.toBasisAt hx)
            (fun i j : Idx => gInv t x i j) hinvAt k V

/-- Raise a supplied lowered connection-variation pairing formula to
Christoffel components. -/
theorem christoffelVariationEquationInFrameOn_of_pairing_local
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (loweredRHS : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hpair :
      forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
        forall i j l : Idx,
          HasDerivWithinAt
            (fun s : Real =>
              (S.family.metric (t : Real)).inner x (frame l x)
                ((S.family.connection s (frame j) x) (frame i x)))
            (loweredRHS (t : Real) x i j l)
            D.carrier
            (t : Real)) :
    ChristoffelVariationEquationInFrameOn
      (I := I) S frame hframe
      (christoffelVariationRHSFromLoweredInFrame (M := M) gInv loweredRHS) := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx, gInv (t : Real) x k l *
          loweredRHS (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l * loweredRHS (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x hx i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact (frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

/-- Difference of Christoffel components expressed through the variable-time
metric pairing with the connection-difference tensor. -/
theorem christoffelSymbol_sub_eq_sum_inv_connectionDiff
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (base var : Real) {x : M} (hx : x ∈ u)
    (i j k : Idx) :
    RicciFlower.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      RicciFlower.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k =
      ∑ l : Idx, gInv var x k l *
        connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
  let Vvar : TangentSpace I x :=
    (S.family.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (S.family.connection base (frame j) x) (frame i x)
  have hvar :=
    frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv var hx k Vvar
  have hbase :=
    frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv var hx k Vbase
  calc
    RicciFlower.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      RicciFlower.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k
        = (∑ l : Idx, gInv var x k l *
            (S.family.metric var).inner x (frame l x) Vvar) -
          (∑ l : Idx, gInv var x k l *
            (S.family.metric var).inner x (frame l x) Vbase) := by
            change hframe.coeff k x Vvar - hframe.coeff k x Vbase =
              (∑ l : Idx, gInv var x k l *
                (S.family.metric var).inner x (frame l x) Vvar) -
              (∑ l : Idx, gInv var x k l *
                (S.family.metric var).inner x (frame l x) Vbase)
            rw [hvar, hbase]
    _ = ∑ l : Idx, gInv var x k l *
          ((S.family.metric var).inner x (frame l x) Vvar -
            (S.family.metric var).inner x (frame l x) Vbase) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun l _hl => ?_
            ring
    _ = ∑ l : Idx, gInv var x k l *
          (S.family.metric var).inner x (frame l x) (Vvar - Vbase) := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            rw [map_sub]
    _ = ∑ l : Idx, gInv var x k l *
          connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            unfold connectionDiffLoweredInFrame connectionDiffVectorInFrame Vvar Vbase
            rw [(S.family.metric var).symm x (frame l x)
              ((S.family.connection var (frame j) x) (frame i x) -
                (S.family.connection base (frame j) x) (frame i x))]

/-- Raise the connection-variation pairing formula to Christoffel components. -/
theorem christoffelEvolutionEquationInFrameOn_of_pairing
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hpair : ConnectionVariationPairingEquationInFrameOn
      (I := I) S frame nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx,
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact (frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

/-- Raise the local lowered connection-variation pairing formula to
Christoffel components. -/
theorem christoffelEvolutionEquationInFrameOn_of_pairing_local
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hpair : ConnectionVariationPairingEquationInFrameOnLocal
      (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx,
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x hx i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact (frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

/-- General metric-variation Christoffel formula in raised component form. -/
theorem christoffelMetricVariationEquationInFrameOn_of_metricVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ChristoffelMetricVariationEquationInFrameOn
      (I := I) S gInv frame hframe metricCovDerivDt :=
  christoffelVariationEquationInFrameOn_of_pairing_local
    (I := I) S gInv frame hframe
    (connectionVariationLoweredRHSFromMetricVariationInFrame metricCovDerivDt)
    hinv
    (connectionVariationPairing_of_metricVariation
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hpair hvarDiff hmetric hunique)

/-- Lemma 6.2 from metric-frame regularity plus the fixed-base metric
covariant-derivative frontier.

This proof differentiates
`Gamma(s) - Gamma(t) = gInv(s) * g_s((nabla^s - nabla^t)e_i e_j, e_l)`.
The product-rule term containing `dt gInv` vanishes because the connection
difference is zero at `s = t`; the remaining derivative is supplied by the
finite-difference Koszul computation and the Ricci-flow metric variation. -/
theorem christoffelEvolution_of_metricFrameTimeRegularity
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetricFrame :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let gamma : Real -> Real := fun s =>
    RicciFlower.Coordinates.christoffelSymbolInFrame
      (S.family.connection s) frame hframe x i j k
  let gamma0 : Real := gamma (t : Real)
  let rhs : Real -> Real := fun s =>
    ∑ l : Idx, gInv s x k l *
      connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l
  let target : Real :=
    ∑ l : Idx, gInv (t : Real) x k l *
      christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l
  have hDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
    variableMetricConnectionDiffDerivative_of_metricCovDeriv
      (I := I) S hS frame hframe hu metricCovDerivDt nablaRic
      hmetric hmetricRicci hmetricFrame.uniqueTimeDerivatives
  have hRhs :
      HasDerivWithinAt rhs target D.carrier (t : Real) := by
    dsimp [rhs, target]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s =>
          gInv s x k l *
            connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            have hprod :=
              (hmetricFrame.inverseMetricDerivative t x k l).mul
                (hDiff t x hx i j l)
            refine hprod.congr_deriv ?_
            simp))
  have hSub :
      HasDerivWithinAt
        (fun s : Real => gamma s - gamma0)
        target
        D.carrier
        (t : Real) := by
    refine hRhs.congr ?_ ?_
    · intro s _hs
      exact christoffelSymbol_sub_eq_sum_inv_connectionDiff
        (I := I) S gInv frame hframe hmetricFrame.nondegenerateGram
        (t : Real) s hx i j k
    · exact christoffelSymbol_sub_eq_sum_inv_connectionDiff
        (I := I) S gInv frame hframe hmetricFrame.nondegenerateGram
        (t : Real) (t : Real) hx i j k
  have hGammaPlus :
      HasDerivWithinAt
        (fun s : Real => (gamma s - gamma0) + gamma0)
        target
        D.carrier
        (t : Real) := by
    simpa using hSub.add_const gamma0
  have hGamma :
      HasDerivWithinAt gamma target D.carrier (t : Real) := by
    refine hGammaPlus.congr ?_ ?_
    · intro s _hs
      ring
    · ring
  simpa [gamma, target, christoffelEvolutionRHSInFrame] using hGamma

/-- Lemma 6.2 from spacetime-smooth Ricci-flow metric components.

This constructor eliminates the broad connection-regularity black box: the only
time/spatial input is the fixed-base mixed derivative of the metric components,
recorded in `MetricFrameSpacetimeRegularityInFrameOnLocal`. -/
theorem christoffelEvolution_of_spacetimeSmoothMetric
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolution_of_metricFrameTimeRegularity
    (I := I) S hS gInv gInvDt frame hframe hu
    (fun t x d a b => (-2 : Real) * nablaRic t x d a b)
    nablaRic
    hreg.toMetricFrameTimeRegularityInFrameOnLocal
    (metricCovDerivDerivativeComponents_of_ricciFlow
      (I := I) S hS gInv gInvDt frame hreg nablaRic hnabla)
    (metricCovDerivDerivativeIsRicciFlowInFrame_neg_two
      (M := M) (Idx := Idx) nablaRic)

/-- LaTeX Lemma 6.2, `lem:evol-christoffel`, in fixed-frame component form:
along Ricci flow,
`partial_t Gamma^k_ij =
  -g^{kl} nabla_i Ric_jl - g^{kl} nabla_j Ric_il
    + g^{kl} nabla_l Ric_ij`. -/
theorem evol_christoffel_inFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (RicciFlower.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        (t : Real) x i j k)
      D.carrier
      (t : Real) := by
  have hEvol :
      ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame hframe nablaRic :=
    christoffelEvolution_of_spacetimeSmoothMetric
      (I := I) S hS gInv gInvDt frame hframe hu nablaRic hreg hnabla
  exact (hEvol t x hx i j k).congr_deriv
    (christoffelEvolutionRHSInFrame_eq_coordinates_rhs
      (M := M) gInv nablaRic (t : Real) x i j k)

/-- Lemma 6.2 in raised Christoffel-component form, from the proved
finite-difference Koszul computation plus the remaining time-regularity
frontiers. -/
theorem christoffelEvolution_of_ricciFlowMetricVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolutionEquationInFrameOn_of_pairing_local
    (I := I) S gInv frame hframe nablaRic hinv
    (connectionVariationPairing_of_ricciFlow
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt nablaRic
      hpair hvarDiff hmetric hmetricRicci hunique)

/-- Lemma 6.2 in raised Christoffel-component form, from the connection
pairing derivative and the Ricci-flow Koszul variation identity. -/
theorem christoffelEvolution_of_koszul
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hdt : ConnectionPairingDerivativeInFrameOn (I := I) S frame pairDt)
    (hkoszul : KoszulConnectionVariationInFrame (M := M) pairDt nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolutionEquationInFrameOn_of_pairing
    (I := I) S gInv frame hframe nablaRic hinv
    (connectionVariationPairing_of_koszul
      (I := I) S frame pairDt nablaRic hdt hkoszul)

end Components

end RicciFlow
end RicciFlower
