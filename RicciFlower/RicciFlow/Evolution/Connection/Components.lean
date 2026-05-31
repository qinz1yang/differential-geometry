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
# Connection variation components

Fixed-frame component definitions and metric-covariant derivative variation producers.
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
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
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

/-- In a frame where the inverse metric components are the identity, the
raised Ricci-flow Christoffel RHS is the book's component formula
`-nabla_i Ric_jk - nabla_j Ric_ik + nabla_k Ric_ij`. -/
theorem christoffelRHS_id
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {t : Real} {x : M}
    (hinv_id : ∀ e l : Idx, gInv t x e l = if e = l then 1 else 0)
    (i j k : Idx) :
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
      -nablaRic t x i j k - nablaRic t x j i k + nablaRic t x k i j := by
  calc
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
        ∑ l : Idx,
          (if k = l then (1 : Real) else 0) *
            christoffelVariationLoweredRHSInFrame nablaRic t x i j l := by
          refine Finset.sum_congr rfl fun l _hl => ?_
          rw [hinv_id k l]
    _ = christoffelVariationLoweredRHSInFrame nablaRic t x i j k := by
          simp
    _ = -nablaRic t x i j k - nablaRic t x j i k +
          nablaRic t x k i j := by
          rfl

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
    S.ricciAt t x
      (Realized.vec2
        ((S.family.connection t (frame a) x) (frame d x))
        (frame b x)) -
    S.ricciAt t x
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

/-- Differentiate the fixed-base covariant metric derivative from the exact
mixed-derivative producer, without using the legacy metric-frame package. -/
theorem metricCovDerivOfMix
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hricci :
      forall t x, x ∈ u -> forall a b : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x)
    (hmix :
      forall a b : Idx,
        FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
          D.carrier D.regular u
          (fun s x => metricCompInFrame (I := I) S frame s x a b)
          (fun t x => (-2 : Real) *
            ricciCompInFrame (I := I) S frame t x a b))
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
  have hExtRaw :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => metricCompInFrame (I := I) S frame s y a b)
            x (frame d x))
        (extDerivFun (I := I)
          (fun y : M => (-2 : Real) *
            ricciCompInFrame (I := I) S frame (t : Real) y a b)
          x (frame d x))
        D.carrier
        (t : Real) :=
    fixedBaseExtDerivTimeDerivativeOnRegular_apply (I := I)
      (h := hmix a b) (t := (t : Real)) t.2 (x := x) hx (frame d x)
  have hscale :
      extDerivFun (I := I)
          (fun y : M => (-2 : Real) *
            ricciCompInFrame (I := I) S frame (t : Real) y a b)
          x (frame d x) =
        (-2 : Real) *
          extDerivFun (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
            x (frame d x) := by
    have h :=
      extDerivFun_const_mul (I := I) (-2 : Real)
        (hricci (t : Real) x hx a b)
    simpa [smul_eq_mul] using congrArg (fun L => L (frame d x)) h
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
    hExtRaw.congr_deriv hscale
  have hCa :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x Ca (frame b x))
        ((-2 : Real) *
          S.ricciAt (t : Real) x (Realized.vec2 Ca (frame b x)))
        D.carrier
        (t : Real) := by
    simpa [Ca, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x Ca (frame b x)
  have hCb :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x (frame a x) Cb)
        ((-2 : Real) *
          S.ricciAt (t : Real) x (Realized.vec2 (frame a x) Cb))
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
            S.ricciAt (t : Real) x (Realized.vec2 Ca (frame b x))) -
          ((-2 : Real) *
            S.ricciAt (t : Real) x (Realized.vec2 (frame a x) Cb)))
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
            S.ricciAt (t : Real) x (Realized.vec2 Ca (frame b x)) -
          (-2 : Real) *
            S.ricciAt (t : Real) x (Realized.vec2 (frame a x) Cb) =
        (-2 : Real) * nablaRic (t : Real) x d a b
    rw [hn]
    simp [Ca, Cb]
    ring

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
          S.ricciAt (t : Real) x (Realized.vec2 Ca (frame b x)))
        D.carrier
        (t : Real) := by
    simpa [Ca, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x Ca (frame b x)
  have hCb :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x (frame a x) Cb)
        ((-2 : Real) *
          S.ricciAt (t : Real) x (Realized.vec2 (frame a x) Cb))
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
            S.ricciAt (t : Real) x (Realized.vec2 Ca (frame b x))) -
          ((-2 : Real) *
            S.ricciAt (t : Real) x (Realized.vec2 (frame a x) Cb)))
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
            S.ricciAt (t : Real) x (Realized.vec2 Ca (frame b x)) -
          (-2 : Real) *
            S.ricciAt (t : Real) x (Realized.vec2 (frame a x) Cb) =
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
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic) :
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


end Components

end RicciFlow
end RicciFlower
