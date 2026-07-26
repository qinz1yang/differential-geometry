import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Pairing

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Raised Christoffel evolution

Local-frame coefficient algebra converting lowered pairing evolution to raised Christoffel components.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

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

/-- Interval Christoffel component evolution in a local frame. -/
def ChristoffelVariationEquationInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
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
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall i j k : Idx,
    FixedBaseExtDerivTimeDerivativeOn (I := I) D.carrier u
      (fun s x =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (fun s x => rhs s x i j k)

/-- Regular-time version of
`ChristoffelVariationMixedDerivativeInFrameOn`.

Ricci-flow evolution identities are only stated at regular times of the time
interval, while the derivative remains a derivative within the full carrier. -/
def ChristoffelVariationMixedDerivativeInFrameOnRegular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall i j k : Idx,
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
      D.carrier D.regular u
      (fun s x =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (fun s x => rhs s x i j k)

/-- The old all-times mixed-Christoffel predicate implies the regular-time
predicate used by Ricci-flow evolution statements. -/
theorem ChristoffelVariationMixedDerivativeInFrameOn.toRegular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
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
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ChristoffelVariationEquationInFrameOn (I := I) S frame hframe
    (christoffelVariationRHSFromMetricVariationInFrame (M := M) gInv metricCovDerivDt)

/-- Pointwise use of `ChristoffelMetricVariationEquationInFrameOn`. -/
theorem christoffelMetricVariation_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h :
      ChristoffelMetricVariationEquationInFrameOn
        (I := I) S gInv frame hframe metricCovDerivDt)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (christoffelVariationRHSFromMetricVariationInFrame
        (M := M) gInv metricCovDerivDt (t : Real) x i j k)
      D.carrier
      (t : Real) :=
  h t x hx i j k

/-- Ricci-flow-specific Christoffel component evolution in a local frame. -/
def ChristoffelEvolutionEquationInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection s) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
          (t : Real) x i j k)
        D.carrier
        (t : Real)

theorem frameCoeff_eq_sum_inv_metricPairing
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
    intro i j
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x hx i j).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x hx i j).2
  calc
    hframe.coeff k x V = (hframe.toBasisAt hx).repr V k := by
        simp [IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
        simpa [IsLocalFrameOn.toBasisAt_coe] using
          DifferentialGeometry.Integral.Connection.basis_coord_eq_sum_inv_inner
            (I := I) (M := M) (S.family.metric t) (hframe.toBasisAt hx)
            (fun i j : Idx => gInv t x i j) hinvAt k V

/-- Local inverse metric components give the frame coefficient formula on the
local frame domain. -/
theorem frameCoeffLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
    intro i j
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx i j).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx i j).2
  calc
    hframe.coeff k x V = (hframe.toBasisAt hx).repr V k := by
        simp [IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
        simpa [IsLocalFrameOn.toBasisAt_coe] using
          DifferentialGeometry.Integral.Connection.basis_coord_eq_sum_inv_inner
            (I := I) (M := M) (S.family.metric t) (hframe.toBasisAt hx)
            (fun i j : Idx => gInv t x i j) hinvAt k V

/-- Raise a supplied lowered connection-variation pairing formula to
Christoffel components. -/
theorem christoffelVariationEquationInFrameOn_of_pairing_local
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (loweredRHS : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hpair :
      forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
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
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

/-- Difference of Christoffel components expressed through the variable-time
metric pairing with the connection-difference tensor. -/
theorem christoffelSymbol_sub_eq_sum_inv_connectionDiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (base var : Real) {x : M} (hx : x ∈ u)
    (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
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
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
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

/-- Local inverse-component version of the Christoffel difference identity. -/
theorem gammaSubLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (base var : Real) {x : M} (hx : x ∈ u)
    (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k =
      ∑ l : Idx, gInv var x k l *
        connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
  let Vvar : TangentSpace I x :=
    (S.family.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (S.family.connection base (frame j) x) (frame i x)
  have hvar :=
    frameCoeffLocal
      (I := I) S gInv frame hframe hinv var hx k Vvar
  have hbase :=
    frameCoeffLocal
      (I := I) S gInv frame hframe hinv var hx k Vbase
  calc
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
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
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
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
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

/-- Raise the local lowered connection-variation pairing formula to
Christoffel components. -/
theorem christoffelEvolutionEquationInFrameOn_of_pairing_local
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
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
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

end Components

end DifferentialGeometry.PDE.RicciFlow
