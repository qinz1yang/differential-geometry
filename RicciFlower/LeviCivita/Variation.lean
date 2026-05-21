import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.Curvature.Basic
import RicciFlower.Curvature.Components
import RicciFlower.LeviCivita.Basic
import RicciFlower.LeviCivita.Torsion
import RicciFlower.Variation.Basic
import RicciFlower.VectorBundle.PartialMfderiv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Coordinate proof layer for Levi-Civita variations

This file contains the coordinate and local-frame proof tools needed by
Perelman's formula 5.10.  The book-facing definition of a variation path lives
in `RicciFlower.Variation.Basic`; the predicates in this file are component
packages extracted from such a path plus higher space/time regularity.

The central producer is `lcGammaVar`: from a path of Levi-Civita connections,
raw metric-component derivatives, fixed-base covariant derivatives of the
metric variation, and derivatives of Christoffel components, it derives the
standard formula

`delta Gamma^k_ij = 1/2 g^{kl} (nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`.
-/

noncomputable section

namespace RicciFlower
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

/-- Difference of two time-slice connections evaluated on a fixed local frame. -/
def connDiffVec
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j : Idx) : TangentSpace I x :=
  (G.connection var (frame j) x) (frame i x) -
    (G.connection base (frame j) x) (frame i x)

/-- Lowered connection difference with an explicitly chosen metric time. -/
def connDiffLow
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base var : Real) (x : M) (i j l : Idx) : Real :=
  (G.metric metricTime).inner x
    (connDiffVec (I := I) G frame base var x i j) (frame l x)

@[simp] theorem connDiffVec_self
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j : Idx) :
    connDiffVec (I := I) G frame base base x i j = 0 := by
  simp [connDiffVec]

@[simp] theorem connDiffLow_self
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base : Real) (x : M) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base base x i j l = 0 := by
  simp [connDiffLow]

/-- Fixed-base covariant derivative of the metric components of `g_var`.

The connection is frozen at `base`, while the metric is evaluated at `var`. -/
def metricCovAtBase
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => (G.metric var).inner y (frame a y) (frame b y))
      x (frame d x) -
    (G.metric var).inner x
      ((G.connection base (frame a) x) (frame d x)) (frame b x) -
    (G.metric var).inner x (frame a x)
      ((G.connection base (frame b) x) (frame d x))

/-- The lowered metric-variation RHS
`1/2 (nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`. -/
def metricVarLowerRHS
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j l : Idx) : Real :=
  (1 / 2 : Real) *
    (metricCovDerivDt x i j l + metricCovDerivDt x j i l -
      metricCovDerivDt x l i j)

/-- The raised Christoffel metric-variation RHS
`1/2 g^{kl} (nabla_i v_jl + nabla_j v_il - nabla_l v_ij)`. -/
def metricVarGammaRHS
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l

/-- Metric trace of the fixed-base covariant derivative of the metric
variation: `nabla_j V = g^{pl} nabla_j v_pl`. -/
def metricTraceCovAt
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (j : Idx) : Real :=
  ∑ p : Idx, ∑ l : Idx, gInv x p l * metricCovDerivDt x j p l

/-- Local derivative package for the fixed-base covariant derivative of the
metric components. -/
def metricCovVarOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ d a b : Idx,
    HasDerivAt
      (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b)
      (metricCovDerivDt x d a b)
      base

/-- The fixed-base covariant derivative of a symmetric metric remains
symmetric in the two metric slots. -/
theorem metricCovAtBase_symm
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) :
    metricCovAtBase (I := I) G frame base var x d a b =
      metricCovAtBase (I := I) G frame base var x d b a := by
  unfold metricCovAtBase
  have hfun :
      (fun y : M => (G.metric var).inner y (frame a y) (frame b y)) =
        fun y : M => (G.metric var).inner y (frame b y) (frame a y) := by
    funext y
    exact (G.metric var).symm y (frame a y) (frame b y)
  rw [hfun]
  rw [(G.metric var).symm x
    ((G.connection base (frame b) x) (frame d x)) (frame a x)]
  rw [(G.metric var).symm x
    (frame b x) ((G.connection base (frame a) x) (frame d x))]
  ring

/-- The supplied derivative of the fixed-base metric covariant derivative is
symmetric in the two metric slots. -/
theorem metricCovVar_symm
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt) :
    ∀ x : M, x ∈ u -> ∀ d a b : Idx,
      metricCovDerivDt x d a b = metricCovDerivDt x d b a := by
  intro x hx d a b
  have h₁ := hmetric x hx d a b
  have h₂ := hmetric x hx d b a
  have hEq :
      (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b) =ᶠ[nhds base]
        fun s : Real => metricCovAtBase (I := I) G frame base s x d b a := by
    exact Filter.Eventually.of_forall fun s =>
      metricCovAtBase_symm (I := I) G frame base s x d a b
  exact h₁.unique (h₂.congr_of_eventuallyEq hEq)

/-- Local derivative package for raw metric components `g_s(e_a,e_b)`. -/
def metricVarOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ a b : Idx,
    HasDerivAt
      (fun s : Real => (G.metric s).inner x (frame a x) (frame b x))
      (metricDot x a b)
      base

/-- Components of the metric-variation tensor in a fixed frame. -/
def metricDotFrame
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (a b : Idx) : Real :=
  Variation.metricVariationComponent (I := I) metricVariation x
    (frame a x) (frame b x)

/-- An admissible metric-potential variation path gives the raw fixed-frame
metric-component derivative. -/
theorem metricVar_path
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation : M -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (hpath :
      Variation.IsMetricPotentialVariationPath (I := I) path metricVariation
        potentialVariation) :
    metricVarOn (I := I) path.G frame path.base u
      (metricDotFrame (I := I) metricVariation frame) := by
  intro x _hx a b
  simpa [metricDotFrame] using
    hpath.metric_deriv x (frame a x) (frame b x)

/-- Mixed regularity for an arbitrary metric variation: differentiating the
fixed-frame spatial derivative of a metric component in time gives the spatial
derivative of the metric variation component. -/
def metricExtDtOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ d a b : Idx,
    HasDerivAt
      (fun s : Real =>
        extDerivFun (I := I)
          (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
          x (frame d x))
      (extDerivFun (I := I) (fun y : M => metricDot y a b) x (frame d x))
      base

/-- Chart/model mixed regularity gives `metricExtDtOn`.

This theorem keeps the regularity input as an explicit analytic hypothesis,
instead of bundling it as a field of a component package. -/
theorem metricExtDt_chart
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real)
    (hchart :
      ∀ x : M, x ∈ u -> ∀ d a b : Idx,
        HasDerivAt
          (fun s : Real =>
            extDerivFun (I := I)
              (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
              x (frame d x))
          (extDerivFun (I := I) (fun y : M => metricDot y a b) x
            (frame d x))
          base) :
    metricExtDtOn (I := I) G frame base u metricDot := by
  intro x hx d a b
  exact hchart x hx d a b

/-- Fixed-frame covariant derivative components of an arbitrary metric
variation tensor. -/
def dotCovAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricDot : M -> Idx -> Idx -> Real)
    (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => metricDot y a b) x (frame d x) -
    (∑ p : Idx,
      Coordinates.christoffelSymbolInFrame cov frame hframe x d a p *
        metricDot x p b) -
    (∑ p : Idx,
      Coordinates.christoffelSymbolInFrame cov frame hframe x d b p *
        metricDot x a p)

private theorem localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

private theorem metricVarConnLeft
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    {x : M} (hx : x ∈ u) (d a b : Idx) :
    HasDerivAt
      (fun s : Real =>
        (G.metric s).inner x
          ((G.connection base (frame a) x) (frame d x)) (frame b x))
      (∑ p : Idx,
        Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x d a p *
          metricDot x p b)
      base := by
  classical
  let Γ : Idx -> Real := fun p =>
    Coordinates.christoffelSymbolInFrame
      (G.connection base) frame hframe x d a p
  have hcov :
      (G.connection base (frame a) x) (frame d x) =
        ∑ p : Idx, Γ p • frame p x := by
    simpa [Γ] using
      hframe.coeff_sum_eq
        (fun y => (G.connection base (frame a) y) (frame d y)) hx
  have hsum :
      HasDerivAt
        (fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame p x) (frame b x))
        (∑ p : Idx, Γ p * metricDot x p b)
        base := by
    simpa using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun p s =>
          Γ p * (G.metric s).inner x (frame p x) (frame b x))
        (A' := fun p => Γ p * metricDot x p b)
        (x := base)
        (fun p _hp => by
          simpa using (hmetricVar x hx p b).const_mul (Γ p)))
  have hEq :
      (fun s : Real =>
        (G.metric s).inner x
          ((G.connection base (frame a) x) (frame d x)) (frame b x)) =
        fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame p x) (frame b x) := by
    funext s
    rw [hcov]
    simp [map_sum, Γ]
  simpa [hEq, Γ] using hsum

private theorem metricVarConnRight
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    {x : M} (hx : x ∈ u) (d a b : Idx) :
    HasDerivAt
      (fun s : Real =>
        (G.metric s).inner x (frame a x)
          ((G.connection base (frame b) x) (frame d x)))
      (∑ p : Idx,
        Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x d b p *
          metricDot x a p)
      base := by
  classical
  let Γ : Idx -> Real := fun p =>
    Coordinates.christoffelSymbolInFrame
      (G.connection base) frame hframe x d b p
  have hcov :
      (G.connection base (frame b) x) (frame d x) =
        ∑ p : Idx, Γ p • frame p x := by
    simpa [Γ] using
      hframe.coeff_sum_eq
        (fun y => (G.connection base (frame b) y) (frame d y)) hx
  have hsum :
      HasDerivAt
        (fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame a x) (frame p x))
        (∑ p : Idx, Γ p * metricDot x a p)
        base := by
    simpa using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun p s =>
          Γ p * (G.metric s).inner x (frame a x) (frame p x))
        (A' := fun p => Γ p * metricDot x a p)
        (x := base)
        (fun p _hp => by
          simpa using (hmetricVar x hx a p).const_mul (Γ p)))
  have hEq :
      (fun s : Real =>
        (G.metric s).inner x (frame a x)
          ((G.connection base (frame b) x) (frame d x))) =
        fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame a x) (frame p x) := by
    funext s
    rw [hcov]
    simp [map_sum, Γ]
  simpa [hEq, Γ] using hsum

/-- The derivative of the fixed-base metric-covariant component is the
fixed-base covariant derivative of the metric variation component. -/
theorem covDtEqDotCov
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hmetric : metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (hExt : metricExtDtOn (I := I) G frame base u metricDot) :
    ∀ x : M, x ∈ u -> ∀ d a b : Idx,
      metricCovDerivDt x d a b =
        dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b := by
  intro x hx d a b
  let Ca : TangentSpace I x :=
    (G.connection base (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (G.connection base (frame b) x) (frame d x)
  have hDeriv :
      HasDerivAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
              x (frame d x) -
            (G.metric s).inner x Ca (frame b x) -
            (G.metric s).inner x (frame a x) Cb)
        (dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b)
        base := by
    have hExt' := hExt x hx d a b
    have hCa := metricVarConnLeft
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCb := metricVarConnRight
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCa' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x Ca (frame b x))
          (∑ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d a p *
              metricDot x p b)
          base := by
      simpa [Ca] using hCa
    have hCb' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x (frame a x) Cb)
          (∑ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d b p *
              metricDot x a p)
          base := by
      simpa [Cb] using hCb
    have h0 := (hExt'.sub hCa').sub hCb'
    refine h0.congr_deriv ?_
    unfold dotCovAt
    ring
  have hDeriv' :
      HasDerivAt
        (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b)
        (dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b)
        base := by
    refine hDeriv.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by
      simp [metricCovAtBase, Ca, Cb]
  exact (hmetric x hx d a b).unique hDeriv'

/-- The fixed-base covariant derivative of the metric path varies by the
covariant derivative of the metric variation tensor.

This is the general arbitrary-variation version of the Ricci-flow
metric-covariant derivative bridge. -/
theorem metricCovVar_ext
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hExt : metricExtDtOn (I := I) G frame base u metricDot) :
    metricCovVarOn (I := I) G frame base u
      (dotCovAt (I := I) (G.connection base) frame hframe metricDot) := by
  intro x hx d a b
  let Ca : TangentSpace I x :=
    (G.connection base (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (G.connection base (frame b) x) (frame d x)
  have hDeriv :
      HasDerivAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
              x (frame d x) -
            (G.metric s).inner x Ca (frame b x) -
            (G.metric s).inner x (frame a x) Cb)
        (dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b)
        base := by
    have hExt' := hExt x hx d a b
    have hCa := metricVarConnLeft
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCb := metricVarConnRight
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCa' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x Ca (frame b x))
          (∑ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d a p *
              metricDot x p b)
          base := by
      simpa [Ca] using hCa
    have hCb' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x (frame a x) Cb)
          (∑ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d b p *
              metricDot x a p)
          base := by
      simpa [Cb] using hCb
    have h0 := (hExt'.sub hCa').sub hCb'
    refine h0.congr_deriv ?_
    unfold dotCovAt
    ring
  refine hDeriv.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => by
    simp [metricCovAtBase, Ca, Cb]

private theorem connDiffVec_symm
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (i j : Idx) :
    connDiffVec (I := I) G frame base var x i j =
      connDiffVec (I := I) G frame base var x j i := by
  have hfi : MDiffAt (T% (frame i)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hfj : MDiffAt (T% (frame j)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx j
  have hvar_torsion :=
    RicciFlower.LeviCivita.torsion_free_apply
      (I := I) (hLC var).2 (hX := hfi) (hY := hfj)
  have hbase_torsion :=
    RicciFlower.LeviCivita.torsion_free_apply
      (I := I) (hLC base).2 (hX := hfi) (hY := hfj)
  have hdiff :
      (G.connection var (frame j) x) (frame i x) -
          (G.connection var (frame i) x) (frame j x) =
        (G.connection base (frame j) x) (frame i x) -
          (G.connection base (frame i) x) (frame j x) := by
    exact hvar_torsion.trans hbase_torsion.symm
  unfold connDiffVec
  apply sub_eq_zero.mp
  calc
    ((G.connection var (frame j) x) (frame i x) -
          (G.connection base (frame j) x) (frame i x)) -
        ((G.connection var (frame i) x) (frame j x) -
          (G.connection base (frame i) x) (frame j x))
        =
      ((G.connection var (frame j) x) (frame i x) -
          (G.connection var (frame i) x) (frame j x)) -
        ((G.connection base (frame j) x) (frame i x) -
          (G.connection base (frame i) x) (frame j x)) := by
        abel
    _ = 0 := by
        rw [hdiff, sub_self]

private theorem connDiffLow_symm
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (metricTime base var : Real) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base var x i j l =
      connDiffLow (I := I) G frame metricTime base var x j i l := by
  unfold connDiffLow
  rw [connDiffVec_symm (I := I) G hLC frame hframe hu hx base var i j]

/-- Metric compatibility rewrites `(nabla^base_d g_var)_{ab}` as the two
connection-difference terms produced by changing the Levi-Civita connection
from `base` to `var`. -/
theorem metricCovAtBase_eq_connDiff
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (d a b : Idx) :
    metricCovAtBase (I := I) G frame base var x d a b =
      connDiffLow (I := I) G frame var base var x d a b +
        (G.metric var).inner x (frame a x)
          (connDiffVec (I := I) G frame base var x d b) := by
  have hfd : MDiffAt (T% (frame d)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx d
  have hfa : MDiffAt (T% (frame a)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hfb : MDiffAt (T% (frame b)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmc :=
    RicciFlower.Connection.metric_compatible_apply
      (I := I) (hLC var).1 (frame d) (frame a) (frame b) hfd hfa hfb
  unfold metricCovAtBase connDiffLow connDiffVec
  have hmc' :
      extDerivFun (I := I)
          (fun y : M => (G.metric var).inner y (frame a y) (frame b y))
          x (frame d x) =
        (G.metric var).inner x
            ((G.connection var (frame a) x) (frame d x)) (frame b x) +
          (G.metric var).inner x (frame a x)
            ((G.connection var (frame b) x) (frame d x)) := by
    simpa [extDerivFun] using hmc
  rw [hmc']
  simp
  ring

/-- Finite-difference Koszul formula for two Levi-Civita connections in the
same fixed local frame. -/
theorem finiteDiffKoszul
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (i j l : Idx) :
    2 * connDiffLow (I := I) G frame var base var x i j l =
      metricCovAtBase (I := I) G frame base var x i j l +
        metricCovAtBase (I := I) G frame base var x j i l -
          metricCovAtBase (I := I) G frame base var x l i j := by
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var i j l]
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var j i l]
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var l i j]
  have hji := connDiffLow_symm
    (I := I) G hLC frame hframe hu hx var base var j i l
  have hli := connDiffLow_symm
    (I := I) G hLC frame hframe hu hx var base var l i j
  have hlj := connDiffVec_symm
    (I := I) G hLC frame hframe hu hx base var l j
  have hsym1 :
      (G.metric var).inner x (frame j x)
          (connDiffVec (I := I) G frame base var x i l) =
        connDiffLow (I := I) G frame var base var x i l j := by
    unfold connDiffLow
    exact (G.metric var).symm x (frame j x)
      (connDiffVec (I := I) G frame base var x i l)
  rw [hji, hli, hlj, hsym1]
  ring

/-- Variable-metric lowered connection difference expressed by Christoffel
component differences in the fixed local frame. -/
theorem connDiffLow_eq_sum_gammaSub [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (metricTime base var : Real) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base var x i j l =
      ∑ k : Idx,
        (Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame k x) (frame l x) := by
  let Vvar : TangentSpace I x :=
    (G.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (G.connection base (frame j) x) (frame i x)
  have hvar :
      Vvar =
        ∑ k : Idx,
          Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k • frame k x := by
    simpa [Vvar, Coordinates.christoffelSymbolInFrame] using
      hframe.coeff_sum_eq
        (fun y : M => (G.connection var (frame j) y) (frame i y)) hx
  have hbase :
      Vbase =
        ∑ k : Idx,
          Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k • frame k x := by
    simpa [Vbase, Coordinates.christoffelSymbolInFrame] using
      hframe.coeff_sum_eq
        (fun y : M => (G.connection base (frame j) y) (frame i y)) hx
  have hdiff :
      Vvar - Vbase =
        ∑ k : Idx,
          (Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x := by
    calc
      Vvar - Vbase =
          (∑ k : Idx,
            Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k • frame k x) -
            (∑ k : Idx,
              Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x i j k • frame k x) := by
            rw [hvar, hbase]
      _ = ∑ k : Idx,
            (Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k • frame k x -
              Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x i j k • frame k x) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Idx,
            (Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k -
              Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x i j k) • frame k x := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [sub_smul]
  calc
    connDiffLow (I := I) G frame metricTime base var x i j l =
        (G.metric metricTime).inner x (Vvar - Vbase) (frame l x) := by
          rfl
    _ = (G.metric metricTime).inner x
        (∑ k : Idx,
          (Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x)
        (frame l x) := by
          rw [hdiff]
    _ = (G.metric metricTime).inner x (frame l x)
        (∑ k : Idx,
          (Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x) := by
          rw [(G.metric metricTime).symm x]
    _ = ∑ k : Idx,
        (Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame l x) (frame k x) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ k : Idx,
        (Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame k x) (frame l x) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [(G.metric metricTime).symm x (frame l x) (frame k x)]

/-- Local derivative package for Christoffel components in a fixed frame. -/
def gammaDerivOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real) (u : Set M)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j k : Idx,
    HasDerivAt
      (fun s : Real =>
        Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k)
      (gammaDot x k i j)
      base

/-- Chart-level Christoffel derivative regularity gives the fixed-frame
Christoffel derivative package. -/
theorem gammaDeriv_chart
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real) (u : Set M)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hchart :
      ∀ x : M, x ∈ u -> ∀ i j k : Idx,
        HasDerivAt
          (fun s : Real =>
            Coordinates.christoffelSymbolInFrame
              (G.connection s) frame hframe x i j k)
          (gammaDot x k i j)
          base) :
    gammaDerivOn (I := I) G frame hframe base u gammaDot := by
  intro x hx i j k
  exact hchart x hx i j k

/-- Product-rule bridge: the variable-metric lowered connection difference has
derivative obtained by lowering `gammaDot` with the base metric. -/
theorem varLowDeriv [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hgamma : gammaDerivOn (I := I) G frame hframe base u gammaDot)
    {x : M} (hx : x ∈ u) (i j l : Idx) :
    HasDerivAt
      (fun s : Real => connDiffLow (I := I) G frame s base s x i j l)
      (∑ k : Idx,
        gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
      base := by
  let gammaSub : Idx -> Real -> Real :=
    fun k s =>
      Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k -
        Coordinates.christoffelSymbolInFrame
          (G.connection base) frame hframe x i j k
  let metricComp : Idx -> Real -> Real :=
    fun k s => (G.metric s).inner x (frame k x) (frame l x)
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ k : Idx, gammaSub k s * metricComp k s)
        (∑ k : Idx,
          gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
        base := by
    simpa [gammaSub, metricComp] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun k s => gammaSub k s * metricComp k s)
        (A' := fun k =>
          gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
        (x := base)
        (fun k _hk => by
          have hγ :
              HasDerivAt (fun s : Real => gammaSub k s)
                (gammaDot x k i j) base := by
            simpa [gammaSub] using
              (hgamma x hx i j k).sub_const
                (Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x i j k)
          have hm :
              HasDerivAt (fun s : Real => metricComp k s)
                (metricDot x k l) base := by
            simpa [metricComp] using hmetricVar x hx k l
          have hmul := hγ.mul hm
          simpa [gammaSub, metricComp] using hmul))
  have hEq :
      (fun s : Real => connDiffLow (I := I) G frame s base s x i j l) =ᶠ[nhds base]
        (fun s : Real => ∑ k : Idx, gammaSub k s * metricComp k s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [gammaSub, metricComp] using
        connDiffLow_eq_sum_gammaSub (I := I) G frame hframe hx s base s i j l
  exact hsum.congr_of_eventuallyEq hEq

/-- Local arbitrary metric-variation Christoffel formula in a fixed frame. -/
def gammaVarEqOn
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j k : Idx,
    gammaDot x k i j =
      metricVarGammaRHS gInv metricCovDerivDt x i j k

/-- Trace of the raised Christoffel variation:
`delta Gamma^p_pj = 1/2 * nabla_j V`. -/
theorem gammaTraceVar
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (u : Set M)
    (hgInv_symm : ∀ x : M, x ∈ u -> ∀ i j : Idx,
      gInv x i j = gInv x j i)
    (hmetric_symm : ∀ x : M, x ∈ u -> ∀ d a b : Idx,
      metricCovDerivDt x d a b = metricCovDerivDt x d b a)
    (hgamma : gammaVarEqOn gInv metricCovDerivDt gammaDot u) :
    ∀ x : M, x ∈ u -> ∀ j : Idx,
      (∑ p : Idx, gammaDot x p p j) =
        (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x j := by
  classical
  intro x hx j
  let A : Real :=
    ∑ p : Idx, ∑ l : Idx,
      gInv x p l * metricCovDerivDt x p j l * (1 / 2 : Real)
  let B : Real :=
    ∑ p : Idx, ∑ l : Idx,
      gInv x p l * metricCovDerivDt x j p l * (1 / 2 : Real)
  let C : Real :=
    ∑ p : Idx, ∑ l : Idx,
      gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real)
  have hCA : C = A := by
    calc
      C = ∑ l : Idx, ∑ p : Idx,
          gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real) := by
            change (∑ p : Idx, ∑ l : Idx,
              gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real)) =
                ∑ l : Idx, ∑ p : Idx,
                  gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real)
            rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ p : Idx,
          gInv x l p * metricCovDerivDt x l j p * (1 / 2 : Real) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hgInv_symm x hx p l, hmetric_symm x hx l p j]
      _ = A := by
            rfl
  have hsum :
      (∑ p : Idx, gammaDot x p p j) =
        A + B - C := by
    calc
      (∑ p : Idx, gammaDot x p p j) =
          ∑ p : Idx, metricVarGammaRHS gInv metricCovDerivDt x p j p := by
            refine Finset.sum_congr rfl fun p _ => ?_
            exact hgamma x hx p j p
      _ = A + B - C := by
            unfold A B C metricVarGammaRHS metricVarLowerRHS
            symm
            rw [← Finset.sum_add_distrib]
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.sum_add_distrib]
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
  calc
    (∑ p : Idx, gammaDot x p p j)
        = A + B - C := hsum
    _ = B := by
        rw [hCA]
        ring
    _ = (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x j := by
        simp [B, metricTraceCovAt, Finset.mul_sum, mul_comm, mul_assoc]

/-- A static frame coefficient is obtained by raising the frozen metric
pairings with inverse metric components. -/
theorem coeff_invMetric [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) g gInv frame)
    {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
  let basis := hframe.toBasisAt hx
  have hcoord :
      basis.coord k V =
        ∑ l : Idx, gInv x k l * g.inner x (basis l) V := by
    symm
    calc
      (∑ l : Idx, gInv x k l * g.inner x (basis l) V)
          = ∑ l : Idx, gInv x k l *
              g.inner x (basis l) (∑ j : Idx, basis.coord j V • basis j) := by
            rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
      _ = ∑ l : Idx, ∑ j : Idx,
            gInv x k l * (basis.coord j V * g.inner x (basis l) (basis j)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_sum]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j : Idx, basis.coord j V *
            (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = ∑ j : Idx, basis.coord j V * (if k = j then 1 else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [show
              (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) =
                (if k = j then 1 else 0) by
                  simpa [basis, IsLocalFrameOn.toBasisAt_coe] using (hinv x k j).1]
      _ = basis.coord k V := by
            simp
  calc
    hframe.coeff k x V = basis.coord k V := by
      simp [basis, IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
      simpa [basis, IsLocalFrameOn.toBasisAt_coe] using hcoord

/-- Derivative package for the frozen-metric lowered connection-variation
pairing.  The metric in the pairing is fixed at `base`; only the connection
varies. -/
def lowerPairDerivOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j l : Idx,
    HasDerivAt
      (fun s : Real =>
        (G.metric base).inner x (frame l x)
          ((G.connection s (frame j) x) (frame i x)))
      (lowerDot x i j l)
      base

/-- Raise a supplied lowered connection-variation pairing. -/
def gammaFromLower
    (gInv : Curvature.InverseMetricComponents M Idx)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv x k l * lowerDot x i j l

/-- A lowered pairing derivative gives the derivative of the Christoffel
components after raising with the frozen inverse metric. -/
theorem gammaDerivOfLower [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hlower : lowerPairDerivOn (I := I) G frame base u lowerDot) :
    gammaDerivOn (I := I) G frame hframe base u
      (fun x k i j => gammaFromLower gInv lowerDot x i j k) := by
  intro x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (G.metric base).inner x (frame l x)
        ((G.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s)
        (∑ l : Idx, gInv x k l * lowerDot x i j l)
        base := by
    simpa [pair] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv x k l * pair l s)
        (A' := fun l => gInv x k l * lowerDot x i j l)
        (x := base)
        (fun l _hl =>
          HasDerivAt.const_mul
            (gInv x k l) (hlower x hx i j l)))
  have hEq :
      (fun s : Real =>
        Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k) =ᶠ[nhds base]
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [Coordinates.christoffelSymbolInFrame, pair] using
        coeff_invMetric (I := I) (M := M)
          (G.metric base) gInv frame hframe hinv hx k
          ((G.connection s (frame j) x) (frame i x))
  simpa [gammaFromLower, pair] using hsum.congr_of_eventuallyEq hEq

/-- Uniqueness of one-dimensional derivatives turns a produced Christoffel
derivative into the component formula for a supplied `gammaDot`. -/
theorem gammaEqOfDeriv
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hformula :
      gammaDerivOn (I := I) G frame hframe base u
        (fun x k i j =>
          gammaFromLower gInv (metricVarLowerRHS metricCovDerivDt) x i j k))
    (hgamma : gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have huniq := (hformula x hx i j k).unique (hgamma x hx i j k)
  simpa [metricVarGammaRHS, gammaFromLower] using huniq.symm

/-- Arbitrary Levi-Civita metric-variation producer for Christoffel symbols.

This is the non-Ricci-flow version of the calculation used in the connection
evolution file.  The proof should be extracted from the finite-difference
Koszul route there, replacing `SolutionOn` and `partial_t g = -2 Ric` by the
plain hypotheses below. -/
theorem lcGammaVar [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (_hu : IsOpen u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (_hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hmetricVar :
      metricVarOn (I := I) G frame base u metricDot)
    (_hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (_hgamma :
      gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have hlow :
      ∀ l : Idx,
        (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    have hL :
        HasDerivAt
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := by
      exact HasDerivAt.const_mul (2 : Real)
        (varLowDeriv (I := I) G frame hframe base metricDot gammaDot
          hmetricVar _hgamma hx i j l)
    have hR :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j)
          base := by
      exact ((_hmetric x hx i j l).add (_hmetric x hx j i l)).sub
        (_hmetric x hx l i j)
    have hEq :
        (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j) =ᶠ[nhds base]
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l) := by
      exact Filter.Eventually.of_forall fun s => by
        exact (finiteDiffKoszul (I := I) G hLC frame hframe _hu hx base s i j l).symm
    have hL_as_R :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := hL.congr_of_eventuallyEq hEq
    have hderiv :
        2 * (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j :=
      hL_as_R.unique hR
    unfold metricVarLowerRHS
    linarith
  let V : TangentSpace I x :=
    ∑ a : Idx, gammaDot x a i j • frame a x
  have hcoeff :
      hframe.coeff k x V = gammaDot x k i j := by
    let basis := hframe.toBasisAt hx
    have hbasis :
        ∀ a : Idx, basis.repr (frame a x) k = if a = k then 1 else 0 := by
      intro a
      have hframe_eq : frame a x = basis a := by
        simp [basis]
      rw [hframe_eq]
      by_cases h : a = k
      · subst k
        simp
      · simp [h]
    calc
      hframe.coeff k x V = basis.repr V k := by
        simp [basis, IsLocalFrameOn.coeff, hx]
      _ = ∑ a : Idx, gammaDot x a i j * basis.repr (frame a x) k := by
        simp [V, map_sum, map_smul, smul_eq_mul]
      _ = ∑ a : Idx, gammaDot x a i j * (if a = k then 1 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hbasis a]
      _ = gammaDot x k i j := by
        simp
  have hinner :
      ∀ l : Idx,
        (G.metric base).inner x (frame l x) V =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    calc
      (G.metric base).inner x (frame l x) V =
          ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame l x) (frame a x) := by
            simp [V, map_sum, smul_eq_mul]
      _ = ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [(G.metric base).symm x (frame l x) (frame a x)]
      _ = metricVarLowerRHS metricCovDerivDt x i j l := hlow l
  calc
    gammaDot x k i j = hframe.coeff k x V := hcoeff.symm
    _ = ∑ l : Idx, gInv x k l * (G.metric base).inner x (frame l x) V := by
      exact coeff_invMetric (I := I) (M := M)
        (G.metric base) gInv frame hframe _hinv hx k V
    _ = ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hinner l]
    _ = metricVarGammaRHS gInv metricCovDerivDt x i j k := by
      rfl

/-- Trace form of `lcGammaVar`: `delta Gamma^p_pj = 1/2 nabla_j V`. -/
theorem gammaTraceVar_of_lcGammaVar [DecidableEq Idx]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hmetricVar :
      metricVarOn (I := I) G frame base u metricDot)
    (hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (hgamma :
      gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    ∀ x : M, x ∈ u -> ∀ j : Idx,
      (∑ p : Idx, gammaDot x p p j) =
        (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x j := by
  have hgammaEq :
      gammaVarEqOn gInv metricCovDerivDt gammaDot u :=
    lcGammaVar (I := I) G hLC gInv frame hframe hu base metricDot
      metricCovDerivDt gammaDot hinv hmetricVar hmetric hgamma
  have hgInv_symm :
      ∀ x : M, x ∈ u -> ∀ i j : Idx, gInv x i j = gInv x j i := by
    intro x _ i j
    exact Curvature.invComp_symm (I := I) (g := G.metric base)
      (gInv := gInv) frame hinv x i j
  have hmetric_symm :
      ∀ x : M, x ∈ u -> ∀ d a b : Idx,
        metricCovDerivDt x d a b = metricCovDerivDt x d b a :=
    metricCovVar_symm (I := I) G frame base u metricCovDerivDt hmetric
  exact gammaTraceVar gInv metricCovDerivDt gammaDot u
    hgInv_symm hmetric_symm hgammaEq

/-! ## Coordinate Ricci variation from Christoffel variation -/

section RicciCoordVariation

open RicciFlower.Coordinates

variable [DecidableEq (CoordinateIdx (𝕜 := Real) E)]

/-- Finite trace contraction of a two-index object against inverse-metric
components.  This is the scalar trace algebra used when contracting the
variation of `Ric + Hess f`. -/
def trace2
    {ι : Type*} [Fintype ι]
    (gInv T : ι -> ι -> Real) : Real :=
  ∑ i : ι, ∑ j : ι, gInv i j * T i j

/-- Product rule for the finite trace contraction `trace2`. -/
theorem trace2_deriv
    {ι : Type*} [Fintype ι]
    {timeSet : Set Real} {base : Real}
    {gInvPath TPath : Real -> ι -> ι -> Real}
    {gInvDot TDot : ι -> ι -> Real}
    (hgInv :
      ∀ i j : ι,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (hT :
      ∀ i j : ι,
        HasDerivWithinAt (fun s : Real => TPath s i j)
          (TDot i j) timeSet base) :
    HasDerivWithinAt
      (fun s : Real => trace2 (gInvPath s) (TPath s))
      ((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          gInvDot i j * TPath base i j + gInvPath base i j * TDot i j)
      timeSet base := by
  unfold trace2
  refine HasDerivWithinAt.fun_sum ?_
  intro i _
  refine HasDerivWithinAt.fun_sum ?_
  intro j _
  simpa [mul_add] using (hgInv i j).mul (hT i j)

/-- Algebraic normalization of the inverse-metric part of a traced variation.
If `metricVariation` is the contravariant metric variation, i.e.
`gInvDot = -metricVariation`, then the `gInvDot` contraction contributes
`-trace2 metricVariation T`. -/
theorem trace2_neg
    {ι : Type*} [Fintype ι]
    (gInvDot metricVariation T U : ι -> ι -> Real)
    (h : ∀ i j : ι, gInvDot i j = -metricVariation i j) :
    ((Finset.univ : Finset ι).sum fun i =>
      (Finset.univ : Finset ι).sum fun j =>
        gInvDot i j * T i j + U i j) =
      -trace2 metricVariation T +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
  classical
  unfold trace2
  calc
    ((Finset.univ : Finset ι).sum fun i =>
      (Finset.univ : Finset ι).sum fun j =>
        gInvDot i j * T i j + U i j)
        =
      ((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          gInvDot i j * T i j) +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
        simp [Finset.sum_add_distrib]
    _ =
      ((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          -metricVariation i j * T i j) +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
        refine congrArg (fun z =>
          z + ((Finset.univ : Finset ι).sum fun i =>
            (Finset.univ : Finset ι).sum fun j => U i j)) ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h i j]
    _ =
      -((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          metricVariation i j * T i j) +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
        simp [Finset.sum_neg_distrib]

private def covDGamma
    {ι : Type*} [Fintype ι]
    (Gamma A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (dir k i j : ι) : Real :=
  dA dir i j k +
    (∑ a : ι, Gamma dir a k * A i j a) -
    (∑ a : ι, Gamma dir i a * A a j k) -
    (∑ a : ι, Gamma dir j a * A i a k)

private theorem curvVarAlg
    {ι : Type*} [Fintype ι]
    (Gamma A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (hGammaSymm : ∀ a b c : ι, Gamma a b c = Gamma b a c)
    (i k j m : ι) :
    dA i k j m - dA k i j m +
        (∑ a : ι, (A k j a * Gamma i a m + Gamma k j a * A i a m)) -
        (∑ a : ι, (A i j a * Gamma k a m + Gamma i j a * A k a m)) =
      covDGamma Gamma A dA i m k j -
        covDGamma Gamma A dA k m i j := by
  classical
  unfold covDGamma
  have hmid :
      (∑ a : ι, Gamma i k a * A a j m) =
        ∑ a : ι, Gamma k i a * A a j m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hGammaSymm i k a]
  have hleft :
      (∑ a : ι, A k j a * Gamma i a m) =
        ∑ a : ι, Gamma i a m * A k j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hright :
      (∑ a : ι, A i j a * Gamma k a m) =
        ∑ a : ι, Gamma k a m * A i j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleft, hright, hmid]
  ring

/-- Time derivative package for coordinate Christoffel components at a fixed
coordinate center.  The supplied `gammaDot x k i j` is `d/ds Gamma^k_ij`. -/
def gammaCoordDerivAt
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ i j k : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCoordAt (I := I) (G.connection s) x0 i j k)
      (gammaDot x0 k i j)
      timeSet
      base

/-- Mixed time/spatial derivative package for coordinate Christoffel
components at a fixed coordinate center. -/
def gammaMixedCoordAt
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ dir i j k : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCoordDerivAt (I := I) (G.connection s)
          x0 dir i j k)
      (extDerivFun (I := I) (fun y : M => gammaDot y k i j) x0
        (coordinateFrameAt (I := I) x0 dir x0))
      timeSet
      base

/-- Coordinate covariant derivative of a Christoffel variation tensor
`A^k_ij = gammaDot x k i j`. -/
def gammaCovCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M)
    (dir k i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (fun y : M => gammaDot y k i j) x0
      (coordinateFrameAt (I := I) x0 dir x0) +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x0 dir a k *
        gammaDot x0 a i j) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x0 dir i a *
        gammaDot x0 k a j) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x0 dir j a *
        gammaDot x0 k i a)

/-- Fixed-coordinate expression for `nabla_i (delta Gamma^p_pj)`. -/
def gammaTraceCovAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M) (dir j : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ p : CoordinateIdx (𝕜 := Real) E,
    gammaCovCoordAt (I := I) cov gammaDot x0 dir p p j

/-- Coordinate RHS of `delta Ric_ij = nabla_p A^p_ij - nabla_i A^p_pj`. -/
def ricciVarCoordRHS
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  (∑ p : CoordinateIdx (𝕜 := Real) E,
    gammaCovCoordAt (I := I) cov gammaDot x0 p p i j) -
    gammaTraceCovAt (I := I) cov gammaDot x0 i j

private theorem christoffelCoordAt_symm_of_lc
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    Realized.christoffelCoordAt (I := I) cov x0 i j k =
      Realized.christoffelCoordAt (I := I) cov x0 j i k := by
  have htf : RicciFlower.LeviCivita.IsTorsionFree (I := I) cov := hLC.2
  have hzero :
      (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff k x0
          (cov.torsion x0
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0)) = 0 := by
    rw [htf x0]
    simp
  have hskew := RicciFlower.LeviCivita.coordinate_torsion_coeff_eq_christoffel_skew
    (I := I) cov x0 i j k
  rw [hzero] at hskew
  simpa [Realized.christoffelCoordAt] using sub_eq_zero.mp hskew.symm

private theorem curvVarCoord
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hvar : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCurvCoeffAt (I := I) (G.connection s)
          x0 i k j m)
      (gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 i m k j -
        gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 k m i j)
      timeSet
      base := by
  classical
  have hD_i := hmix i k j m
  have hD_k := hmix k i j m
  have hGamma :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt
          (fun s : Real =>
            Realized.christoffelCoordAt (I := I) (G.connection s)
              x0 a b c)
          (gammaDot x0 c a b) timeSet base := by
    intro a b c
    exact hvar a b c
  have hprod_left :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (G.connection s)
              x0 k j a *
            Realized.christoffelCoordAt (I := I) (G.connection s)
              x0 i a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (gammaDot x0 a k j *
            Realized.christoffelCoordAt (I := I) (G.connection base)
              x0 i a m +
          Realized.christoffelCoordAt (I := I) (G.connection base)
              x0 k j a *
            gammaDot x0 m i a))
        timeSet
        base := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hGamma k j a).mul (hGamma i a m)))
  have hprod_right :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (G.connection s)
              x0 i j a *
            Realized.christoffelCoordAt (I := I) (G.connection s)
              x0 k a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (gammaDot x0 a i j *
            Realized.christoffelCoordAt (I := I) (G.connection base)
              x0 k a m +
          Realized.christoffelCoordAt (I := I) (G.connection base)
              x0 i j a *
            gammaDot x0 m k a))
        timeSet
        base := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hGamma i j a).mul (hGamma k a m)))
  have hraw :
      HasDerivWithinAt
        (fun s : Real =>
          Realized.christoffelCurvCoeffAt (I := I) (G.connection s)
            x0 i k j m)
        ((extDerivFun (I := I) (fun y : M => gammaDot y m k j) x0
            (coordinateFrameAt (I := I) x0 i x0) -
          extDerivFun (I := I) (fun y : M => gammaDot y m i j) x0
            (coordinateFrameAt (I := I) x0 k x0)) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (gammaDot x0 a k j *
              Realized.christoffelCoordAt (I := I)
                (G.connection base) x0 i a m +
            Realized.christoffelCoordAt (I := I)
                (G.connection base) x0 k j a *
              gammaDot x0 m i a)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (gammaDot x0 a i j *
              Realized.christoffelCoordAt (I := I)
                (G.connection base) x0 k a m +
            Realized.christoffelCoordAt (I := I)
                (G.connection base) x0 i j a *
              gammaDot x0 m k a)))
        timeSet
        base := by
    simpa [Realized.christoffelCurvCoeffAt, sub_eq_add_neg, add_assoc,
      Finset.sum_add_distrib] using
      (((hD_i.sub hD_k).add hprod_left).sub hprod_right)
  refine hraw.congr_deriv ?_
  have hsymm :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) (G.connection base) x0 a b c =
          Realized.christoffelCoordAt (I := I) (G.connection base) x0 b a c := by
    intro a b c
    exact christoffelCoordAt_symm_of_lc (I := I) (G.connection base)
      (G.metric base) (hLC base) x0 a b c
  let Gamma : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c =>
      Realized.christoffelCoordAt (I := I) (G.connection base) x0 a b c
  let A : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c => gammaDot x0 c a b
  let dA : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun dir a b c =>
      extDerivFun (I := I) (fun y : M => gammaDot y c a b) x0
        (coordinateFrameAt (I := I) x0 dir x0)
  have hGammaSymm :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E, Gamma a b c = Gamma b a c := by
    intro a b c
    exact hsymm a b c
  simpa [Gamma, A, dA, gammaCovCoordAt, covDGamma] using
    (curvVarAlg Gamma A dA hGammaSymm i k j m)

/-- Coordinate-frame Ricci variation from a supplied Christoffel variation:
`d Ric_ij / ds = nabla_p A^p_ij - nabla_i A^p_pj`. -/
theorem lcRicciVarCoord
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hvar : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelRicciCoeffAt (I := I) (G.connection s)
          x0 i j)
      (ricciVarCoordRHS (I := I) (G.connection base) gammaDot x0 i j)
      timeSet
      base := by
  classical
  have hsum :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCurvCoeffAt (I := I)
              (G.connection s) x0 k i j k)
        (∑ k : CoordinateIdx (𝕜 := Real) E,
          (gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 k k i j -
            gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 i k k j))
        timeSet
        base := by
    exact HasDerivWithinAt.fun_sum fun k _ =>
      curvVarCoord (I := I) G hLC timeSet base x0 gammaDot hvar hmix k i j k
  refine hsum.congr_deriv ?_
  simp [ricciVarCoordRHS, gammaTraceCovAt, Finset.sum_sub_distrib]

/-- First coordinate derivative of a scalar in the fixed coordinate frame. -/
def scalarCoordDerivAt
    (f : M -> Real) (x0 : M) (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) f x0 (coordinateFrameAt (I := I) x0 i x0)

/-- First coordinate derivative as a scalar function near a fixed coordinate
center. -/
def scalarCoordDerivFun
    (f : M -> Real) (x0 : M) (j : CoordinateIdx (𝕜 := Real) E)
    (x : M) : Real :=
  extDerivFun (I := I) f x (coordinateFrameAt (I := I) x0 j x)

/-- Second coordinate derivative of a scalar in the fixed coordinate frame. -/
def scalarCoordSecondAt
    (f : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (scalarCoordDerivFun (I := I) f x0 j) x0
    (coordinateFrameAt (I := I) x0 i x0)

/-- Exterior derivative is invariant under local equality near the evaluation
point. -/
private theorem extDerivFun_congr_eventually_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

/-- Directional derivative of the finite trace
`sum_p delta Gamma^p_pj`. -/
theorem traceExtSum
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E)
    (hmdiff :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) (fun y : M => gammaDot y p p j) x0
          (coordinateFrameAt (I := I) x0 i x0)) =
      extDerivFun (I := I)
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j)
        x0 (coordinateFrameAt (I := I) x0 i x0) := by
  classical
  let t : Finset (CoordinateIdx (𝕜 := Real) E) := Finset.univ
  let F : CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun p y => gammaDot y p p j
  have hsum := RicciFlower.Coordinates.extDerivFun_finset_sum_real
    (I := I) (t := t) (f := F)
    (x := x0) (v := coordinateFrameAt (I := I) x0 i x0)
    (by
      intro p _hp
      exact hmdiff p)
  have hfun :
      t.sum F =
        fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot y p p j := by
    funext y
    simp [t, F]
  rw [← hfun]
  simpa [t, F] using hsum.symm

/-- Pointwise trace of `delta Gamma`, after the metric trace derivative has
been identified. -/
theorem gammaTracePoint
    (gInv :
      Curvature.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (metricCovDerivDt gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (a : CoordinateIdx (𝕜 := Real) E)
    (hgammaTrace :
      (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
        (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x0 a)
    (hmetricTrace :
      metricTraceCovAt gInv metricCovDerivDt x0 a =
        scalarCoordDerivAt (I := I) metricTrace x0 a) :
    (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
      (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a := by
  rw [hgammaTrace, hmetricTrace]

/-- Derivative of the metric trace from the raw product rule, the contracted
inverse-metric covariant derivative cancellation, and the supplied covariant
derivative components of the metric variation. -/
theorem metricTraceCov_eq_deriv
    (gInv :
      Curvature.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricDot : M -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real)
    (metricCovDerivDt :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (j : CoordinateIdx (𝕜 := Real) E)
    (metricDotDeriv gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (htrace_deriv :
      scalarCoordDerivAt (I := I) metricTrace x0 j =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            (gInv x0 p l * metricDotDeriv p l +
              gInvDeriv p l * metricDot x0 p l))
    (hmetricCov :
      ∀ p l : CoordinateIdx (𝕜 := Real) E,
        metricCovDerivDt x0 j p l =
          metricDotDeriv p l -
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              Realized.christoffelCoordAt (I := I) cov x0 j p a *
                metricDot x0 a l) -
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              Realized.christoffelCoordAt (I := I) cov x0 j l a *
                metricDot x0 p a))
    (hinv_contract :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv p l * metricDot x0 p l) =
        -∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                Realized.christoffelCoordAt (I := I) cov x0 j p a *
                  metricDot x0 a l) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                Realized.christoffelCoordAt (I := I) cov x0 j l a *
                  metricDot x0 p a))) :
    metricTraceCovAt gInv metricCovDerivDt x0 j =
      scalarCoordDerivAt (I := I) metricTrace x0 j := by
  classical
  let corr :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun p l =>
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) cov x0 j p a *
          metricDot x0 a l) +
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) cov x0 j l a *
          metricDot x0 p a)
  calc
    metricTraceCovAt gInv metricCovDerivDt x0 j =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * (metricDotDeriv p l - corr p l) := by
          unfold metricTraceCovAt corr
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hmetricCov p l]
          ring
    _ =
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * metricDotDeriv p l) -
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * corr p l) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ =
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * metricDotDeriv p l) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInvDeriv p l * metricDot x0 p l) := by
          rw [hinv_contract]
          unfold corr
          ring
    _ = scalarCoordDerivAt (I := I) metricTrace x0 j := by
          rw [htrace_deriv]
          simp [Finset.sum_add_distrib]

/-- Product-rule derivative of the metric trace
`V = gInv^{pl} metricDot_pl` in a fixed frame direction. -/
theorem traceDerivAt
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricTrace : M -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {x : M} (d : Idx)
    (htrace :
      metricTrace =ᶠ[nhds x]
        fun y : M => ∑ p : Idx, ∑ l : Idx,
          gInv y p l * metricDot y p l)
    (hgInv_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y p l) x)
    (hmetricDot_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => metricDot y p l) x) :
    extDerivFun (I := I) metricTrace x (frame d x) =
      ∑ p : Idx, ∑ l : Idx,
        (gInv x p l *
          extDerivFun (I := I) (fun y : M => metricDot y p l)
            x (frame d x) +
        extDerivFun (I := I) (fun y : M => gInv y p l)
            x (frame d x) *
          metricDot x p l) := by
  classical
  have hcongr := extDerivFun_congr_eventually_real
    (I := I) (x := x) (frame d x) htrace
  rw [hcongr]
  have hmdiffInner : ∀ p : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ∑ l : Idx, gInv y p l * metricDot y p l) x := by
    intro p
    have hmd :=
      RicciFlower.Coordinates.mdiffAt_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv y p l * metricDot y p l)
        (by
          intro l _hl
          exact (hgInv_mdiff p l).mul (hmetricDot_mdiff p l))
    have hfun :
        ((Finset.univ : Finset Idx).sum
          (fun l : Idx => fun y : M =>
            gInv y p l * metricDot y p l)) =
          (fun y : M =>
            ∑ l : Idx, gInv y p l * metricDot y p l) := by
      funext y
      simp
    rw [← hfun]
    exact hmd
  have houter :
      extDerivFun (I := I)
          (fun y : M => ∑ p : Idx, ∑ l : Idx,
            gInv y p l * metricDot y p l)
          x (frame d x) =
        ∑ p : Idx,
          extDerivFun (I := I)
            (fun y : M => ∑ l : Idx, gInv y p l * metricDot y p l)
            x (frame d x) := by
    have hsum := RicciFlower.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun p y => ∑ l : Idx, gInv y p l * metricDot y p l)
      (x := x) (v := frame d x)
      (by
        intro p _hp
        exact hmdiffInner p)
    have hfun :
        ((Finset.univ : Finset Idx).sum
          (fun p : Idx => fun y : M =>
            ∑ l : Idx, gInv y p l * metricDot y p l)) =
          (fun y : M => ∑ p : Idx, ∑ l : Idx,
            gInv y p l * metricDot y p l) := by
      funext y
      simp
    rw [← hfun]
    exact hsum
  rw [houter]
  refine Finset.sum_congr rfl fun p _hp => ?_
  have hinner :
      extDerivFun (I := I)
          (fun y : M => ∑ l : Idx, gInv y p l * metricDot y p l)
          x (frame d x) =
        ∑ l : Idx,
          extDerivFun (I := I)
            (fun y : M => gInv y p l * metricDot y p l)
            x (frame d x) := by
    have hsum := RicciFlower.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun l y => gInv y p l * metricDot y p l)
      (x := x) (v := frame d x)
      (by
        intro l _hl
        exact (hgInv_mdiff p l).mul (hmetricDot_mdiff p l))
    have hfun :
        ((Finset.univ : Finset Idx).sum
          (fun l : Idx => fun y : M =>
            gInv y p l * metricDot y p l)) =
          (fun y : M =>
            ∑ l : Idx, gInv y p l * metricDot y p l) := by
      funext y
      simp
    rw [← hfun]
    exact hsum
  rw [hinner]
  refine Finset.sum_congr rfl fun l _hl => ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    RicciFlower.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) (frame d x)
      (hgInv_mdiff p l) (hmetricDot_mdiff p l)

private theorem traceCancelAlg
    {ι : Type*} [Fintype ι]
    (G V DU : ι -> ι -> Real)
    (Γ : ι -> ι -> Real)
    (hDU : ∀ p l : ι,
      DU p l =
        -((∑ a : ι, Γ a p * G a l) +
          (∑ a : ι, Γ a l * G p a))) :
    (∑ p : ι, ∑ l : ι, DU p l * V p l) =
      -∑ p : ι, ∑ l : ι,
        G p l *
          ((∑ a : ι, Γ p a * V a l) +
           (∑ a : ι, Γ l a * V p a)) := by
  classical
  have hfirst :
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a p * G a l) * V p l) =
        ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ p a * V a l) := by
    calc
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a p * G a l) * V p l)
          =
        ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ a p * G a l * V p l := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ a : ι, ∑ l : ι, ∑ p : ι,
          Γ a p * G a l * V p l := by
            calc
              (∑ p : ι, ∑ l : ι, ∑ a : ι,
                Γ a p * G a l * V p l)
                  =
                ∑ p : ι, ∑ a : ι, ∑ l : ι,
                  Γ a p * G a l * V p l := by
                    refine Finset.sum_congr rfl fun p _ => ?_
                    rw [Finset.sum_comm]
              _ = ∑ a : ι, ∑ p : ι, ∑ l : ι,
                  Γ a p * G a l * V p l := by
                    rw [Finset.sum_comm]
              _ = ∑ a : ι, ∑ l : ι, ∑ p : ι,
                  Γ a p * G a l * V p l := by
                    refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ p a * G p l * V a l := by
            simp
      _ = ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ p a * V a l) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring_nf
  have hsecond :
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a l * G p a) * V p l) =
        ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ l a * V p a) := by
    calc
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a l * G p a) * V p l)
          =
        ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ a l * G p a * V p l := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ p : ι, ∑ a : ι, ∑ l : ι,
          Γ a l * G p a * V p l := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ l a * G p l * V p a := by
            simp
      _ = ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ l a * V p a) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring_nf
  calc
    (∑ p : ι, ∑ l : ι, DU p l * V p l)
        =
      ∑ p : ι, ∑ l : ι,
        -((∑ a : ι, Γ a p * G a l) +
          (∑ a : ι, Γ a l * G p a)) * V p l := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hDU p l]
    _ =
      -((∑ p : ι, ∑ l : ι,
          (∑ a : ι, Γ a p * G a l) * V p l) +
        (∑ p : ι, ∑ l : ι,
          (∑ a : ι, Γ a l * G p a) * V p l)) := by
        simp [add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ =
      -((∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ p a * V a l)) +
        (∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ l a * V p a))) := by
        rw [hfirst, hsecond]
    _ =
      -∑ p : ι, ∑ l : ι,
        G p l *
          ((∑ a : ι, Γ p a * V a l) +
           (∑ a : ι, Γ l a * V p a)) := by
        simp [Finset.sum_add_distrib, mul_add]

/-- Contracting `nabla gInv = 0` with the metric variation gives the inverse
metric cancellation needed by the trace derivative. -/
theorem gInvTraceCancel
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricDot : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d : Idx)
    (hzero : ∀ p l : Idx,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I) gInv cov frame hframe x d p l = 0) :
    (∑ p : Idx, ∑ l : Idx,
      extDerivFun (I := I) (fun y : M => gInv y p l) x (frame d x) *
        metricDot x p l) =
      -∑ p : Idx, ∑ l : Idx,
        gInv x p l *
          ((∑ a : Idx,
            Coordinates.christoffelSymbolInFrame cov frame hframe x d p a *
              metricDot x a l) +
           (∑ a : Idx,
            Coordinates.christoffelSymbolInFrame cov frame hframe x d l a *
              metricDot x p a)) := by
  classical
  let DU : Idx -> Idx -> Real := fun p l =>
    extDerivFun (I := I) (fun y : M => gInv y p l) x (frame d x)
  let G : Idx -> Idx -> Real := fun p l => gInv x p l
  let V : Idx -> Idx -> Real := fun p l => metricDot x p l
  let Γ : Idx -> Idx -> Real := fun a c =>
    Coordinates.christoffelSymbolInFrame cov frame hframe x d a c
  have hDU : ∀ p l : Idx,
      DU p l =
        -((∑ a : Idx, Γ a p * G a l) +
          (∑ a : Idx, Γ a l * G p a)) := by
    intro p l
    have hz := hzero p l
    unfold RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame at hz
    change DU p l +
        (∑ a : Idx, Γ a p * G a l) +
        (∑ a : Idx, Γ a l * G p a) = 0 at hz
    linarith
  simpa [DU, G, V, Γ] using traceCancelAlg G V DU Γ hDU

/-- The covariant trace of the metric variation equals the directional
derivative of the scalar metric trace. -/
theorem traceCovEqDeriv
    (gInv : Curvature.InverseMetricComponents M Idx)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (metricTrace : M -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (d : Idx)
    (hmetricCov : ∀ p l : Idx,
      metricCovDerivDt x d p l =
        dotCovAt (I := I) cov frame hframe metricDot x d p l)
    (htrace :
      metricTrace =ᶠ[nhds x]
        fun y : M => ∑ p : Idx, ∑ l : Idx,
          gInv y p l * metricDot y p l)
    (hgInv_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y p l) x)
    (hmetricDot_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => metricDot y p l) x)
    (hzero : ∀ p l : Idx,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I) gInv cov frame hframe x d p l = 0) :
    metricTraceCovAt gInv metricCovDerivDt x d =
      extDerivFun (I := I) metricTrace x (frame d x) := by
  classical
  have htraceDeriv := traceDerivAt
    (I := I) gInv metricDot metricTrace frame d htrace
    hgInv_mdiff hmetricDot_mdiff
  have hcancel := gInvTraceCancel
    (I := I) gInv metricDot cov frame hframe x d hzero
  calc
    metricTraceCovAt gInv metricCovDerivDt x d =
        ∑ p : Idx, ∑ l : Idx,
          gInv x p l *
            dotCovAt (I := I) cov frame hframe metricDot x d p l := by
          unfold metricTraceCovAt
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hmetricCov p l]
    _ =
        (∑ p : Idx, ∑ l : Idx,
          gInv x p l *
            extDerivFun (I := I) (fun y : M => metricDot y p l)
              x (frame d x)) +
        (∑ p : Idx, ∑ l : Idx,
          extDerivFun (I := I) (fun y : M => gInv y p l)
              x (frame d x) *
            metricDot x p l) := by
          rw [hcancel]
          unfold dotCovAt
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, mul_add, mul_sub]
          ring
    _ =
        ∑ p : Idx, ∑ l : Idx,
          (gInv x p l *
            extDerivFun (I := I) (fun y : M => metricDot y p l)
              x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y p l)
              x (frame d x) *
            metricDot x p l) := by
          simp [Finset.sum_add_distrib]
    _ = extDerivFun (I := I) metricTrace x (frame d x) := htraceDeriv.symm

/-- Spatial derivative of the traced Christoffel variation from its local
identification with half the scalar trace derivative. -/
theorem gammaTraceDeriv
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_eventual :
      (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
        gammaDot y p p j) =ᶠ[nhds x0]
          fun y : M =>
            (1 / 2 : Real) *
              scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    extDerivFun (I := I)
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j)
        x0 (coordinateFrameAt (I := I) x0 i x0) =
      (1 / 2 : Real) *
        scalarCoordSecondAt (I := I) metricTrace x0 i j := by
  have hcongr := extDerivFun_congr_eventually_real
    (I := I) (x := x0)
    (coordinateFrameAt (I := I) x0 i x0) htrace_eventual
  rw [hcongr]
  have hconst := extDerivFun_const_mul
    (I := I) (c := (1 / 2 : Real))
    (f := scalarCoordDerivFun (I := I) metricTrace x0 j)
    (x := x0) hscalar_mdiff
  change extDerivFun (I := I)
      (fun y : M =>
        (1 / 2 : Real) *
          scalarCoordDerivFun (I := I) metricTrace x0 j y)
      x0 (coordinateFrameAt (I := I) x0 i x0) = _
  rw [hconst]
  rfl

/-- Coordinate Hessian expression
`Hess_ij f = partial_i partial_j f - Gamma^p_ij partial_p f`. -/
def scalarHessCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (f : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  scalarCoordSecondAt (I := I) f x0 i j -
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x0 i j p *
        scalarCoordDerivAt (I := I) f x0 p

/-- Covariant trace variation bridge.  Once the traced Christoffel variation
one-form has derivative `1/2 * partial_i partial_j V` and pointwise value
`1/2 * partial_a V`, the full covariant derivative is
`1/2 * Hess_ij V`.  The middle connection-correction terms cancel by finite
trace algebra. -/
theorem gammaTraceCovVar
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_deriv :
      extDerivFun (I := I)
          (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
            gammaDot y p p j)
          x0 (coordinateFrameAt (I := I) x0 i x0) =
        (1 / 2 : Real) * scalarCoordSecondAt (I := I) metricTrace x0 i j)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (htrace_ext :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I) (fun y : M => gammaDot y p p j) x0
            (coordinateFrameAt (I := I) x0 i x0)) =
        extDerivFun (I := I)
          (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
            gammaDot y p p j)
          x0 (coordinateFrameAt (I := I) x0 i x0)) :
    gammaTraceCovAt (I := I) cov gammaDot x0 i j =
      (1 / 2 : Real) *
        scalarHessCoordAt (I := I) cov metricTrace x0 i j := by
  classical
  let Idx := CoordinateIdx (𝕜 := Real) E
  let Gamma : Idx -> Idx -> Idx -> Real :=
    fun a b c => Realized.christoffelCoordAt (I := I) cov x0 a b c
  let A : Idx -> Idx -> Idx -> Real := fun k a b => gammaDot x0 k a b
  let D : Real :=
    ∑ p : Idx,
      extDerivFun (I := I) (fun y : M => gammaDot y p p j) x0
        (coordinateFrameAt (I := I) x0 i x0)
  let U : Real := ∑ p : Idx, ∑ a : Idx, Gamma i a p * A a p j
  let L : Real := ∑ p : Idx, ∑ a : Idx, Gamma i p a * A p a j
  let T : Idx -> Real := fun a => ∑ p : Idx, A p p a
  have hUL : U = L := by
    calc
      U = ∑ a : Idx, ∑ p : Idx, Gamma i a p * A a p j := by
        unfold U
        rw [Finset.sum_comm]
      _ = L := by
        rfl
  have hlast :
      (∑ p : Idx, ∑ a : Idx, Gamma i j a * A p p a) =
        ∑ a : Idx, Gamma i j a * T a := by
    unfold T
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  calc
    gammaTraceCovAt (I := I) cov gammaDot x0 i j
        = D + U - L - ∑ p : Idx, ∑ a : Idx, Gamma i j a * A p p a := by
          unfold gammaTraceCovAt gammaCovCoordAt D U L A Gamma Idx
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_add_distrib]
    _ = D - ∑ a : Idx, Gamma i j a * T a := by
          rw [hUL, hlast]
          ring
    _ = (1 / 2 : Real) * scalarCoordSecondAt (I := I) metricTrace x0 i j -
          ∑ a : Idx, Gamma i j a *
            ((1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a) := by
          rw [show D = (1 / 2 : Real) *
              scalarCoordSecondAt (I := I) metricTrace x0 i j by
            unfold D
            rw [htrace_ext, htrace_deriv]]
          refine congrArg (fun z : Real =>
            (1 / 2 : Real) * scalarCoordSecondAt (I := I) metricTrace x0 i j - z) ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          unfold T A Idx
          rw [htrace_point a]
    _ = (1 / 2 : Real) *
          scalarHessCoordAt (I := I) cov metricTrace x0 i j := by
          have hsum_half :
              (∑ a : Idx, Gamma i j a *
                ((1 / 2 : Real) *
                  scalarCoordDerivAt (I := I) metricTrace x0 a)) =
                (1 / 2 : Real) *
                  ∑ a : Idx, Gamma i j a *
                    scalarCoordDerivAt (I := I) metricTrace x0 a := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
          unfold scalarHessCoordAt Gamma Idx
          rw [hsum_half]
          ring

/-- Time derivative package for scalar first coordinate derivatives. -/
def scalarFirstVarCoordAt
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M) : Prop :=
  ∀ p : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real => scalarCoordDerivAt (I := I) (f s) x0 p)
      (scalarCoordDerivAt (I := I) h x0 p)
      timeSet
      base

/-- Time derivative package for scalar second coordinate derivatives. -/
def scalarSecondVarCoordAt
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M) : Prop :=
  ∀ i j : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real => scalarCoordSecondAt (I := I) (f s) x0 i j)
      (scalarCoordSecondAt (I := I) h x0 i j)
      timeSet
      base

/-- Chart-level first spatial derivative regularity of the potential path gives
the scalar first-coordinate derivative package. -/
theorem scalarFirst_chart
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (hchart :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt
          (fun s : Real => scalarCoordDerivAt (I := I) (f s) x0 p)
          (scalarCoordDerivAt (I := I) h x0 p)
          timeSet
          base) :
    scalarFirstVarCoordAt (I := I) f h timeSet base x0 := by
  intro p
  exact hchart p

/-- Chart-level second spatial derivative regularity of the potential path
gives the scalar second-coordinate derivative package. -/
theorem scalarSecond_chart
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (hchart :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt
          (fun s : Real => scalarCoordSecondAt (I := I) (f s) x0 i j)
          (scalarCoordSecondAt (I := I) h x0 i j)
          timeSet
          base) :
    scalarSecondVarCoordAt (I := I) f h timeSet base x0 := by
  intro i j
  exact hchart i j

/-- Coordinate-frame Hessian variation from Christoffel variation:
`d Hess_ij(f_s) / ds = Hess_ij(h) - A^p_ij partial_p f`. -/
theorem lcHessVarCoord
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (scalarHessCoordAt (I := I) (G.connection base) h x0 i j -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot x0 p i j * scalarCoordDerivAt (I := I) (f base) x0 p)
      timeSet
      base := by
  classical
  have hprod :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (G.connection s) x0 i j p *
              scalarCoordDerivAt (I := I) (f s) x0 p)
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          (gammaDot x0 p i j * scalarCoordDerivAt (I := I) (f base) x0 p +
            Realized.christoffelCoordAt (I := I) (G.connection base) x0 i j p *
              scalarCoordDerivAt (I := I) h x0 p))
        timeSet
        base := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun p _ => (hgamma i j p).mul (hfirst p)))
  have hraw :
      HasDerivWithinAt
        (fun s : Real =>
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
        (scalarCoordSecondAt (I := I) h x0 i j -
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            (gammaDot x0 p i j * scalarCoordDerivAt (I := I) (f base) x0 p +
              Realized.christoffelCoordAt (I := I) (G.connection base) x0 i j p *
                scalarCoordDerivAt (I := I) h x0 p))
        timeSet
        base := by
    simpa [scalarHessCoordAt] using (hsecond i j).sub hprod
  refine hraw.congr_deriv ?_
  simp [scalarHessCoordAt, Finset.sum_add_distrib, sub_eq_add_neg, add_comm,
    add_left_comm]

/-- The weighted-divergence component
`nabla_p A^p_ij - A^p_ij partial_p f`, i.e. the coordinate expression for
`e^f nabla_p(e^{-f} A^p_ij)`. -/
def gammaWeightedDivCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (f : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  (∑ p : CoordinateIdx (𝕜 := Real) E,
    gammaCovCoordAt (I := I) cov gammaDot x0 p p i j) -
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      gammaDot x0 p i j * scalarCoordDerivAt (I := I) f x0 p

/-- Coordinate RHS for the variation of `Ric_ij + Hess_ij f` before replacing
`nabla_i A^p_pj` by the Hessian of the metric trace. -/
def ricciHessVarCoordRHS
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (f h : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  gammaWeightedDivCoordAt (I := I) cov gammaDot f x0 i j +
    scalarHessCoordAt (I := I) cov h x0 i j -
      gammaTraceCovAt (I := I) cov gammaDot x0 i j

/-- Coordinate-frame variation of `Ric_ij + Hess_ij f` in the pre-trace form:
`nabla_p A^p_ij - A^p_ij partial_p f + Hess_ij h - nabla_i A^p_pj`. -/
theorem lcRicciHessVarCoord
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (ricciHessVarCoordRHS (I := I) (G.connection base) gammaDot
        (f base) h x0 i j)
      timeSet
      base := by
  classical
  have hric := lcRicciVarCoord (I := I) G hLC timeSet base x0 gammaDot
    hgamma hmix i j
  have hhess := lcHessVarCoord (I := I) G timeSet base x0 f h gammaDot
    hgamma hfirst hsecond i j
  have hsum := hric.add hhess
  refine hsum.congr_deriv ?_
  simp [ricciHessVarCoordRHS, ricciVarCoordRHS, gammaWeightedDivCoordAt,
    gammaTraceCovAt, scalarHessCoordAt, sub_eq_add_neg]
  ring

/-- Shifted scalar Hessian term `Hess_ij(h - V/2)`, represented as
`Hess_ij h - (1/2) Hess_ij V` to avoid needing linearity of the coordinate
Hessian in this local producer. -/
def shiftedScalarHessCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (h metricTrace : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  scalarHessCoordAt (I := I) cov h x0 i j -
    (1 / 2 : Real) * scalarHessCoordAt (I := I) cov metricTrace x0 i j

/-- Coordinate-frame variation of `Ric_ij + Hess_ij f` after identifying
`nabla_i A^p_pj` with half the Hessian of the metric trace. -/
theorem lcRicciHessVarShifted
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace :
      gammaTraceCovAt (I := I) (G.connection base) gammaDot x0 i j =
        (1 / 2 : Real) *
          scalarHessCoordAt (I := I) (G.connection base) metricTrace x0 i j) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
          (f base) x0 i j +
        shiftedScalarHessCoordAt (I := I) (G.connection base) h metricTrace
          x0 i j)
      timeSet
      base := by
  have hpre := lcRicciHessVarCoord (I := I) G hLC timeSet base x0 f h gammaDot
    hgamma hmix hfirst hsecond i j
  refine hpre.congr_deriv ?_
  unfold ricciHessVarCoordRHS shiftedScalarHessCoordAt
  rw [htrace]
  ring_nf

/-- Trace contraction of the shifted `Ric + Hess f` variation formula.  This is
the scalar producer for the variation of `g^{ij}(Ric_ij + Hess_ij f)` before
identifying the inverse-metric variation term with `-v_ij(Ric_ij+Hess_ij f)`. -/
theorem lcTraceVar
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvPath :
      Real -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        Real)
    (gInvDot :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (hgInv :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (htrace :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        gammaTraceCovAt (I := I) (G.connection base) gammaDot x0 i j =
          (1 / 2 : Real) *
            scalarHessCoordAt (I := I) (G.connection base) metricTrace x0 i j) :
    HasDerivWithinAt
      (fun s : Real =>
        trace2 (gInvPath s)
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
              scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j))
      ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun i =>
        (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun j =>
          gInvDot i j *
            (Realized.christoffelRicciCoeffAt (I := I) (G.connection base)
                x0 i j +
              scalarHessCoordAt (I := I) (G.connection base) (f base)
                x0 i j) +
          gInvPath base i j *
            (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
                (f base) x0 i j +
              shiftedScalarHessCoordAt (I := I) (G.connection base) h
                metricTrace x0 i j))
      timeSet base := by
  apply trace2_deriv
  · exact hgInv
  · intro i j
    exact lcRicciHessVarShifted (I := I) G hLC timeSet base x0 f h
      metricTrace gammaDot hgamma hmix hfirst hsecond i j (htrace i j)

/-- Coordinate-frame variation of `Ric_ij + Hess_ij f` with the trace
covariant-derivative input produced from the traced Christoffel one-form. -/
theorem lcRicciHessShifted_of_trace
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_eventual :
      (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
        gammaDot y p p j) =ᶠ[nhds x0]
          fun y : M =>
            (1 / 2 : Real) *
              scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (hgamma_mdiff :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
          (f base) x0 i j +
        shiftedScalarHessCoordAt (I := I) (G.connection base) h metricTrace
          x0 i j)
      timeSet
      base := by
  have htrace_deriv := gammaTraceDeriv
    (I := I) gammaDot metricTrace x0 i j htrace_eventual hscalar_mdiff
  have htrace_ext := traceExtSum
    (I := I) gammaDot x0 i j hgamma_mdiff
  have htrace_cov := gammaTraceCovVar
    (I := I) (G.connection base) gammaDot metricTrace x0 i j
    htrace_deriv htrace_point htrace_ext
  exact lcRicciHessVarShifted (I := I) G hLC timeSet base x0 f h
    metricTrace gammaDot hgamma hmix hfirst hsecond i j htrace_cov

/-- Trace contraction of `lcRicciHessShifted_of_trace`.  This removes the
pointwise `nabla_i A^p_pj` input from the scalar trace variation producer. -/
theorem lcTraceVar_of_trace
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvPath :
      Real -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        Real)
    (gInvDot :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (hgInv :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (htrace_eventual :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j) =ᶠ[nhds x0]
            fun y : M =>
              (1 / 2 : Real) *
                scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (hgamma_mdiff :
      ∀ j p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        trace2 (gInvPath s)
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
              scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j))
      ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun i =>
        (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun j =>
          gInvDot i j *
            (Realized.christoffelRicciCoeffAt (I := I) (G.connection base)
                x0 i j +
              scalarHessCoordAt (I := I) (G.connection base) (f base)
                x0 i j) +
          gInvPath base i j *
            (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
                (f base) x0 i j +
              shiftedScalarHessCoordAt (I := I) (G.connection base) h
                metricTrace x0 i j))
      timeSet base := by
  apply trace2_deriv
  · exact hgInv
  · intro i j
    exact lcRicciHessShifted_of_trace
      (I := I) G hLC timeSet base x0 f h metricTrace gammaDot
      hgamma hmix hfirst hsecond i j (htrace_eventual j) htrace_point
      (hgamma_mdiff j) (hscalar_mdiff j)

/-- Trace contraction of `Ric + Hess f` with the inverse-metric variation
normalized as the contravariant metric-variation contraction.  This is the
formula 5.10 scalar trace producer: the first term in the product rule is
rewritten as `-v^{ij}(Ric_ij + Hess_ij f)`. -/
theorem lcTraceVar_inv
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvPath :
      Real -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        Real)
    (gInvDot metricVariation :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (hgInv :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (hcontra :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        gInvDot i j = -metricVariation i j)
    (htrace_eventual :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j) =ᶠ[nhds x0]
            fun y : M =>
              (1 / 2 : Real) *
                scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (hgamma_mdiff :
      ∀ j p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        trace2 (gInvPath s)
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
              scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j))
      (-trace2 metricVariation
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            Realized.christoffelRicciCoeffAt (I := I) (G.connection base)
                x0 i j +
              scalarHessCoordAt (I := I) (G.connection base) (f base)
                x0 i j) +
        ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun i =>
          (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun j =>
            gInvPath base i j *
              (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
                  (f base) x0 i j +
                shiftedScalarHessCoordAt (I := I) (G.connection base) h
                  metricTrace x0 i j)))
      timeSet base := by
  have htrace :=
    lcTraceVar_of_trace (I := I) G hLC timeSet base x0 f h metricTrace
      gammaDot gInvPath gInvDot hgamma hmix hfirst hsecond hgInv
      htrace_eventual htrace_point hgamma_mdiff hscalar_mdiff
  refine htrace.congr_deriv ?_
  exact trace2_neg gInvDot metricVariation
    (fun i j : CoordinateIdx (𝕜 := Real) E =>
      Realized.christoffelRicciCoeffAt (I := I) (G.connection base)
          x0 i j +
        scalarHessCoordAt (I := I) (G.connection base) (f base)
          x0 i j)
    (fun i j : CoordinateIdx (𝕜 := Real) E =>
      gInvPath base i j *
        (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
            (f base) x0 i j +
          shiftedScalarHessCoordAt (I := I) (G.connection base) h
            metricTrace x0 i j))
    hcontra

/-- Coordinate-frame shifted Ricci-plus-Hessian variation with the Christoffel
trace inputs produced from the metric-trace and inverse-metric compatibility
bridges. -/
theorem lcTraceShifted
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : Curvature.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (metricDot : M -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real)
    (metricCovDerivDt gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv (coordinateFrameAt (I := I) x0))
    (hmetricVar :
      metricVarOn (I := I) G (coordinateFrameAt (I := I) x0) base
        (coordinateFrameSet (I := I) x0) metricDot)
    (hmetric :
      metricCovVarOn (I := I) G (coordinateFrameAt (I := I) x0) base
        (coordinateFrameSet (I := I) x0) metricCovDerivDt)
    (hExt :
      metricExtDtOn (I := I) G (coordinateFrameAt (I := I) x0) base
        (coordinateFrameSet (I := I) x0) metricDot)
    (hgammaLocal :
      gammaDerivOn (I := I) G (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) base
        (coordinateFrameSet (I := I) x0) gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_on :
      ∀ y : M, y ∈ coordinateFrameSet (I := I) x0 ->
        metricTrace y =
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            ∑ l : CoordinateIdx (𝕜 := Real) E,
              gInv y p l * metricDot y p l)
    (hgInv_mdiff :
      ∀ y : M, y ∈ coordinateFrameSet (I := I) x0 ->
        ∀ p l : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real) (fun z : M => gInv z p l) y)
    (hmetricDot_mdiff :
      ∀ y : M, y ∈ coordinateFrameSet (I := I) x0 ->
        ∀ p l : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun z : M => metricDot z p l) y)
    (hgamma_mdiff :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
          (f base) x0 i j +
        shiftedScalarHessCoordAt (I := I) (G.connection base) h metricTrace
          x0 i j)
      timeSet
      base := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let u0 := coordinateFrameSet (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hu : IsOpen u0 := coordinateFrameSet_open (I := I) x0
  have hx0 : x0 ∈ u0 := coordinateFrameAt_mem (I := I) x0
  have hcoordGamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot := by
    intro a b c
    have h := hgammaLocal x0 hx0 a b c
    simpa [gammaCoordDerivAt, Realized.christoffelCoordAt, frame, hframe] using
      h.hasDerivWithinAt
  have hcov :
      ∀ y : M, y ∈ u0 -> ∀ d a b : CoordinateIdx (𝕜 := Real) E,
        metricCovDerivDt y d a b =
          dotCovAt (I := I) (G.connection base) frame hframe metricDot
            y d a b :=
    covDtEqDotCov (I := I) G frame hframe base metricDot metricCovDerivDt
      hmetricVar hmetric hExt
  have hinvCoord :
      RicciFlower.Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) (G.metric base) gInv frame := by
    intro y a b
    constructor
    · simpa [RicciFlower.Coordinates.metricCompForMetricInFrame, frame] using
        (hinv y a b).1
    · simpa [RicciFlower.Coordinates.metricCompForMetricInFrame, frame] using
        (hinv y a b).2
  have hmetric_mdiff :
      ∀ y : M, y ∈ u0 -> ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun z : M =>
            RicciFlower.Coordinates.metricCompForMetricInFrame
              (I := I) (G.metric base) frame z a b) y := by
    intro y hy a b
    exact RicciFlower.Coordinates.metricComp_mdiffAt
      (I := I) (G.metric base) frame hframe hu hy a b
  have hzero :
      ∀ y : M, y ∈ u0 -> ∀ d p l : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
          (I := I) gInv (G.connection base) frame hframe y d p l = 0 := by
    intro y hy d p l
    exact RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame_eq_zero
      (I := I) (g := G.metric base) (gInv := gInv)
      (cov := G.connection base) (frame := frame) (hframe := hframe)
      hinvCoord (hLC base).1 hu hy (hgInv_mdiff y hy)
      (hmetric_mdiff y hy) d p l
  have htrace_nhds :
      ∀ y : M, y ∈ u0 ->
        metricTrace =ᶠ[nhds y]
          fun z : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
            ∑ l : CoordinateIdx (𝕜 := Real) E,
              gInv z p l * metricDot z p l := by
    intro y hy
    filter_upwards [hu.mem_nhds hy] with z hz using htrace_on z hz
  have htraceCov :
      ∀ y : M, y ∈ u0 -> ∀ d : CoordinateIdx (𝕜 := Real) E,
        metricTraceCovAt gInv metricCovDerivDt y d =
          extDerivFun (I := I) metricTrace y (frame d y) := by
    intro y hy d
    exact traceCovEqDeriv (I := I) gInv metricDot metricCovDerivDt
      metricTrace (G.connection base) frame hframe d (hcov y hy d)
      (htrace_nhds y hy) (hgInv_mdiff y hy) (hmetricDot_mdiff y hy)
      (hzero y hy d)
  have htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a := by
    intro a
    have hgammaTrace :=
      gammaTraceVar_of_lcGammaVar (I := I) G hLC gInv frame hframe hu base
        metricDot metricCovDerivDt gammaDot hinv hmetricVar hmetric
        hgammaLocal x0 hx0 a
    have hmetricTrace :
        metricTraceCovAt gInv metricCovDerivDt x0 a =
          scalarCoordDerivAt (I := I) metricTrace x0 a := by
      simpa [scalarCoordDerivAt, frame] using htraceCov x0 hx0 a
    exact gammaTracePoint (I := I) gInv metricCovDerivDt gammaDot
      metricTrace x0 a hgammaTrace hmetricTrace
  have htrace_eventual :
      (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
        gammaDot y p p j) =ᶠ[nhds x0]
          fun y : M =>
            (1 / 2 : Real) *
              scalarCoordDerivFun (I := I) metricTrace x0 j y := by
    filter_upwards [hu.mem_nhds hx0] with y hy
    have hgammaTrace :=
      gammaTraceVar_of_lcGammaVar (I := I) G hLC gInv frame hframe hu base
        metricDot metricCovDerivDt gammaDot hinv hmetricVar hmetric
        hgammaLocal y hy j
    have hmetricTrace :
        metricTraceCovAt gInv metricCovDerivDt y j =
          scalarCoordDerivFun (I := I) metricTrace x0 j y := by
      simpa [scalarCoordDerivFun, frame] using htraceCov y hy j
    rw [hgammaTrace, hmetricTrace]
  exact lcRicciHessShifted_of_trace
    (I := I) G hLC timeSet base x0 f h metricTrace gammaDot
    hcoordGamma hmix hfirst hsecond i j htrace_eventual htrace_point
    hgamma_mdiff hscalar_mdiff

end RicciCoordVariation

end LeviCivita
end RicciFlower
