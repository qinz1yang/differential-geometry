import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Producers
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BlackBox

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Time side: the metric frame-component mixed-derivative swap from a solution

The foundational time-side bridge: the fixed-base time-derivative swap for the
metric frame component `g_s(e_a, e_b)`, with the pointwise time derivative
discharged from the solution's metric variation equation `∂ₛg = −2Ric`
(`IsSolutionOn.equation`).

The manifold mixed-derivative swap core is `fixedBaseOnReg_of_timeDerivWithin`
(`Bundle/PartialMfderiv/FixedBase.lean`).  The **only** genuinely new content here
is wiring the solution's `equation` into its `hTime` slot; the spatial-regularity
inputs (`hSmooth` joint spacetime `C²` from `MetricFamilySmoothOn.frameCompSmooth`,
`hFdiff`/`hFtdiff` fixed-time spatial `MDiff`) are taken as hypotheses — each is
dischargeable from the existing smoothness API (`ricciTensor_apply_smooth`,
`inner_smooth_scalar`, `TensorMultilinear.contMDiffAt_section_apply_gen`) plus the
canonical-Ricci bridge `SolutionOn.ricciAt_eq`, which the metric-cov-derivative
producer supplies. -/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- **Public metric-inner `MDifferentiableAt`** for `∞`-smooth tangent sections — the
public counterpart of the (private) `inner_mdiffAt_scalar`, re-proved here from the
public metric bundle smoothness `g.contMDiff` and `cotangentCov_pairing_contMDiff`.
This is the spatial-`MDiff` input the time-side producer needs (with the `∞`
coordinate frame supplying the smooth sections). -/
theorem metricInner_mdiffAt
    (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Z b)))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real) (fun b : M => g.inner b (Y b) (Z b)) x := by
  have hg : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real) b
        (g.inner b)) := g.contMDiff
  have hgY : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] Real) b (g.inner b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[Real] Real)
      (b := fun b : M => b)
      (ϕ := fun b => g.inner b) (v := fun b => Y b) hg hY
  exact ((DifferentialGeometry.Integral.Connection.cotangentCov_pairing_contMDiff hgY hZ)
    x).mdifferentiableAt (by simp)

/-- **The metric frame-component fixed-base mixed-derivative swap, from a solution.**
With `F s y = g_s(e_a, e_b)(y)` and `Ft t y = −2·Ric_t(e_a, e_b)(y)`, the time
derivative of the spatial derivative of `F` is the spatial derivative of `Ft`.

`hTime` is discharged from the solution's metric variation equation; the
spatial-regularity inputs `hSmooth`/`hFdiff`/`hFtdiff` are the genuine prerequisites
(dischargeable from `MetricFamilySmoothOn` + the canonical-Ricci bridge). -/
theorem metricFrameComp_fixedBaseSwap_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (a b : Idx)
    (hSmooth : ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2))
        (t, x))
    (hFdiff : ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (-2 : Real) * ricciCompInFrame (I := I) S frame t y a b) x) :
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular u
      (fun s y => (S.family.metric s).inner y (frame a y) (frame b y))
      (fun t y => (-2 : Real) * ricciCompInFrame (I := I) S frame t y a b) := by
  refine fixedBaseOnReg_of_timeDerivWithin (I := I)
    (D.regular_subset) (fun {t} ht => D.regular_mem_nhds ht)
    hSmooth hFdiff hFtdiff ?hTime
  -- `hTime`: the metric variation `∂ₛ g_s(e_a, e_b) = −2 Ric_t(e_a, e_b)`.
  intro t ht x
  have heq := hS.equation ⟨t, ht⟩ x (frame a x) (frame b x)
  simpa [ricciCompInFrame] using heq

/-- **The metric covariant-derivative time derivative from a solution** (`∂ₛ(∇ᵗ g_s)`).
Discharges the `MetricCovDerivDerivativeComponentsInFrameOnLocal` regularity that the
banked Christoffel-evolution producer consumes, with
`metricCovDerivDt = −2·ricciCovDerivCompInFrame` (the `−2∇Ric` Ricci-flow form).

The three terms of `metricCovDerivCompInFrameAtBase` are differentiated in `s`: the
`extDerivFun(g_s(e_a,e_b))` term by the mixed-derivative swap
`metricFrameComp_fixedBaseSwap_of_solution`, and the two frozen-vector terms
`g_s(∇ᵗe_a, e_b)`, `g_s(e_a, ∇ᵗe_b)` directly by the metric variation `∂ₛg = −2Ric`.
The spatial-regularity inputs are taken `∀ a b` (dischargeable at the `∞` coordinate
frame). -/
theorem metricCovDerivDeriv_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hSmooth : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2))
        (t, x))
    (hFdiff : ∀ a b : Idx, ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x) :
    MetricCovDerivDerivativeComponentsInFrameOnLocal (I := I) S frame u
      (fun t x d a b => (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame t x d a b) := by
  intro t x hx d a b
  -- Term 1: the mixed-derivative swap on `extDerivFun(g_s(e_a, e_b))` (the swap's
  -- `Ft = −2·Ric` differentiability is `const · Ric`).
  have h1 := (metricFrameComp_fixedBaseSwap_of_solution (I := I) S hS frame a b
    (hSmooth a b) (hFdiff a b)
    (fun t' ht' x' hx' => (mdifferentiableAt_const (c := (-2 : Real))).mul
      (hFtdiff a b t' ht' x' hx'))) (t : Real) t.2 x hx (frame d x)
  -- Terms 2, 3: the metric variation on the frozen-vector inner products.
  have h2 := hS.equation t x
    ((S.family.connection (t : Real) (frame a) x) (frame d x)) (frame b x)
  have h3 := hS.equation t x
    (frame a x) ((S.family.connection (t : Real) (frame b) x) (frame d x))
  have hcomb := (h1.sub h2).sub h3
  -- The differentiated function is `metricCovDerivCompInFrameAtBase` (defeq); match the value.
  have hval :
      extDerivFun (I := I)
            (fun y : M => -2 * ricciCompInFrame (I := I) S frame (t : Real) y a b) x (frame d x) -
          (-2 : Real) * RicciAtFamily.toTensorField (I := I) S.ricciAt (t : Real) x
            ((S.family.connection (t : Real) (frame a) x) (frame d x)) (frame b x) -
          (-2 : Real) * RicciAtFamily.toTensorField (I := I) S.ricciAt (t : Real) x
            (frame a x) ((S.family.connection (t : Real) (frame b) x) (frame d x)) =
        (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame (t : Real) x d a b := by
    rw [extDerivFun_const_mul (I := I) (-2 : Real)
      (hFtdiff a b (t : Real) t.2 x hx)]
    simp only [ricciCovDerivCompInFrame, RicciAtFamily.toTensorField_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  show HasDerivWithinAt
      (fun s : Real => metricCovDerivCompInFrameAtBase (I := I) S frame (t : Real) s x d a b)
      ((-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame (t : Real) x d a b)
      D.carrier (t : Real)
  exact hval ▸ hcomb

/-- **The connection-variation black box discharged from a solution.**  The
`metricCovDerivDerivative` field is `metricCovDerivDeriv_of_solution`; the
`metricCovDerivRicciFlow` field is definitional (`metricCovDerivDt = −2·ricciCovDeriv`,
`nablaRic = ricciCovDeriv`).  Spatial regularity taken as inputs (dischargeable at the
`∞` coordinate frame). -/
def connectionVariationBlackBox_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hSmooth : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, x))
    (hFdiff : ∀ a b : Idx, ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x) :
    ConnectionVariationBlackBoxInFrameOn (I := I) S frame u
      (fun t x d a b => ricciCovDerivCompInFrame (I := I) S frame t x d a b) where
  metricCovDerivDt := fun t x d a b => (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame t x d a b
  metricCovDerivDerivative :=
    metricCovDerivDeriv_of_solution (I := I) S hS frame hSmooth hFdiff hFtdiff
  metricCovDerivRicciFlow := fun _ _ _ _ _ => rfl

/-- **Raised Christoffel evolution `∂ₜΓ` from a solution** (Lemma 6.2), with the
connection-variation black box discharged via `metricCovDerivDeriv_of_solution`.
The remaining input `hmetricFrame` (`MetricFrameTimeRegularityInFrameOnLocal`) is the
standing metric-frame time-regularity black box. -/
theorem christoffelEvolution_of_solution
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    (hmetricFrame : MetricFrameTimeRegularityInFrameOnLocal (I := I) S gInv gInvDt frame u)
    (hSmooth : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, x))
    (hFdiff : ∀ a b : Idx, ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x) :
    ChristoffelEvolutionEquationInFrameOn (I := I) S gInv frame hframe
      (fun t x d a b => ricciCovDerivCompInFrame (I := I) S frame t x d a b) :=
  christoffelEvolution_of_blackBox (I := I) S hS gInv gInvDt frame hframe hu
    (fun t x d a b => ricciCovDerivCompInFrame (I := I) S frame t x d a b)
    hmetricFrame
    (connectionVariationBlackBox_of_solution (I := I) S hS frame hSmooth hFdiff hFtdiff)

end DifferentialGeometry.PDE.RicciFlow
