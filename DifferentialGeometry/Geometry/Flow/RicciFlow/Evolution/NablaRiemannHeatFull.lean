import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SBochnerProduct

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

/-!
# The intrinsic `k = 1` heat equation for `|∇Rm|²` from the two general Bochner lemmas

This file assembles the **intrinsic** `k = 1` Bernstein–Bando–Shi heat equation
for `|∇Rm|²` by instantiating, at `T = ∇Rm` (`nablaRm04Field`), the two
*rank-uniform, frame-free* Bochner lemmas that retired the standing
norm-square hypotheses of the architecture:

* the **time-derivative half**
  `Tensor0SBundle.hasDerivWithinAt_normSq0S_ricciFlow`
  (`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`):
  under `∂ₜg = −2 Ric`,
  `∂ₜ‖T‖² = (Ric ∗ T²) + 2⟨∂ₜT, T⟩` at any rank, derived from the component
  time derivative `∂ₜT` — **no** assembled-heat hypothesis;
* the **Laplacian half** `Tensor0SBundle.tensorNormBochnerSplit_mc`
  (`Tensor/RSTensor/FiberMetric/Tensor0SBochnerProduct.lean`):
  `Δ‖T‖² = 2⟨ΔT, T⟩ + 2‖∇T‖²` at any rank, hypothesis-free (derived from metric
  compatibility, taking only the standard realization inputs — the same frontier
  as the `(0,2)` `ricci_lap_mc`).

## What it produces

Writing `u = |∇Rm|²`, `Δ|∇Rm|²` for the Hessian trace, `nabla2 = |∇²Rm|²`, and
the **rough Laplacian** `Δ∇Rm = metricTrace0S2TensorInBasis basis gInv (∇²Rm)`:

* **subtracting** the two splits gives the heat-equation identity
  `∂ₜ|∇Rm|² = Δ|∇Rm|² − 2|∇²Rm|² + reaction`,
  with the reaction the **derived**
  `reaction = (Ric ∗ ∇Rm²) + 2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`
  (`nablaRm04ReactionIntrinsic`): the standard BBS reaction, *no* renamed
  hypothesis;
* `nablaRm04NormHeatEquationOn_intrinsic` packages this as the producer predicate
  `NablaRm04NormHeatEquationOn` (`Evolution/NablaRiemannHeat.lean`) in the
  intrinsic fibre norms;
* `nablaRm04NormHeatBoundOn_intrinsic` feeds it, together with a frame-independent
  reaction bound (same status as the `(0,2)` reaction in
  `RicciNorm.lean`'s `ricci_heat_mc`) and `|∇²Rm|² ≥ 0`, to the `horth`-free
  scalar producer `nablaRm04NormHeatBoundOn_scalar`
  (`Evolution/NablaRiemannHeatSolution.lean`), yielding the
  `NablaRm04NormHeatBoundOn` predicate consumed by
  `bernstein_first_derivative_estimate`.

## Honest input status

The realization inputs (`nablaRm04Field`/`nabla2Rm04Field` covariant-derivative
realizations — banked, `RmRealizationBridge.lean`; `DuFieldRealizes`/
`HessianRealizesNablaDuAt` of `|∇Rm|²`; smooth basis fields; the genuine inverse
metric; the metric-compatible connection; the Ricci-flow inverse-metric
derivative relation `inverseMetric_derivative_solve`; and the component time
derivative `∂ₜ∇Rm`) and the reaction bound are taken as hypotheses **at exactly
the same status as the `(0,2)` producer** `ricci_heat_mc`
(`Geometry/Flow/RicciFlow/Basic/RicciNorm.lean`), which likewise takes its
`DuFieldRealizes`, `HessianRealizesNablaDuAt`, `SmoothBasisFieldsAt`, the
per-component time-derivative (`h_ricci`/`h_inv`) facts, and the reaction term as
hypotheses.  The advance over the previous `k = 1` status is that the assembled
heat **equation** `NablaRm04NormHeatEquationOn` — formerly always a raw input
(`Evolution/NablaRiemannHeat.lean`) — is now *derived* from the two general
Bochner lemmas plus the component time derivative; the moving-metric `∂ₜg`
reaction term is supplied intrinsically by `hasDerivWithinAt_normSq0S_ricciFlow`,
not assumed.

`#print axioms` for every public theorem is `[propext, Classical.choice,
Quot.sound]`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

-- File-local instances to resolve the variable-rank `Tensor0SModel` normed
-- structure diamond (KNOWN PITFALL), mirroring `Tensor0SBochnerProduct.lean`.
private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance

/-! ## The intrinsic scalar fields of the `k = 1` heat equation

All four scalar fields are intrinsic (frame-free) functions of `(t, x)`. -/

section Fields

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The intrinsic squared norm `|∇Rm|²` of the bundled `∇Rm` (`nablaRm04Field`). -/
def nablaRm04NormSqIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.base.metric t) x 5 (nablaRm04Field (I := I) S t x)

/-- The intrinsic squared norm `|∇²Rm|²` of the bundled `∇²Rm`
(`nabla2Rm04Field`). -/
def nabla2Rm04NormSqIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.base.metric t) x 6 (nabla2Rm04Field (I := I) S t x)

/-- The **derived `k = 1` reaction** `(Ric ∗ ∇Rm²) + 2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`.

`ric` is the (frame-component) Ricci array; `Tdot t x` is the abstract fibre value
of `∂ₜ∇Rm`; the second term is the contraction of the heat residual
`(∂ₜ − Δ)∇Rm = ∂ₜ∇Rm − roughLap(∇²Rm)` against `∇Rm`.  The metric reaction is the
`ricReactionContract` produced from the moving-metric `∂ₜg` term of
`hasDerivWithinAt_normSq0S_ricciFlow`.  Frame-free apart from the abstract `ric`
contraction (which, contracted, is the intrinsic `Ric ∗ ∇Rm²`). -/
def nablaRm04ReactionIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 x) : Real -> M -> Real :=
  fun t x =>
    ricReactionContract (gInv t x) (ric t x)
        (fun I0 : Fin 5 -> Idx =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S t x)
            (fun i => basis x i) I0)
        (fun J0 : Fin 5 -> Idx =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S t x)
            (fun i => basis x i) J0) +
      2 * inner0S (I := I) (S.base.metric t) x 5
            (Tdot t x -
              metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                (nabla3Rm04Field (I := I) S t x))
            (nablaRm04Field (I := I) S t x)

end Fields

/-! ## The intrinsic heat equation

The core assembly: the two Bochner lemmas, instantiated at `∇Rm`, combine into the
`NablaRm04NormHeatEquationOn` predicate. -/

section HeatEquation

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **The intrinsic `k = 1` heat equation for `|∇Rm|²`.**

Instantiating the time-derivative Bochner lemma `hasDerivWithinAt_normSq0S_ricciFlow`
(giving `∂ₜ|∇Rm|² = ricReaction + 2⟨∂ₜ∇Rm, ∇Rm⟩`) and the Laplacian Bochner split
`tensorNormBochnerSplit_mc` (giving `Δ|∇Rm|² = 2⟨Δ∇Rm, ∇Rm⟩ + 2|∇²Rm|²`) at
`T = ∇Rm`, and *subtracting*, the heat equation
`∂ₜu = uLap + (−2·nabla2 + reaction)` holds with

* `u = nablaRm04NormSqIntrinsic` (`= |∇Rm|²`);
* `uLap = metricTrace0S2InBasis (basis x) (gInv t x) (normSecond t x) Fin.elim0`
  (`= Δ|∇Rm|²`, the realized Hessian trace, as in the `(0,2)` `hlapTrace`);
* `nabla2 = nabla2Rm04NormSqIntrinsic` (`= |∇²Rm|²`);
* `reaction = nablaRm04ReactionIntrinsic` (`= (Ric ∗ ∇Rm²) + 2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`).

The hypotheses are the realization inputs of the two Bochner lemmas — at exactly
the status the `(0,2)` `ricci_heat_mc` takes them — plus the Ricci-flow
inverse-metric-derivative relation `hflow` and the component time derivative
`hT`/`hTdot` of `∇Rm`. -/
theorem nablaRm04NormHeatEquationOn_intrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Xb : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nablaRmNormLap : Real -> M -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 x)
    (hinv : ∀ (t : Real) (x : M),
      MetricInverseInBasis (I := I) (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x : M, SmoothBasisFieldsAt (I := I) (basis x) (Xb x))
    (hdu : ∀ t : Real,
      DuFieldRealizes (I := I)
        (fun y : M => normSq0S (I := I) (S.base.metric t) y 5
          (nablaRm04Field (I := I) S t y)) (du t))
    (hHess : ∀ (t : Real) (x : M),
      HessianRealizesNablaDuAt (I := I) (S.family.connection t) (du t)
        (normSecond t) x)
    (hlapTrace : ∀ (t : Real) (x : M),
      nablaRmNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hT : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (I0 : Fin 5 -> Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S r x)
            (fun i => basis x i) I0)
        (tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
        D.carrier (t : Real))
    (hgInvDt : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (i j : Idx),
      HasDerivWithinAt (fun r : Real => gInv r x i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
        D.carrier (t : Real)) :
    NablaRm04NormHeatEquationOn (D := D)
      (nablaRm04NormSqIntrinsic (I := I) S)
      nablaRmNormLap
      (nabla2Rm04NormSqIntrinsic (I := I) S)
      (nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot) := by
  classical
  intro t x
  -- The metric-compatible Levi-Civita connection of the solution.
  have hmc : IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real)) :=
    solution_isMetricCompatible (I := I) S (t : Real)
  -- The time-derivative Bochner lemma at `T = ∇Rm`, under the Ricci-flow
  -- inverse-metric-derivative relation, gives
  -- `∂ₜ|∇Rm|² = ricReaction + 2⟨∂ₜ∇Rm, ∇Rm⟩`.
  have hdt :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I)
      (s := 5) (x := x) (u := D.carrier) (t := (t : Real))
      (g := fun r : Real => S.base.metric r)
      (gInv := fun r : Real => gInv r x)
      (gInvDt := fun i j => 2 * (∑ p : Idx, ∑ q : Idx,
        gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
      (ric := ric (t : Real) x)
      (T := fun r : Real => nablaRm04Field (I := I) S r x)
      (Tdt := fun I0 =>
        tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
      (Tdot := Tdot (t : Real) x)
      (basis := basis x)
      (fun r => hinv r x)
      (hgInvDt t x)
      (hT t x)
      (fun I0 => rfl)
      (fun i j => rfl)
  -- The Laplacian Bochner split at `T = ∇Rm`:
  -- `Δ|∇Rm|² = 2⟨Δ∇Rm, ∇Rm⟩ + 2|∇²Rm|²`.
  have hsplit :=
    tensorNormBochnerSplit_mc (I := I) (s := 5)
      (cov := S.family.connection (t : Real))
      (g := S.base.metric (t : Real))
      hmc (basis := basis x) (gInv := gInv (t : Real) x) (hinv t x)
      (Xb := Xb x) (hfields x)
      (T := nablaRm04Field (I := I) S (t : Real))
      (nablaT := nabla2Rm04Field (I := I) S (t : Real))
      (nabla2T := nabla3Rm04Field (I := I) S (t : Real))
      (nabla2Rm04Field_realizes (I := I) S (t : Real))
      (nabla3Rm04Field_realizes (I := I) S (t : Real))
      (du := du (t : Real)) (normSecond := normSecond (t : Real))
      (hdu (t : Real)) (hHess (t : Real) x)
  -- Convert the derivative value to the producer's RHS.
  refine hdt.congr_deriv ?_
  -- Unfold the four fields and substitute the Bochner split for `uLap`.
  rw [hlapTrace (t : Real) x]
  -- Abbreviations.
  set Rm := nablaRm04Field (I := I) S (t : Real) x with hRm
  set Rm2 := nabla2Rm04Field (I := I) S (t : Real) x with hRm2
  set roughT := metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
    (nabla3Rm04Field (I := I) S (t : Real) x) with hroughT
  -- `hsplit : metricTrace0S2InBasis … (normSecond t x) = 2⟨roughT, Rm⟩ + 2|∇²Rm|²`.
  rw [hsplit]
  -- Reaction: split the residual inner product `⟨Tdot − roughT, Rm⟩`.
  rw [nablaRm04ReactionIntrinsic, nabla2Rm04NormSqIntrinsic]
  -- `inner0S (Tdot − roughT) Rm = inner0S Tdot Rm − inner0S roughT Rm`.
  have hsub :
      inner0S (I := I) (S.base.metric (t : Real)) x 5 (Tdot (t : Real) x - roughT) Rm =
        inner0S (I := I) (S.base.metric (t : Real)) x 5 (Tdot (t : Real) x) Rm -
          inner0S (I := I) (S.base.metric (t : Real)) x 5 roughT Rm := by
    simp only [inner0S, MetricFiberData.inner, map_sub, LinearMap.sub_apply]
  rw [hsub]
  -- All remaining terms are real scalars; the metric reaction and the `∂ₜ∇Rm`
  -- inner product match definitionally.  `roughT = ΔRm`, so `2⟨roughT,Rm⟩`
  -- cancels against the Bochner split's `2⟨ΔRm,Rm⟩`.
  ring

end HeatEquation

/-! ## The intrinsic `k = 1` heat-inequality producer

Feed the intrinsic heat equation, the intrinsic-norm nonnegativity, and a
frame-independent reaction bound into the `horth`-free scalar producer. -/

section Producer

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The intrinsic `|∇²Rm|²` is nonnegative (the fibre inner product is positive
semidefinite). -/
theorem nabla2Rm04NormSqIntrinsic_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    0 ≤ nabla2Rm04NormSqIntrinsic (I := I) S t x := by
  unfold nabla2Rm04NormSqIntrinsic
  rw [normSq0S_eq_inner]
  exact (tensor0SMetricData (I := I) (S.base.metric t) x 6).inner_nonneg
    (nabla2Rm04Field (I := I) S t x)

/-- **The intrinsic `k = 1` heat-inequality producer** `NablaRm04NormHeatBoundOn`.

From the intrinsic heat equation (`nablaRm04NormHeatEquationOn_intrinsic`) plus a
frame-independent reaction bound

`reaction ≤ cReact · √(|Rm|²) · |∇Rm|²`

(`hreact_bound`, the BBS `Rm ∗ ∇Rm` reaction estimate — same hypothesis status as
the `(0,2)` reaction in `ricci_heat_mc`), the dropped scalar heat inequality

`(∂ₜ − Δ)|∇Rm|² ≤ cReact · |Rm| · |∇Rm|²`

holds — the exact `NablaRm04NormHeatBoundOn` predicate consumed by
`bernstein_first_derivative_estimate` (`Evolution/BernsteinShi.lean`), in the
intrinsic fibre norms `|∇Rm|² = normSq0S g 5 (∇Rm)`, `|Rm|² = normSq0S g 4 (Rm)`.

This is the `k = 1` analogue of the `k = 0` curvature-norm producer, assembled
through the two general Bochner lemmas; no orthonormal frame appears in the
inequality. -/
theorem nablaRm04NormHeatBoundOn_intrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Xb : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nablaRmNormLap : Real -> M -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 x)
    (cReact : Real)
    (hinv : ∀ (t : Real) (x : M),
      MetricInverseInBasis (I := I) (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x : M, SmoothBasisFieldsAt (I := I) (basis x) (Xb x))
    (hdu : ∀ t : Real,
      DuFieldRealizes (I := I)
        (fun y : M => normSq0S (I := I) (S.base.metric t) y 5
          (nablaRm04Field (I := I) S t y)) (du t))
    (hHess : ∀ (t : Real) (x : M),
      HessianRealizesNablaDuAt (I := I) (S.family.connection t) (du t)
        (normSecond t) x)
    (hlapTrace : ∀ (t : Real) (x : M),
      nablaRmNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hT : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (I0 : Fin 5 -> Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S r x)
            (fun i => basis x i) I0)
        (tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
        D.carrier (t : Real))
    (hgInvDt : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (i j : Idx),
      HasDerivWithinAt (fun r : Real => gInv r x i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
        D.carrier (t : Real))
    (hreact_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M),
      nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot (t : Real) x ≤
        cReact *
          Real.sqrt
            (normSq0S (I := I) (S.base.metric (t : Real)) x 4
              (S.base.rm04 (t : Real) x)) *
          nablaRm04NormSqIntrinsic (I := I) S (t : Real) x) :
    NablaRm04NormHeatBoundOn (D := D)
      (nablaRm04NormSqIntrinsic (I := I) S)
      nablaRmNormLap
      (fun t x => normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x))
      cReact := by
  have h_heat :
      NablaRm04NormHeatEquationOn (D := D)
        (nablaRm04NormSqIntrinsic (I := I) S)
        nablaRmNormLap
        (nabla2Rm04NormSqIntrinsic (I := I) S)
        (nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot) :=
    nablaRm04NormHeatEquationOn_intrinsic (I := I) S basis gInv ric Xb du normSecond
      nablaRmNormLap Tdot hinv hfields hdu hHess hlapTrace hT hgInvDt
  exact nablaRm04NormHeatBoundOn_scalar (D := D)
    (nablaRm04NormSqIntrinsic (I := I) S)
    nablaRmNormLap
    (nabla2Rm04NormSqIntrinsic (I := I) S)
    (nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot)
    (fun t x => normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x))
    cReact h_heat
    (fun t x => nabla2Rm04NormSqIntrinsic_nonneg (I := I) S (t : Real) x)
    hreact_bound

end Producer

end DifferentialGeometry.PDE.RicciFlow
