import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFull
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannTimeDeriv
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

/-!
# The rank-uniform (all-`k`) heat equation for `|∇ᵏRm|²` from the two general Bochner lemmas

This file generalizes the **intrinsic `k = 1` heat equation**
`nablaRm04NormHeatEquationOn_intrinsic` (`Evolution/NablaRiemannHeatFull.lean`) to
**every** order `k`, by instantiating, at `T = ∇ᵏRm` (`nablaKRm04Field S t k`,
`Evolution/RmRealizationBridgeAllK.lean`, rank `4 + k`), the two *rank-uniform,
frame-free* Bochner lemmas:

* the **time-derivative half**
  `Tensor0SBundle.hasDerivWithinAt_normSq0S_ricciFlow`
  (`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`): under `∂ₜg = −2 Ric`,
  `∂ₜ‖T‖² = (Ric ∗ T²) + 2⟨∂ₜT, T⟩` at any rank, derived from the component time
  derivative `∂ₜT` — **no** assembled-heat hypothesis;
* the **Laplacian half** `Tensor0SBundle.tensorNormBochnerSplit_mc`
  (`Tensor/RSTensor/FiberMetric/Tensor0SBochnerProduct.lean`):
  `Δ‖T‖² = 2⟨ΔT, T⟩ + 2‖∇T‖²` at any rank, hypothesis-free (taking only the
  standard realization inputs — the same frontier as the `(0,2)` `ricci_lap_mc`).

The realization inputs at rank `4 + k` are **discharged** from the all-`k` bridge:
`nablaKRm04Field_realizes S t k` realizes `∇^{k+1}Rm`, and
`nablaKRm04Field_realizes S t (k+1)` realizes `∇^{k+2}Rm`, both from the canonical
`totalNabla0S_realizes` (no axiomatization).  The `4 + (k+1) = (4+k) + 1` arity
step is definitional, so the rank-`(4+k)` Bochner split takes
`nablaKRm04Field S t (k+1)` / `nablaKRm04Field S t (k+2)` for `∇T` / `∇²T` directly.

## What it produces

Writing `u = |∇ᵏRm|²`, `Δ|∇ᵏRm|²` for the Hessian trace, `nabla2 = |∇^{k+1}Rm|²`,
and the **rough Laplacian** `Δ∇ᵏRm = metricTrace0S2TensorInBasis basis gInv (∇^{k+2}Rm)`:

* **subtracting** the two splits gives the heat-equation identity
  `∂ₜ|∇ᵏRm|² = Δ|∇ᵏRm|² − 2|∇^{k+1}Rm|² + reaction`,
  with the reaction the **derived**
  `reaction = (Ric ∗ ∇ᵏRm²) + 2⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩`
  (`nablaKRm04ReactionIntrinsic`): the standard BBS reaction, *no* renamed
  hypothesis;
* `nablaKRm04NormHeatEquationOn_intrinsic` packages this as the producer predicate
  `NablaRm04NormHeatEquationOn` (`Evolution/NablaRiemannHeat.lean`) in the
  intrinsic fibre norms.

The `k = 1` specialization reproduces `nablaRm04NormHeatEquationOn_intrinsic`
exactly (`nablaKRm04Field S t 1 = nablaRm04Field S t` definitionally).

## Honest input status

Exactly as the `k = 1` template `nablaRm04NormHeatEquationOn_intrinsic`: the
realization inputs (`DuFieldRealizes`/`HessianRealizesNablaDuAt` of `|∇ᵏRm|²`,
smooth basis fields, the genuine inverse metric, the metric-compatible connection,
the Ricci-flow inverse-metric derivative relation, and the **component time
derivative `∂ₜ∇ᵏRm`** of `∇ᵏRm`) are taken as hypotheses **at the same status the
`(0,2)` producer `ricci_heat_mc` takes them**.  The advance over the per-rank
status is that the assembled heat **equation** is *derived* from the two general
Bochner lemmas plus the component time derivative; the moving-metric `∂ₜg`
reaction term is supplied intrinsically by `hasDerivWithinAt_normSq0S_ricciFlow`,
not assumed.

The covariant-derivative realizations `∇^{k+1}Rm`/`∇^{k+2}Rm` are **not**
hypotheses: they are discharged by `nablaKRm04Field_realizes`.

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
-- structure diamond (KNOWN PITFALL), mirroring `NablaRiemannHeatFull.lean`.
private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance

/-! ## The intrinsic scalar fields of the all-`k` heat equation

All scalar fields are intrinsic (frame-free) functions of `(t, x)`, the
rank-uniform generalizations of the `k = 1` fields. -/

section Fields

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The intrinsic squared norm `|∇ᵏRm|²` of the bundled `∇ᵏRm` (`nablaKRm04Field`),
rank `4 + k`.  Rank-uniform generalization of `nablaRm04NormSqIntrinsic`. -/
def nablaKRm04NormSqIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) : Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.base.metric t) x (4 + k)
    (nablaKRm04Field (I := I) S t k x)

/-- The **derived all-`k` reaction** `(Ric ∗ ∇ᵏRm²) + 2⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩`.

`ric` is the (frame-component) Ricci array; `Tdot t x` is the abstract fibre value
of `∂ₜ∇ᵏRm`; the second term is the contraction of the heat residual
`(∂ₜ − Δ)∇ᵏRm = ∂ₜ∇ᵏRm − roughLap(∇^{k+2}Rm)` against `∇ᵏRm`.  The metric reaction
is the `ricReactionContract` produced from the moving-metric `∂ₜg` term of
`hasDerivWithinAt_normSq0S_ricciFlow`.  Rank-uniform generalization of
`nablaRm04ReactionIntrinsic`. -/
def nablaKRm04ReactionIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x) : Real -> M -> Real :=
  fun t x =>
    ricReactionContract (gInv t x) (ric t x)
        (fun I0 : Fin (4 + k) -> Idx =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) I0)
        (fun J0 : Fin (4 + k) -> Idx =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) J0) +
      2 * inner0S (I := I) (S.base.metric t) x (4 + k)
            (Tdot t x -
              metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                (nablaKRm04Field (I := I) S t (k + 2) x))
            (nablaKRm04Field (I := I) S t k x)

/-- Pointwise form of the all-`k` reaction, using one tangent-space basis and
the corresponding inverse-metric and Ricci component arrays. -/
def nablaKReactionAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M)
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x) : Real :=
  ricReactionContract gInv ric
      (fun I0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
          (fun i => basis i) I0)
      (fun J0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
          (fun i => basis i) J0) +
    2 * inner0S (I := I) (S.base.metric t) x (4 + k)
      (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
        (nablaKRm04Field (I := I) S t (k + 2) x))
      (nablaKRm04Field (I := I) S t k x)

end Fields

/-! ## Spatial regularity of the intrinsic tower norms -/

/-- At each fixed time, the intrinsic squared norm `|∇ᵏRm|²` is smooth in
space for every finite tower level `k`. -/
theorem nablaKNorm_smooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (nablaKRm04NormSqIntrinsic (I := I) S k t) := by
  simpa [nablaKRm04NormSqIntrinsic] using
    (normSq0S_smooth (I := I) (S.base.metric t)
      (nablaKRm04Field (I := I) S t k))

/-- Canonical differential of the fixed-time scalar field `|∇ᵏRm|²`. -/
noncomputable def nablaKNormDu
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  duSec (I := I) (nablaKRm04NormSqIntrinsic (I := I) S k t)
    (nablaKNorm_smooth (I := I) S t k)

/-- Canonical Hessian of the fixed-time scalar field `|∇ᵏRm|²`. -/
noncomputable def nablaKNormHess
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  hessianSec (I := I) (S.family.connection t) (connSmoothInf (I := I) S t)
    (nablaKRm04NormSqIntrinsic (I := I) S k t)
    (nablaKNorm_smooth (I := I) S t k)

/-- Intrinsic scalar Laplacian of the fixed-time field `|∇ᵏRm|²`. -/
noncomputable def nablaKNormLap
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) : Real → M → Real :=
  fun t x => laplacian (I := I) (S.family.connection t) (S.base.metric t)
    (nablaKRm04NormSqIntrinsic (I := I) S k t) x

/-! ## The intrinsic all-`k` heat equation

The core assembly: the two Bochner lemmas, instantiated at `∇ᵏRm`, combine into
the `NablaRm04NormHeatEquationOn` predicate. -/

section HeatEquation

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Pointwise intrinsic heat equation for `|∇ᵏRm|²`. All spatial differential
objects and smooth extensions of the chosen basis vectors are canonical; the
only supplied data are the target-point time derivatives of the inverse metric
and of `∇ᵏRm`. -/
theorem nablaKNormHeatAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real → Idx → Idx → Real)
    (ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x)
    (hinv : ∀ r : Real,
      MetricInverseInBasis (I := I) (S.base.metric r) x basis (gInv r))
    (hT : ∀ I0 : Fin (4 + k) → Idx,
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k x)
            (fun i => basis i) I0)
        (tensor0SComponent (I := I) Tdot (fun i => basis i) I0)
        D.carrier (t : Real))
    (hgInvDt : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) i p * gInv (t : Real) j q * ric p q))
        D.carrier (t : Real)) :
    HasDerivWithinAt
      (fun r : Real => nablaKRm04NormSqIntrinsic (I := I) S k r x)
      (nablaKNormLap (I := I) S k (t : Real) x +
        (-2 * nablaKRm04NormSqIntrinsic (I := I) S (k + 1) (t : Real) x +
          nablaKReactionAt (I := I) S k (t : Real) x basis
            (gInv (t : Real)) ric Tdot))
      D.carrier (t : Real) := by
  classical
  have hmc : IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real)) :=
    solution_isMetricCompatible (I := I) S (t : Real)
  let X : Idx → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun i =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis i)).choose
  have hfields : SmoothBasisFieldsAt (I := I) basis X := by
    intro i
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis i)).choose_spec
  have hf := nablaKNorm_smooth (I := I) S (t : Real) k
  have hdu : DuFieldRealizes (I := I)
      (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real))
      (nablaKNormDu (I := I) S (t : Real) k) := by
    simpa [nablaKNormDu] using
      (duSec_realizes (I := I)
        (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real)) hf)
  have hHess : HessianRealizesNablaDuAt (I := I)
      (S.family.connection (t : Real))
      (nablaKNormDu (I := I) S (t : Real) k)
      (nablaKNormHess (I := I) S (t : Real) k) x := by
    simpa [nablaKNormDu, nablaKNormHess] using
      (hessianSec_realizesAt (I := I)
        (S.family.connection (t : Real)) (connSmoothInf (I := I) S (t : Real))
        (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real)) hf x)
  have hlapReal :=
    scalarLap_smooth (I := I)
      (S.family.connection (t : Real)) (connSmoothInf (I := I) S (t : Real))
      (S.base.metric (t : Real)) hmc
      (x := x) (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real)) hf
  have hlapBasis :=
    ScalarLaplacianRealizesTraceAt.toInBasis (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real))
      basis (gInv (t : Real)) (hinv (t : Real))
      (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real))
      (nablaKNormHess (I := I) S (t : Real) k x) hlapReal
  have hlap :
      nablaKNormLap (I := I) S k (t : Real) x =
        metricTrace0S2InBasis (I := I) basis (gInv (t : Real))
          (nablaKNormHess (I := I) S (t : Real) k x) Fin.elim0 := by
    simpa [nablaKNormLap] using hlapBasis
  have hdt :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I)
      (s := 4 + k) (x := x) (u := D.carrier) (t := (t : Real))
      (g := fun r : Real => S.base.metric r)
      (gInv := gInv)
      (gInvDt := fun i j => 2 * (∑ p : Idx, ∑ q : Idx,
        gInv (t : Real) i p * gInv (t : Real) j q * ric p q))
      (ric := ric)
      (T := fun r : Real => nablaKRm04Field (I := I) S r k x)
      (Tdt := fun I0 =>
        tensor0SComponent (I := I) Tdot (fun i => basis i) I0)
      (Tdot := Tdot)
      (basis := basis)
      hinv hgInvDt hT (fun I0 => rfl) (fun i j => rfl)
  have hsplit :=
    tensorNormBochnerSplit_mc (I := I) (s := 4 + k)
      (cov := S.family.connection (t : Real))
      (g := S.base.metric (t : Real))
      hmc (basis := basis) (gInv := gInv (t : Real)) (hinv (t : Real))
      (Xb := X) hfields
      (T := nablaKRm04Field (I := I) S (t : Real) k)
      (nablaT := nablaKRm04Field (I := I) S (t : Real) (k + 1))
      (nabla2T := nablaKRm04Field (I := I) S (t : Real) (k + 2))
      (nablaKRm04Field_realizes (I := I) S (t : Real) k)
      (nablaKRm04Field_realizes (I := I) S (t : Real) (k + 1))
      (du := nablaKNormDu (I := I) S (t : Real) k)
      (normSecond := nablaKNormHess (I := I) S (t : Real) k)
      hdu hHess
  refine hdt.congr_deriv ?_
  rw [hlap, nablaKReactionAt, nablaKRm04NormSqIntrinsic]
  set A := ricReactionContract (gInv (t : Real)) ric
      (fun I0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis i) I0)
      (fun J0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis i) J0) with hA
  set Rm := nablaKRm04Field (I := I) S (t : Real) k x with hRm
  have hsub :
      inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
          (Tdot - metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
            (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm =
        inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) Tdot Rm -
          inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
            (metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm := by
    simp only [inner0S, MetricFiberData.inner, map_sub, LinearMap.sub_apply]
  rw [hsub]
  set B := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) Tdot Rm with hB
  set C := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
      (metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
        (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm with hC
  have hsplit' :
      metricTrace0S2InBasis (I := I) basis (gInv (t : Real))
          (nablaKNormHess (I := I) S (t : Real) k x) Fin.elim0 =
        2 * C +
          2 * normSq0S (I := I) (S.base.metric (t : Real)) x (4 + (k + 1))
            (nablaKRm04Field (I := I) S (t : Real) (k + 1) x) := hsplit
  rw [hsplit']
  ring

/-- **The intrinsic all-`k` heat equation for `|∇ᵏRm|²`.**

Instantiating the time-derivative Bochner lemma `hasDerivWithinAt_normSq0S_ricciFlow`
(giving `∂ₜ|∇ᵏRm|² = ricReaction + 2⟨∂ₜ∇ᵏRm, ∇ᵏRm⟩`) and the Laplacian Bochner split
`tensorNormBochnerSplit_mc` (giving `Δ|∇ᵏRm|² = 2⟨Δ∇ᵏRm, ∇ᵏRm⟩ + 2|∇^{k+1}Rm|²`) at
`T = ∇ᵏRm`, and *subtracting*, the heat equation
`∂ₜu = uLap + (−2·nabla2 + reaction)` holds with

* `u = nablaKRm04NormSqIntrinsic S k` (`= |∇ᵏRm|²`);
* `uLap = metricTrace0S2InBasis (basis x) (gInv t x) (normSecond t x) Fin.elim0`
  (`= Δ|∇ᵏRm|²`, the realized Hessian trace, as in the `(0,2)` `hlapTrace`);
* `nabla2 = nablaKRm04NormSqIntrinsic S (k+1)` (`= |∇^{k+1}Rm|²`);
* `reaction = nablaKRm04ReactionIntrinsic` (`= (Ric ∗ ∇ᵏRm²) + 2⟨(∂ₜ − Δ)∇ᵏRm, ∇ᵏRm⟩`).

The covariant-derivative realizations of `∇^{k+1}Rm` / `∇^{k+2}Rm` are discharged
from `nablaKRm04Field_realizes`; the remaining hypotheses are the realization
inputs of the two Bochner lemmas — at exactly the status the `(0,2)`
`ricci_heat_mc` takes them — plus the Ricci-flow inverse-metric-derivative relation
`hgInvDt` and the component time derivative `hT`/`Tdot` of `∇ᵏRm`.

This is the rank-uniform generalization of `nablaRm04NormHeatEquationOn_intrinsic`
(`k = 1`). -/
theorem nablaKRm04NormHeatEquationOn_intrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Xb : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nablaKRmNormLap : Real -> M -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x)
    (hinv : ∀ (t : Real) (x : M),
      MetricInverseInBasis (I := I) (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x : M, SmoothBasisFieldsAt (I := I) (basis x) (Xb x))
    (hdu : ∀ t : Real,
      DuFieldRealizes (I := I)
        (fun y : M => normSq0S (I := I) (S.base.metric t) y (4 + k)
          (nablaKRm04Field (I := I) S t k y)) (du t))
    (hHess : ∀ (t : Real) (x : M),
      HessianRealizesNablaDuAt (I := I) (S.family.connection t) (du t)
        (normSecond t) x)
    (hlapTrace : ∀ (t : Real) (x : M),
      nablaKRmNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hT : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (I0 : Fin (4 + k) -> Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k x)
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
      (nablaKRm04NormSqIntrinsic (I := I) S k)
      nablaKRmNormLap
      (nablaKRm04NormSqIntrinsic (I := I) S (k + 1))
      (nablaKRm04ReactionIntrinsic (I := I) S k basis gInv ric Tdot) := by
  classical
  intro t x
  -- The metric-compatible Levi-Civita connection of the solution.
  have hmc : IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real)) :=
    solution_isMetricCompatible (I := I) S (t : Real)
  -- The time-derivative Bochner lemma at `T = ∇ᵏRm`, under the Ricci-flow
  -- inverse-metric-derivative relation, gives
  -- `∂ₜ|∇ᵏRm|² = ricReaction + 2⟨∂ₜ∇ᵏRm, ∇ᵏRm⟩`.
  have hdt :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I)
      (s := 4 + k) (x := x) (u := D.carrier) (t := (t : Real))
      (g := fun r : Real => S.base.metric r)
      (gInv := fun r : Real => gInv r x)
      (gInvDt := fun i j => 2 * (∑ p : Idx, ∑ q : Idx,
        gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
      (ric := ric (t : Real) x)
      (T := fun r : Real => nablaKRm04Field (I := I) S r k x)
      (Tdt := fun I0 =>
        tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
      (Tdot := Tdot (t : Real) x)
      (basis := basis x)
      (fun r => hinv r x)
      (hgInvDt t x)
      (hT t x)
      (fun I0 => rfl)
      (fun i j => rfl)
  -- The Laplacian Bochner split at `T = ∇ᵏRm`:
  -- `Δ|∇ᵏRm|² = 2⟨Δ∇ᵏRm, ∇ᵏRm⟩ + 2|∇^{k+1}Rm|²`.
  have hsplit :=
    tensorNormBochnerSplit_mc (I := I) (s := 4 + k)
      (cov := S.family.connection (t : Real))
      (g := S.base.metric (t : Real))
      hmc (basis := basis x) (gInv := gInv (t : Real) x) (hinv t x)
      (Xb := Xb x) (hfields x)
      (T := nablaKRm04Field (I := I) S (t : Real) k)
      (nablaT := nablaKRm04Field (I := I) S (t : Real) (k + 1))
      (nabla2T := nablaKRm04Field (I := I) S (t : Real) (k + 2))
      (nablaKRm04Field_realizes (I := I) S (t : Real) k)
      (nablaKRm04Field_realizes (I := I) S (t : Real) (k + 1))
      (du := du (t : Real)) (normSecond := normSecond (t : Real))
      (hdu (t : Real)) (hHess (t : Real) x)
  -- Convert the derivative value to the producer's RHS.
  refine hdt.congr_deriv ?_
  -- Unfold the reaction, the Hessian-trace Laplacian, and the next-level norm field.
  rw [hlapTrace (t : Real) x, nablaKRm04ReactionIntrinsic, nablaKRm04NormSqIntrinsic]
  -- Abbreviate the four scalar atoms.  The rough-Laplacian inner product `C` and the
  -- next-level norm `F` are pinned to *fixed forms*; the Bochner split `hsplit`
  -- produces the same scalars at the definitionally-equal arities `(4+k)+1`/`(4+k)+2`
  -- (vs the reaction's `4+(k+1)`/`4+(k+2)`), so we reconcile them by `rfl` rather
  -- than relying on syntactic folding.
  set A := ricReactionContract (gInv (t : Real) x) (ric (t : Real) x)
      (fun I0 : Fin (4 + k) -> Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis x i) I0)
      (fun J0 : Fin (4 + k) -> Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis x i) J0) with hA
  set Rm := nablaKRm04Field (I := I) S (t : Real) k x with hRm
  -- `inner0S (Tdot − roughT) Rm = inner0S Tdot Rm − inner0S roughT Rm`.
  have hsub :
      inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
          (Tdot (t : Real) x -
            metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm =
        inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) (Tdot (t : Real) x) Rm -
          inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
            (metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm := by
    simp only [inner0S, MetricFiberData.inner, map_sub, LinearMap.sub_apply]
  rw [hsub]
  -- The goal is now a linear identity over four real atoms `A`, `B = ⟨Tdot,Rm⟩`,
  -- `C = ⟨Δ∇ᵏRm,Rm⟩`, `F = |∇^{k+1}Rm|²`.  `hsplit`'s `C`/`F` are *defeq* to the
  -- reaction's; supply the bridging `rfl`s and finish with `linarith`.
  set B := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) (Tdot (t : Real) x) Rm
    with hB
  set C := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
      (metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
        (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm with hC
  -- The Bochner split, with its `C`/`F` reconciled to the fixed atoms by `rfl`.
  have hsplit' :
      metricTrace0S2InBasis (I := I) (basis x) (gInv (t : Real) x)
          (normSecond (t : Real) x) Fin.elim0 =
        2 * C +
          2 * normSq0S (I := I) (S.base.metric (t : Real)) x (4 + (k + 1))
            (nablaKRm04Field (I := I) S (t : Real) (k + 1) x) := hsplit
  rw [hsplit']
  ring

end HeatEquation

/-! ## The rank-uniform iterated time derivative `∂ₜ∇ᵏRm`

We build the **all-`k` time derivative of the component tower** `iteratedRmComp`,
by induction on `k` from the rank-uniform single-step time-derivative identity
`covDerivStepComp_hasDerivWithinAt` (`Evolution/NablaRiemannTimeDeriv.lean`).  This
generalizes `iteratedRmComp_one_hasDerivWithinAt` (`k = 1`) to every `k`.

The explicit time-derivative array `iteratedRmCompDt` is defined by the same
recursion shape as `iteratedRmComp`: at level `k+1` it is

`∂ₜ(∇^{k+1}Rm) = ∇(∂ₜ∇ᵏRm) − (∂ₜΓ) ∗ ∇ᵏRm`
            `= covDerivStepComp (frameExtData (∂ₜ∇ᵏRm)) (chr) (∂ₜ∇ᵏRm)`
            `  − covDerivStepDt (∂ₜΓ) (∇ᵏRm)`,

i.e. the covariant derivative of `∂ₜ∇ᵏRm` minus the Christoffel-time-derivative
correction on `∇ᵏRm` — exactly the `k = 1` identity at every level.

We work at the pure component level (matching `iteratedRmComp`/`covDerivStepComp`),
so no curvature/metric/Ricci-flow hypothesis enters; the three geometric inputs
(`∂ₜRm`, `∂ₜΓ`, and the per-level spatial-frame/time derivative swap) are taken as
the cited interface hypotheses, exactly as at `k = 1`. -/

section IteratedTimeDeriv

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The explicit **iterated time-derivative array** `∂ₜ∇ᵏRm` of the component tower
`iteratedRmComp frame chr base`, by recursion on `k` mirroring `iteratedRmComp`.

* `k = 0`: the supplied base time derivative `baseDt` (`= ∂ₜRm`).
* `k+1`: `covDerivStepComp (frameExtData (∂ₜ∇ᵏRm)) (chr) (∂ₜ∇ᵏRm) − covDerivStepDt (∂ₜΓ) (∇ᵏRm)`,
  the covariant derivative of `∂ₜ∇ᵏRm` minus the `(∂ₜΓ) ∗ ∇ᵏRm` correction.

`chrDt` is the Christoffel time-derivative datum `∂ₜΓ`.  Rank-uniform
generalization of the level-1 time-derivative value in
`iteratedRmComp_one_hasDerivWithinAt`. -/
def iteratedRmCompDt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real)
    (baseDt : Real → M → (Fin 4 → Idx) → Real) :
    (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real
  | 0 => baseDt
  | (k + 1) => fun t x =>
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iteratedRmCompDt frame chr chrDt base baseDt k t y) x)
        (chr t x)
        (iteratedRmCompDt frame chr chrDt base baseDt k t x) -
      covDerivStepDt (chrDt t x)
        (iteratedRmComp (I := I) frame chr base k t x)

@[simp] theorem iteratedRmCompDt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base baseDt : Real → M → (Fin 4 → Idx) → Real) :
    iteratedRmCompDt (I := I) frame chr chrDt base baseDt 0 = baseDt := rfl

theorem iteratedRmCompDt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base baseDt : Real → M → (Fin 4 → Idx) → Real) (k : ℕ) (t : Real) (x : M) :
    iteratedRmCompDt (I := I) frame chr chrDt base baseDt (k + 1) t x =
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t y) x)
        (chr t x)
        (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x) -
      covDerivStepDt (chrDt t x)
        (iteratedRmComp (I := I) frame chr base k t x) := rfl

/-- **The rank-uniform iterated time-derivative identity for `∇ᵏRm`.**

For the component tower `iteratedRmComp frame chr base` over a Ricci-flow solution,
the level-`k` array `s ↦ ∇ᵏRm(s)` is differentiable in time with derivative the
explicit `iteratedRmCompDt frame chr chrDt base baseDt k`, i.e. `∂ₜ∇ᵏRm`.

Proved by **induction on `k`** from the rank-uniform single-step time-derivative
identity `covDerivStepComp_hasDerivWithinAt` (`Evolution/NablaRiemannTimeDeriv.lean`):

* base `k = 0`: `hrm` (`= ∂ₜRm`, the level-0 time derivative);
* step `k+1`: feed the inductive hypothesis (each level-`k` component is
  differentiable with derivative `iteratedRmCompDt k`) as the step lemma's `hA`
  data, with `hchr` (`= ∂ₜΓ`) and the per-level swap `hswap k` (the
  spatial-frame/time derivative swap for level `k`).

The three geometric inputs are the cited interface hypotheses, exactly as at
`k = 1` (`iteratedRmComp_one_hasDerivWithinAt`):

* `hrm` — the level-0 time derivative `∂ₜRm` (Uhlenbeck curvature evolution);
* `hchr` — the Christoffel time derivative `∂ₜΓ` (`evol_christoffel_inFrame`);
* `hswap` — the per-level spatial-frame/time derivative swap
  (`FixedBaseExtDerivTimeDerivativeOnRegular`), for the inductively-built
  `iteratedRmCompDt` at each level.

This is the all-`k` `∂ₜ∇ᵏRm` producer the task's piece (1) asks for; no
time-derivative fact is axiomatized here. -/
theorem iteratedRmComp_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base baseDt : Real → M → (Fin 4 → Idx) → Real)
    {D : Set Real} {t : Real} (x : M)
    (hrm : ∀ m : Fin 4 → Idx,
      HasDerivWithinAt (fun s : Real => base s x m) (baseDt t x m) D t)
    (hchr : ∀ i a p : Idx,
      HasDerivWithinAt (fun s : Real => chr s x i a p) (chrDt t x i a p) D t)
    (hswap : ∀ (k : ℕ) (d : Idx) (m : Fin (4 + k) → Idx),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => iteratedRmComp (I := I) frame chr base k s y m) x
            (frame d x))
        (extDerivFun (I := I)
          (fun y : M => iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t y m) x
          (frame d x))
        D t) :
    ∀ (k : ℕ) (n : Fin (4 + k) → Idx),
      HasDerivWithinAt
        (fun s : Real => iteratedRmComp (I := I) frame chr base k s x n)
        (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x n)
        D t := by
  intro k
  induction k with
  | zero =>
      intro n
      simpa [iteratedRmComp_zero, iteratedRmCompDt_zero] using hrm n
  | succ k ih =>
      intro n
      -- Unfold both the array and its time-derivative at level `k+1` to the bare
      -- `covDerivStepComp`/correction shape.
      rw [show
          (fun s : Real => iteratedRmComp (I := I) frame chr base (k + 1) s x n) =
            fun s : Real =>
              covDerivStepComp
                (frameExtData (I := I) frame
                  (fun y : M => iteratedRmComp (I := I) frame chr base k s y) x)
                (chr s x)
                (iteratedRmComp (I := I) frame chr base k s x) n from by
        funext s; rw [iteratedRmComp_succ]]
      rw [iteratedRmCompDt_succ]
      -- Apply the rank-uniform single-step time-derivative identity with the
      -- inductive hypothesis as the `hA` data and the level-`k` swap.
      exact covDerivStepComp_hasDerivWithinAt
        (I := I) frame
        (iteratedRmComp (I := I) frame chr base k)
        (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k)
        chr chrDt x n
        (fun m => ih m)
        hchr
        (fun m => hswap k (n 0) m)

end IteratedTimeDeriv

/-! ## Nonnegativity of the next-level norm -/

section Nonneg

/-- The intrinsic `|∇ᵏRm|²` is nonnegative (the fibre inner product is positive
semidefinite). -/
theorem nablaKRm04NormSqIntrinsic_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M) :
    0 ≤ nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  unfold nablaKRm04NormSqIntrinsic
  rw [normSq0S_eq_inner]
  exact (tensor0SMetricData (I := I) (S.base.metric t) x (4 + k)).inner_nonneg
    (nablaKRm04Field (I := I) S t k x)

end Nonneg

end DifferentialGeometry.PDE.RicciFlow
