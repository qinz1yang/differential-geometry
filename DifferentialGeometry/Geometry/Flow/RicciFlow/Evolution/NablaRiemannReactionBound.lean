import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannT1Bound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannT2Bound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmFrozenSlotField
import DifferentialGeometry.Geometry.Operator.CotangentSharpSmooth
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The `k = 1` quantitative reaction bound `|nablaLapCommReactionTerm| ≤ C·|Rm|·|∇Rm|`

This file assembles the **`T₁` quantitative bound** (route 2, piece (3)) and combines
it with the already-proved `T₂` bound (`Evolution/NablaRiemannT2Bound.lean`) to give
the full `k = 1` curvature reaction bound, then discharges the `k = 1` heat producer.

All prerequisites are banked, sorry-free and axiom-clean (see
`Evolution/IteratedNablaRmTower.md`, follow-ups 5–9).
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

/-- The solution connection is metric-compatible (Levi-Civita). -/
theorem solution_isMetricCompatible
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.base.metric t) := by
  simpa [SolutionFamily.connection, metricCov] using
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (S.base.metric t)

/-! ## The sharp field of a frozen one-form of `Rm04` and its smoothness

The route-2 K-Leibniz differentiates `K = -Σ_q rm04(…, g♯ βq)` with
`βq = oneFormAtSlot0S Rm04 slots q` the slot-frozen one-form
(`RmRaisingBridge.curvatureAction0SAt_eq_rm04_raise`).  The raised vector field
`y ↦ g♯ (βq y)` enters as the moving fourth slot of the outer `Rm04`.  We package
it as a bundled smooth tangent section so `nabla0SFun_eval_smooth_slots` applies. -/

open DifferentialGeometry.Integral.DivergenceTheorem
  DifferentialGeometry.Integral.Measure in
set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the frozen-one-form chart-basis components: the frozen one-form
field `rmFrozenSlotField S t q Y` evaluated on a chart-basis frame vector is `C^∞`
on each chart source.  This discharges the `hβ` hypothesis of
`cotangentSharp_gen_mdiffAt` / `cotangentSharp_gen_contMDiff_total`.

The `set_option backward.isDefEq.respectTransparency false` is required (as in the
`freezeAllBut04Field` definition itself) so the `Tensor0SModel` model-fibre
`NormedSpace`/`NormedAddCommGroup` instances unify when the bundled field's
smoothness `(...).contMDiff` is fed to `contMDiffAt_section_apply_gen`. -/
theorem rmFrozenSlot_chartBasis_contMDiffOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α : M) (j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real) ∞
      (fun b : M =>
        rmFrozenSlotField (I := I) S t q Y b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  -- The chart-basis component is `Rm04(b)(update (Y · b) q (chartBasisVec))`, the
  -- evaluation of the smooth `(0,1)` field `freezeAllBut04Field Rm04 q Y` on a
  -- smooth chart-basis section, hence smooth on the chart source.
  have hval : ∀ b : M,
      rmFrozenSlotField (I := I) S t q Y b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) =
        (freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y) b
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
    intro b; rfl
  simp only [hval]
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  -- The chart-basis vector section is smooth at `x₀ ∈ chart source`.
  have hv_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun b : M =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
            (chartBasisVecFiber (I := I) α j b)) x₀ :=
    (chartBasisVec_contMDiffOn (I := I) α j).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds
        (by
          rw [trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M)]
          exact hx₀))
  -- Pass the bundled field's smoothness inline so the expected type pins the
  -- `Tensor0SModel` model-fibre instances.
  have h_eval := TensorMultilinear.contMDiffAt_section_apply_gen
    (𝕜 := Real) (I := I) (M := M) (n := 1) (x₀ := x₀)
    (T := fun b : M => (freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y) b)
    ((freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y).contMDiff x₀)
    (v := fun _ : Fin 1 => fun b : M => chartBasisVecFiber (I := I) α j b)
    (fun _ => hv_at)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using h_eval

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- **`MDiffAt` of the raised frozen one-form field.**  The sharp field
`y ↦ g♯ (βq y)` of the frozen one-form `βq = rmFrozenSlotField S t q Y` is
`MDifferentiableAt` everywhere.  This discharges the `hSharp` hypothesis of the
sharp-parallelism `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`. -/
theorem rmFrozenSlotSharp_mdiffAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDiffAt
      (T% (fun y : M =>
        cotangentSharp_gen (I := I) (S.base.metric t) y
          (rmFrozenSlotField (I := I) S t q Y y))) x :=
  cotangentSharp_gen_mdiffAt (I := I) (S.base.metric t)
    (β := fun y : M => rmFrozenSlotField (I := I) S t q Y y)
    (fun α j => rmFrozenSlot_chartBasis_contMDiffOn (I := I) S t q Y α j) x

open DifferentialGeometry.Integral.DivergenceTheorem in
/-- The raised frozen one-form field `y ↦ g♯ (βq y)`, bundled as a smooth tangent
section.  This is the moving fourth slot fed to the outer `Rm04` in the raise-form
curvature action.  Smoothness is `cotangentSharp_gen_contMDiff_total` via
`rmFrozenSlot_chartBasis_contMDiffOn`. -/
def rmFrozenSlotSharpSection
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk
    (fun y : M =>
      cotangentSharp_gen (I := I) (S.base.metric t) y
        (rmFrozenSlotField (I := I) S t q Y y))
    (cotangentSharp_gen_contMDiff_total (I := I) (S.base.metric t)
      (β := fun y : M => rmFrozenSlotField (I := I) S t q Y y)
      (fun α j => rmFrozenSlot_chartBasis_contMDiffOn (I := I) S t q Y α j))

@[simp] theorem rmFrozenSlotSharpSection_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (y : M) :
    rmFrozenSlotSharpSection (I := I) S t q Y y =
      cotangentSharp_gen (I := I) (S.base.metric t) y
        (rmFrozenSlotField (I := I) S t q Y y) :=
  rfl

/-! ## The per-`q` contraction Leibniz

The single `q`-th summand of the raise-form curvature action is
`Rm04(Vb, Vc, Vm_q, g♯βq)`, the outer `Rm04` contracted against the raised frozen
one-form `g♯βq` in its last slot.  We differentiate the scalar field
`y ↦ Rm04(y)(Vb y, Vc y, Vm_q y, g♯βq(y))` covariantly via
`nabla0SFun_eval_smooth_slots`, choosing the `Vb, Vc, Vm` slot sections covariantly
constant at `x₀` so their corrections vanish, leaving only the moving sharp-slot
correction, which the sharp-parallelism rewrites as `Rm04(…, g♯ ∇βq)`. -/

/-- The four outer-`Rm04` slot sections for the `q`-th raise-form summand: the two
derivative directions `Vb, Vc`, the `q`-th `Rm`-slot `Vm q`, and the raised frozen
one-form `g♯βq`. -/
def rmRaiseSlotSections
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ![Vb, Vc, Vm q, rmFrozenSlotSharpSection (I := I) S t q Vm]

/-- **The per-`q` contraction Leibniz (covariant derivative of one raise-form
summand).**  At the chart centre `x₀`, for a Ricci-flow solution at a regular time,
with derivative section `X` and slot sections `Vb, Vc, Vm` chosen covariantly
constant at `x₀` along `X`, the directional derivative of the `q`-th raise-form
scalar `y ↦ Rm04(y)(Vb y, Vc y, Vm_q y, g♯βq(y))` equals

`(∇Rm04)(X x₀, Vb x₀, Vc x₀, Vm_q x₀, g♯βq x₀) + Rm04 x₀ (Vb x₀, Vc x₀, Vm_q x₀, g♯(∇_X βq))`,

the two `Rm04 ∗ ∇Rm04` raise contractions: the first differentiates the outer
`Rm04`, the second differentiates the raised frozen one-form `g♯βq` (sharp-parallelism
`cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`, `∇βq` given by
`nablaRmFrozenSlot_eval`). -/
theorem rmRaise_summand_covDeriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) (q : Fin 4)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    extDerivFun (I := I)
        (fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                (rmFrozenSlotField (I := I) S (t : Real) q Vm y))))
        x₀ (X x₀) =
      nablaRm04Field (I := I) S (t : Real) x₀
          (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀))) +
        S.base.rm04 (t : Real) x₀
          (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)))) := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def
  -- The four outer-`Rm04` slot sections.
  set W : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    rmRaiseSlotSections (I := I) S (t : Real) q Vb Vc Vm with hW_def
  -- The slot sections at `x₀`.
  have hW0 : W 0 = Vb := rfl
  have hW1 : W 1 = Vc := rfl
  have hW2 : W 2 = Vm q := rfl
  have hW3 : W 3 = rmFrozenSlotSharpSection (I := I) S (t : Real) q Vm := rfl
  -- `eval_smooth_slots` for `Rm04` on the four slots `W`.
  have heval :=
    (nablaRm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X W x₀
  -- The scalar field `y ↦ Rm04(y)(W·y)` is the raise-form summand.
  have hscalar :
      (fun y : M => S.base.rm04 (t : Real) y (fun a : Fin 4 => W a y)) =
        fun y : M =>
          S.base.rm04 (t : Real) y
            (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                (rmFrozenSlotField (I := I) S (t : Real) q Vm y))) := by
    funext y
    congr 1
    funext a
    fin_cases a <;>
      simp [hW_def, rmRaiseSlotSections, vec4, rmFrozenSlotSharpSection_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  -- The `Fin.cons (X x₀) (W·x₀)` tuple is `vec5`.
  have hcons :
      (Fin.cons (X x₀) (fun a : Fin 4 => W a x₀) : Fin 5 → TangentSpace I x₀) =
        vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
          (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
            (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)) := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · rfl
    · rw [Fin.cons_succ]
      fin_cases j <;>
        simp [hW_def, rmRaiseSlotSections, vec5, rmFrozenSlotSharpSection_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  -- The correction sum: only the moving sharp slot (`a = 3`) survives.
  have hcorr :
      (∑ a : Fin 4,
          S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) a
              ((cov (fun p : M => W a p) x₀) (X x₀)))) =
        S.base.rm04 (t : Real) x₀
          (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
            (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)))) := by
    rw [Fin.sum_univ_four]
    -- Slots 0,1,2 are covariantly constant at `x₀`, killing their corrections.
    have hc0 : (cov (fun p : M => W 0 p) x₀) (X x₀) = 0 := by rw [hW0]; exact hVb
    have hc1 : (cov (fun p : M => W 1 p) x₀) (X x₀) = 0 := by rw [hW1]; exact hVc
    have hc2 : (cov (fun p : M => W 2 p) x₀) (X x₀) = 0 := by rw [hW2]; exact hVm q
    -- The `a = 3` correction: sharp-parallelism turns `cov(g♯βq)` into `g♯(∇βq)`.
    have hc3 :
        (cov (fun p : M => W 3 p) x₀) (X x₀) =
          cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
              (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)) := by
      have hsharp :=
        cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
          cov (S.base.metric (t : Real))
          (solution_isMetricCompatible (I := I) S (t : Real))
          (rmFrozenSlotField (I := I) S (t : Real) q Vm)
          (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm)
          (nablaRmFrozenSlotField_realizes (I := I) S (t : Real) q Vm)
          X x₀
          (rmFrozenSlotSharp_mdiffAt (I := I) S (t : Real) q Vm x₀)
      rw [hW3]
      -- `W 3 = rmFrozenSlotSharpSection`, whose value is `g♯βq`.
      simpa [rmFrozenSlotSharpSection_apply] using hsharp
    -- Drop the three vanishing corrections, keep the sharp one.
    rw [hc0, hc1, hc2, hc3]
    -- The three zero-corrected terms vanish by multilinearity (zero in a slot).
    rw [show
        S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) 0 (0 : TangentSpace I x₀)) = 0 from
      (S.base.rm04 (t : Real) x₀).map_update_zero _ 0]
    rw [show
        S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) 1 (0 : TangentSpace I x₀)) = 0 from
      (S.base.rm04 (t : Real) x₀).map_update_zero _ 1]
    rw [show
        S.base.rm04 (t : Real) x₀
            (Function.update (fun b : Fin 4 => W b x₀) 2 (0 : TangentSpace I x₀)) = 0 from
      (S.base.rm04 (t : Real) x₀).map_update_zero _ 2]
    simp only [zero_add, add_zero]
    -- The surviving `a = 3` term: rewrite `update W 3 c` to `vec4`.
    congr 1
    funext b
    fin_cases b <;>
      simp [hW_def, rmRaiseSlotSections, vec4, Function.update,
        rmFrozenSlotSharpSection_apply]
  -- Assemble: `extDerivFun(scalar) = nabla + corrections`.
  rw [← hscalar]
  -- `heval : nabla (cons X W) = extDerivFun(scalar') - Σcorr`, so
  -- `extDerivFun(scalar') = nabla (cons X W) + Σcorr`.
  rw [hcons] at heval
  rw [hcorr] at heval
  linarith [heval]

/-! ## The generic-frame `T₁` reduction on covariantly-constant sections

The producer consumes `T₁` in a **genuine orthonormal frame** (`exists_orthoBasisFrameAt`),
whose vectors are only pointwise-defined at `x₀`.  Since `T₁ = ∇³Rm(a,b,c) − ∇³Rm(a,c,b)`
is a tensor value at `x₀`, we realise the frame vectors by sections covariantly
constant at `x₀` (`exists_cov_zero_at_apply`), where the `eval_smooth_slots`
Christoffel corrections vanish, and reduce `T₁` to the directional derivative
`∇_X K` of the curvature-action field `K = [∇_b,∇_c]Rm = curvatureAction(rm13)(Rm04)`. -/

/-- The six `∇²Rm` slot sections `(Vb, Vc, Vm 0, …, Vm 3)` assembled as a
`metricTraceInput`-shaped tuple of sections. -/
def nabla2SlotSections
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin 6 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  Fin.cons Vb (Fin.cons Vc Vm)

/-- The six slot sections evaluated at a point form the `metricTraceInput` of the
two derivative directions and the four `Rm`-slots. -/
theorem nabla2SlotSections_apply
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (y : M) :
    (fun a : Fin 6 => nabla2SlotSections (I := I) Vb Vc Vm a y) =
      metricTraceInput (I := I) (Vb y) (Vc y)
        (fun i : Fin 4 => Vm i y) := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · rfl

/-- **The generic-frame `T₁` reduction on cov-constant sections.**  At `x₀`, for a
Ricci-flow solution at a regular time, with sections `X` (derivative), `Vb`, `Vc`,
`Vm` covariantly constant at `x₀` along `X`, the `∇³Rm` antisymmetrization

`nabla3(X x₀, Vb x₀, Vc x₀, Vm·x₀) − nabla3(X x₀, Vc x₀, Vb x₀, Vm·x₀)`

equals the directional derivative `∇_X K` of the curvature-action field
`K(y) = curvatureAction0SAt (rm13)(Rm04 y)(Vb y)(Vc y)(Vm·y)`, in the corrections-free
form (the cov-constant slots kill every `eval_smooth_slots` Christoffel correction):

`= extDerivFun (y ↦ curvatureAction0SAt (rm13)(Rm04 y)(Vb y)(Vc y)(Vm·y)) x₀ (X x₀)`. -/
theorem nabla3_antisym_eq_covDeriv_curvatureAction_covConst
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀))) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀))) =
      extDerivFun (I := I)
        (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y))
        x₀ (X x₀) := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def
  -- The six `∇²Rm` slot sections, in both `(b,c)` and `(c,b)` orders.
  set Wbc := nabla2SlotSections (I := I) Vb Vc Vm with hWbc_def
  set Wcb := nabla2SlotSections (I := I) Vc Vb Vm with hWcb_def
  -- The six slots are covariantly constant at `x₀`.
  have hWbc_cov : ∀ a : Fin 6, (cov (fun p : M => Wbc a p) x₀) (X x₀) = 0 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [hWbc_def, nabla2SlotSections] using hVb
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [hWbc_def, nabla2SlotSections] using hVc
      · simpa [hWbc_def, nabla2SlotSections] using hVm k
  have hWcb_cov : ∀ a : Fin 6, (cov (fun p : M => Wcb a p) x₀) (X x₀) = 0 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [hWcb_def, nabla2SlotSections] using hVc
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [hWcb_def, nabla2SlotSections] using hVb
      · simpa [hWcb_def, nabla2SlotSections] using hVm k
  -- `nabla3 = ∇(nabla2)`, evaluated via `eval_smooth_slots`; corrections vanish.
  have hbc :=
    (nabla3Rm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X Wbc x₀
  have hcb :=
    (nabla3Rm04Field_realizes (I := I) S (t : Real)).eval_smooth_slots X Wcb x₀
  -- Kill the correction sums (all slots cov-constant).
  have hbc_corr :
      (∑ a : Fin 6,
          nabla2Rm04Field (I := I) S (t : Real) x₀
            (Function.update (fun b : Fin 6 => Wbc b x₀) a
              ((cov (fun p : M => Wbc a p) x₀) (X x₀)))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hWbc_cov a]
    exact (nabla2Rm04Field (I := I) S (t : Real) x₀).map_update_zero _ a
  have hcb_corr :
      (∑ a : Fin 6,
          nabla2Rm04Field (I := I) S (t : Real) x₀
            (Function.update (fun b : Fin 6 => Wcb b x₀) a
              ((cov (fun p : M => Wcb a p) x₀) (X x₀)))) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hWcb_cov a]
    exact (nabla2Rm04Field (I := I) S (t : Real) x₀).map_update_zero _ a
  -- Rewrite the slot tuples at `x₀` as the `metricTraceInput`.
  have hWbc_x : (fun a : Fin 6 => Wbc a x₀) =
      metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀) :=
    nabla2SlotSections_apply (I := I) Vb Vc Vm x₀
  have hWcb_x : (fun a : Fin 6 => Wcb a x₀) =
      metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀) :=
    nabla2SlotSections_apply (I := I) Vc Vb Vm x₀
  rw [hbc_corr, sub_zero] at hbc
  rw [hcb_corr, sub_zero] at hcb
  rw [hWbc_x] at hbc
  rw [hWcb_x] at hcb
  -- `T₁ = extDerivFun(nabla2 bc) − extDerivFun(nabla2 cb) = extDerivFun(difference)`.
  rw [hbc, hcb]
  -- The two `nabla2` scalar fields (in slot-section form), `MDifferentiableAt`.
  have hmdiff_bc :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          nabla2Rm04Field (I := I) S (t : Real) p (fun a : Fin 6 => Wbc a p)) x₀ :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (nabla2Rm04Field (I := I) S (t : Real)) Wbc x₀).mdifferentiableAt (by simp)
  have hmdiff_cb :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          nabla2Rm04Field (I := I) S (t : Real) p (fun a : Fin 6 => Wcb a p)) x₀ :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (nabla2Rm04Field (I := I) S (t : Real)) Wcb x₀).mdifferentiableAt (by simp)
  rw [← extDerivFun_sub_at (I := I) (X x₀) hmdiff_bc hmdiff_cb]
  -- The difference field equals the curvature-action field, pointwise.
  have hfield :
      (fun y : M =>
          nabla2Rm04Field (I := I) S (t : Real) y (fun a : Fin 6 => Wbc a y) -
            nabla2Rm04Field (I := I) S (t : Real) y (fun a : Fin 6 => Wcb a y)) =
        fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y) := by
    funext y
    rw [nabla2SlotSections_apply (I := I) Vb Vc Vm y,
      nabla2SlotSections_apply (I := I) Vc Vb Vm y]
    exact rm04_ricciIdentityAt (I := I) S hS t y
      (Vb y) (Vc y) (fun i : Fin 4 => Vm i y)
  rw [hfield]

/-! ## The assembled K-Leibniz

Combining the generic-frame `T₁` reduction (`T₁ = ∇_X K = extDerivFun(K)` on
cov-constant sections) with the raise-form of `K`
(`curvatureAction0SAt_eq_rm04_raise`, `K = -Σ_q rm04(…, g♯βq)`) and the per-`q`
contraction Leibniz (`rmRaise_summand_covDeriv`), the `T₁` summand is the sum of the
two `Rm04 ∗ ∇Rm04` raise contractions. -/

/-- **The K-Leibniz for the `T₁` summand (on covariantly-constant sections).**

At `x₀`, for a Ricci-flow solution at a regular time, with sections `X` (derivative),
`Vb`, `Vc`, `Vm` covariantly constant at `x₀` along `X`, the `∇³Rm` antisymmetrization

`nabla3(X x₀, Vb x₀, Vc x₀, Vm·x₀) − nabla3(X x₀, Vc x₀, Vb x₀, Vm·x₀) = ∇_X([∇_b,∇_c]Rm)`

equals the negated sum of the two `Rm04 ∗ ∇Rm04` raise contractions

`= -Σ_q [ (∇Rm04)(X, Vb, Vc, Vm_q, g♯βq) + Rm04(Vb, Vc, Vm_q, g♯(∇_X βq)) ]`,

`βq = oneFormAtSlot0S Rm04 (Vm slots) q = rmFrozenSlotField S t q Vm`, the slot-frozen
one-form of `Rm04`.  This is the covariant Leibniz `∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm`
for the curvature action `K = [∇_b,∇_c]Rm`, derived through the metric-raising form
(no `∇rm13`): the first contraction differentiates the outer `Rm04`, the second the
raised frozen one-form `g♯βq` via the sharp-parallelism. -/
theorem nablaLapComm_T1_eq_rm04_raise_leibniz
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hVb : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVc : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVm : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀))) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀))) =
      -∑ q : Fin 4,
        (nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀))) +
          S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))) := by
  classical
  -- Step 1: `T₁ = extDerivFun(K)`.
  rw [nabla3_antisym_eq_covDeriv_curvatureAction_covConst (I := I) S hS t x₀
    X Vb Vc Vm hVb hVc hVm]
  -- Step 2: rewrite `K` pointwise via the raise form
  -- `K(y) = -Σ_q rm04(y)(Vb,Vc,Vm_q, g♯βq(y))`.
  have hKfield :
      (fun y : M =>
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
            (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y)) =
        fun y : M =>
          -∑ q : Fin 4,
            S.base.rm04 (t : Real) y
              (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
                (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
                  (rmFrozenSlotField (I := I) S (t : Real) q Vm y))) := by
    funext y
    rw [curvatureAction0SAt_eq_rm04_raise (I := I) (S.base.metric (t : Real))
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) y)
      (solution_rm04LowersRm13At (I := I) S (t : Real) y)
      (S.base.rm04 (t : Real) y) (Vb y) (Vc y) (fun i : Fin 4 => Vm i y)]
    -- The frozen one-form `oneFormAtSlot0S Rm04 (Vm·y) q` is `rmFrozenSlotField`
    -- (definitionally), so both sides agree.
    rfl
  rw [hKfield]
  -- The `q`-th raise-form summand field.
  set g : Fin 4 → M → Real := fun q y =>
    S.base.rm04 (t : Real) y
      (vec4 (I := I) (Vb y) (Vc y) (Vm q y)
        (cotangentSharp_gen (I := I) (S.base.metric (t : Real)) y
          (rmFrozenSlotField (I := I) S (t : Real) q Vm y))) with hg_def
  -- `MDifferentiableAt` of each `q`-th summand field (smooth `Rm04` on smooth slots).
  have hmdiff_q : ∀ q : Fin 4,
      MDifferentiableAt I 𝓘(Real, Real) (g q) x₀ := by
    intro q
    have h := (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (S.base.rm04 (t : Real))
      (rmRaiseSlotSections (I := I) S (t : Real) q Vb Vc Vm) x₀).mdifferentiableAt (by simp)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [hg_def]
    dsimp only
    congr 1
    funext a
    fin_cases a <;>
      simp [rmRaiseSlotSections, vec4, rmFrozenSlotSharpSection_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Step 3: `extDerivFun(-Σ_q g q) = -Σ_q extDerivFun(g q)`.
  have hstep3 :
      extDerivFun (I := I) (fun y : M => -∑ q : Fin 4, g q y) x₀ (X x₀) =
        -∑ q : Fin 4, extDerivFun (I := I) (g q) x₀ (X x₀) := by
    have hsumfun : (fun y : M => ∑ q : Fin 4, g q y) =
        (Finset.univ : Finset (Fin 4)).sum g := by
      funext y; simp [Finset.sum_apply]
    have hneg :
        extDerivFun (I := I) (fun y : M => -∑ q : Fin 4, g q y) x₀ (X x₀) =
          -extDerivFun (I := I) (fun y : M => ∑ q : Fin 4, g q y) x₀ (X x₀) :=
      extDerivFun_neg_at (I := I) (f := fun y : M => ∑ q : Fin 4, g q y) (X x₀)
        (by
          rw [hsumfun]
          exact MDifferentiableAt.sum (𝕜 := Real) (I := I)
            (t := (Finset.univ : Finset (Fin 4))) (fun q _ => hmdiff_q q))
    rw [hneg, hsumfun]
    rw [DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real (I := I)
      (t := (Finset.univ : Finset (Fin 4))) g (X x₀) (fun q _ => hmdiff_q q)]
  rw [hstep3]
  -- Each `q`-th `extDerivFun(g q)` is the per-`q` contraction Leibniz.
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hg_def]
  exact rmRaise_summand_covDeriv (I := I) S hS t x₀ q X Vb Vc Vm hVb hVc (fun i => hVm i)

/-! ## The `T₁` quantitative bound in a `g`-orthonormal basis

Each summand of the K-Leibniz is a `Rm04 ∗ ∇Rm04` raise contraction.  In a
`g`-orthonormal basis the raised covector `g♯β` reconstructs as `∑_e (β e_e) • e_e`
(`cotangentSharp_eq_sum_inv_gen` with `gᵃᵇ = δ`), so the contraction becomes a plain
frame-index double sum, and Cauchy–Schwarz bounds it by `card·√|Rm|·√|∇Rm|` per slot,
exactly as B's `abs_curvatureAction0SAt_orthoBasis_le`. -/

section T1Bound

variable {n : ℕ}

/-- In a `g`-orthonormal basis the raised covector reconstructs as the orthonormal
expansion `g♯ β = ∑_e (β e_e) • e_e`.  (Re-derivation of B's private
`cotangentSharp_orthoBasis_expand` of `Evolution/NablaRiemannT2Bound.lean`.) -/
theorem cotangentSharp_orthoBasis_expand'
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    cotangentSharp_gen (I := I) g x β =
      ∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) • basis e := by
  classical
  set gInv : Fin n → Fin n → Real := fun i j => if i = j then 1 else 0 with hgInv
  have hdiag : ∀ i : Fin n, gInv i i = 1 := by intro i; simp [hgInv]
  have hoff : ∀ i k : Fin n, i ≠ k → gInv i k = 0 := by
    intro i k hk; simp [hgInv, hk]
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_single i]
      · rw [hdiag i, one_mul]; exact horth i j
      · intro k _ hk; rw [hoff i k (fun h => hk h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [Finset.sum_eq_single j]
      · rw [hdiag j, mul_one]; exact horth i j
      · intro k _ hk; rw [hoff k j hk, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv β]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [hdiag i, one_mul, cotangentToDual_apply_gen]
  · intro j _ hj; rw [hoff i j (fun h => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Multilinearity of a `(0,5)` tensor `T` in its **last** slot, `vec5`-shaped. -/
theorem tensor05_vec5_sum_last
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (A B C D : TangentSpace I x)
    (coef : Fin n → Real) (vecs : Fin n → TangentSpace I x) :
    T (vec5 (I := I) A B C D (∑ e : Fin n, coef e • vecs e)) =
      ∑ e : Fin n, coef e * T (vec5 (I := I) A B C D (vecs e)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec5 (I := I) A B C D Z =
        Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4 Z := by
    intro Z; funext i; fin_cases i <;> simp [vec5, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (∑ e : Fin n, coef e • vecs e)) =
      T.toMultilinearMap (Function.update
        (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (∑ e : Fin n, coef e • vecs e)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show T.toMultilinearMap (Function.update
        (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4 (coef e • vecs e)) =
      T (Function.update (vec5 (I := I) A B C D (0 : TangentSpace I x)) 4
        (coef e • vecs e)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]

/-- Multilinearity of a `(0,4)` tensor `T` in its **last** slot, `vec4`-shaped. -/
theorem tensor04_vec4_sum_last'
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (A B C : TangentSpace I x)
    (coef : Fin n → Real) (vecs : Fin n → TangentSpace I x) :
    T (vec4 (I := I) A B C (∑ e : Fin n, coef e • vecs e)) =
      ∑ e : Fin n, coef e * T (vec4 (I := I) A B C (vecs e)) := by
  classical
  have hupd : ∀ Z : TangentSpace I x,
      vec4 (I := I) A B C Z =
        Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 Z := by
    intro Z; funext i; fin_cases i <;> simp [vec4, Function.update]
  rw [hupd]
  rw [show T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Fin n, coef e • vecs e)) =
      T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Fin n, coef e • vecs e)) from rfl]
  rw [T.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show T.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 (coef e • vecs e)) =
      T (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (coef e • vecs e)) from rfl]
  rw [T.map_update_smul, ← hupd]
  simp [smul_eq_mul]

/-- **Cauchy–Schwarz on a last-slot raise contraction (rank-5 tensor).**  For a
`g`-orthonormal basis, a `(0,5)` tensor `T`, fixed slots `A,B,C,D`, and a one-form
`β`, the contraction `T(A,B,C,D, g♯β)` is bounded by

`|T(A,B,C,D, g♯β)| ≤ card · √(∑_e T(A,B,C,D,e_e)²) · √(∑_e (β e_e)²)`.

(Last-slot multilinearity + the orthonormal `g♯` expansion + Cauchy–Schwarz.) -/
theorem abs_tensor05_sharp_last_le
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (A B C D : TangentSpace I x)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    |T (vec5 (I := I) A B C D (cotangentSharp_gen (I := I) g x β))| ≤
      (Fintype.card (Fin n) : Real) *
        (Real.sqrt (∑ e : Fin n, (T (vec5 (I := I) A B C D (basis e))) ^ 2) *
          Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2)) := by
  classical
  set NT : Real := Real.sqrt (∑ e : Fin n, (T (vec5 (I := I) A B C D (basis e))) ^ 2)
    with hNT
  set Nβ : Real := Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2) with hNβ
  have hNTnn : 0 ≤ NT := Real.sqrt_nonneg _
  have hNβnn : 0 ≤ Nβ := Real.sqrt_nonneg _
  rw [cotangentSharp_orthoBasis_expand' (I := I) g basis horth β]
  rw [tensor05_vec5_sum_last (I := I) T A B C D]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin n => NT * Nβ) ?_) ?_
  · intro e _
    rw [abs_mul, mul_comm]
    have hTbnd : |T (vec5 (I := I) A B C D (basis e))| ≤ NT := by
      rw [hNT, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (T (vec5 (I := I) A B C D (basis e'))) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    have hβbnd : |β (fun _ : Fin 1 => basis e)| ≤ Nβ := by
      rw [hNβ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (β (fun _ : Fin 1 => basis e')) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    exact mul_le_mul hTbnd hβbnd (abs_nonneg _) hNTnn
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Cauchy–Schwarz on a last-slot raise contraction (rank-4 tensor).**  The
rank-4 analogue of `abs_tensor05_sharp_last_le`. -/
theorem abs_tensor04_sharp_last_le
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (A B C : TangentSpace I x)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    |T (vec4 (I := I) A B C (cotangentSharp_gen (I := I) g x β))| ≤
      (Fintype.card (Fin n) : Real) *
        (Real.sqrt (∑ e : Fin n, (T (vec4 (I := I) A B C (basis e))) ^ 2) *
          Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2)) := by
  classical
  set NT : Real := Real.sqrt (∑ e : Fin n, (T (vec4 (I := I) A B C (basis e))) ^ 2)
    with hNT
  set Nβ : Real := Real.sqrt (∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) ^ 2) with hNβ
  have hNTnn : 0 ≤ NT := Real.sqrt_nonneg _
  have hNβnn : 0 ≤ Nβ := Real.sqrt_nonneg _
  rw [cotangentSharp_orthoBasis_expand' (I := I) g basis horth β]
  rw [tensor04_vec4_sum_last' (I := I) T A B C]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ : Fin n => NT * Nβ) ?_) ?_
  · intro e _
    rw [abs_mul, mul_comm]
    have hTbnd : |T (vec4 (I := I) A B C (basis e))| ≤ NT := by
      rw [hNT, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (T (vec4 (I := I) A B C (basis e'))) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    have hβbnd : |β (fun _ : Fin 1 => basis e)| ≤ Nβ := by
      rw [hNβ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum
          (f := fun e' : Fin n => (β (fun _ : Fin 1 => basis e')) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ e))
    exact mul_le_mul hTbnd hβbnd (abs_nonneg _) hNTnn
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Slot-uniform partial-sum domination.**  For a `(0, r)` tensor `T`, a multi-index
`idx`, and a slot `q`, summing the squared component over the `q`-th slot is dominated
by the full `compNormSqMulti` (the map `e ↦ update idx q e` is injective, so the partial
sum is a sub-sum of all multi-index components). -/
theorem sum_sq_update_le_compNormSqMulti {r : ℕ}
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (idx : Fin r → Fin n) (q : Fin r) :
    (∑ e : Fin n,
        (T (fun p : Fin r => basis (Function.update idx q e p))) ^ 2) ≤
      compNormSqMulti (fun jdx : Fin r → Fin n => T (fun p => basis (jdx p))) := by
  classical
  set F : Fin n → (Fin r → Fin n) := fun e => Function.update idx q e with hF
  set P : (Fin r → Fin n) → Real :=
    fun jdx => (T (fun p => basis (jdx p))) ^ 2 with hP
  have hinj : Set.InjOn F (Finset.univ : Finset (Fin n)) := by
    intro e₁ _ e₂ _ heq
    have := congrFun heq q
    simpa [hF, Function.update_self] using this
  have himg : (∑ e : Fin n, P (F e)) = ∑ jdx ∈ Finset.univ.image F, P jdx :=
    (Finset.sum_image (fun e _ e' _ h => hinj (Finset.mem_univ e) (Finset.mem_univ e') h)).symm
  have hlhs : (∑ e : Fin n,
        (T (fun p : Fin r => basis (Function.update idx q e p))) ^ 2) =
      ∑ e : Fin n, P (F e) := rfl
  rw [hlhs, himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => sq_nonneg _)

end T1Bound

/-! ## The solution-facing `T₁` bound

We instantiate the K-Leibniz and the abstract Cauchy–Schwarz bounds at the solution
in a genuine `g`-orthonormal basis (`exists_orthoBasisFrameAt`), realizing the basis
vectors as covariantly-constant sections (`exists_cov_zero_at_apply`). -/

section SolutionT1Bound

variable {n : ℕ}

/-- The `q`-th frozen one-form of `Rm04` on a basis vector is a plain `Rm04`
component (slot `q` carries the basis vector). -/
theorem rmFrozenSlot_basis_component
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (e : TangentSpace I x₀) :
    rmFrozenSlotField (I := I) S t q Vm x₀ (fun _ : Fin 1 => e) =
      S.base.rm04 t x₀ (Function.update (fun i : Fin 4 => Vm i x₀) q e) :=
  rmFrozenSlotField_apply_vec (I := I) S t q Vm x₀ e

open TensorLieDeriv in
/-- **The `T₁` summand quantitative bound on covariantly-constant sections.**

At `x₀`, for a Ricci-flow solution at a regular time, in a `g`-orthonormal basis
realised by sections `X, Vb, Vc, Vm` covariantly constant at `x₀` (with values the
basis vectors), the `T₁` summand `∇³Rm(X,Vb,Vc,Vm) − ∇³Rm(X,Vc,Vb,Vm)` is bounded by

`|T₁| ≤ 8 · card · √(compNormSqMulti of basis ∇Rm) · √(compNormSqMulti of basis Rm)`,

i.e. `|T₁| ≤ C(card)·|∇Rm|·|Rm|`, via the K-Leibniz and the orthonormal Cauchy–Schwarz
on the two `Rm04 ∗ ∇Rm04` raise contractions. -/
theorem abs_nablaLapComm_T1_covConst_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vb Vc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Vm : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (a b c : Fin n) (m : Fin 4 → Fin n)
    (hXa : X x₀ = basis a) (hVb : Vb x₀ = basis b) (hVc : Vc x₀ = basis c)
    (hVm : ∀ i : Fin 4, Vm i x₀ = basis (m i))
    (hXcov : ((S.family.connection (t : Real) (fun p : M => X p) x₀) (X x₀)) = 0)
    (hVbcov : ((S.family.connection (t : Real) (fun p : M => Vb p) x₀) (X x₀)) = 0)
    (hVccov : ((S.family.connection (t : Real) (fun p : M => Vc p) x₀) (X x₀)) = 0)
    (hVmcov : ∀ i : Fin 4,
      ((S.family.connection (t : Real) (fun p : M => Vm i p) x₀) (X x₀)) = 0) :
    |nabla3Rm04Field (I := I) S (t : Real) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀))) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (Fin.cons (X x₀)
            (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀)))| ≤
      (8 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
            S.base.rm04 (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  set g := S.base.metric (t : Real) with hg_def
  set Nnab : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) with hNnab
  set NRm : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
      S.base.rm04 (t : Real) x₀ (fun p => basis (idx p)))) with hNRm
  have hNnabnn : 0 ≤ Nnab := Real.sqrt_nonneg _
  have hNRmnn : 0 ≤ NRm := Real.sqrt_nonneg _
  have hcardnn : (0 : Real) ≤ (Fintype.card (Fin n) : Real) := by positivity
  -- The K-Leibniz: `T₁ = -Σ_q (T₁a_q + T₁b_q)`.
  rw [nablaLapComm_T1_eq_rm04_raise_leibniz (I := I) S hS t x₀ X Vb Vc Vm
    hVbcov hVccov hVmcov]
  rw [abs_neg]
  -- Triangle inequality over the `q`-sum and the two summand types.
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  -- Per-`q`: `|T₁a_q + T₁b_q| ≤ |T₁a_q| + |T₁b_q| ≤ 2·card·Nnab·NRm`.
  have hper : ∀ q : Fin 4,
      |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀))) +
          S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))| ≤
        (2 : Real) * (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by
    intro q
    refine le_trans (abs_add_le _ _) ?_
    -- Bound `T₁a_q`.
    have hT1a :
        |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)))| ≤
          (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by
      have hCS := abs_tensor05_sharp_last_le (I := I) g basis horth
        (nablaRm04Field (I := I) S (t : Real) x₀)
        (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
        (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)
      refine le_trans hCS ?_
      -- Factor 1: `√(Σ_e ∇Rm04(vec5 a b c m_q e)²) ≤ Nnab`.
      have hf1 :
          Real.sqrt (∑ e : Fin n,
              (nablaRm04Field (I := I) S (t : Real) x₀
                (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀) (basis e))) ^ 2) ≤ Nnab := by
        rw [hNnab]
        refine Real.sqrt_le_sqrt ?_
        rw [hXa, hVb, hVc, hVm q]
        have hidx : ∀ e : Fin n,
            vec5 (I := I) (basis a) (basis b) (basis c) (basis (m q)) (basis e) =
              fun p : Fin 5 => basis ((Function.update ![a, b, c, m q, a] 4 e) p) := by
          intro e; funext p; fin_cases p <;> simp [vec5, Function.update]
        simp only [hidx]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (nablaRm04Field (I := I) S (t : Real) x₀) basis ![a, b, c, m q, a] 4
      -- Factor 2: `√(Σ_e βq(e)²) ≤ NRm`.
      have hf2 :
          Real.sqrt (∑ e : Fin n,
              (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀
                (fun _ : Fin 1 => basis e)) ^ 2) ≤ NRm := by
        rw [hNRm]
        refine Real.sqrt_le_sqrt ?_
        have hβ : ∀ e : Fin n,
            (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀
                (fun _ : Fin 1 => basis e)) ^ 2 =
              (S.base.rm04 (t : Real) x₀
                (fun p : Fin 4 => basis ((Function.update m q e) p))) ^ 2 := by
          intro e
          rw [rmFrozenSlot_basis_component (I := I) S (t : Real) q Vm x₀ (basis e)]
          congr 2
          funext p
          by_cases hp : p = q
          · subst hp; simp [Function.update]
          · simp [Function.update, hp, hVm p]
        rw [Finset.sum_congr rfl (fun e _ => hβ e)]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (S.base.rm04 (t : Real) x₀) basis m q
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hf1 hf2 (Real.sqrt_nonneg _) hNnabnn) hcardnn
    -- Bound `T₁b_q`.
    have hT1b :
        |S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))| ≤
          (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by
      have hCS := abs_tensor04_sharp_last_le (I := I) g basis horth
        (S.base.rm04 (t : Real) x₀)
        (Vb x₀) (Vc x₀) (Vm q x₀)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
          (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))
      refine le_trans hCS ?_
      -- Factor 1: `√(Σ_e Rm04(vec4 b c m_q e)²) ≤ NRm`.
      have hf1 :
          Real.sqrt (∑ e : Fin n,
              (S.base.rm04 (t : Real) x₀
                (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀) (basis e))) ^ 2) ≤ NRm := by
        rw [hNRm]
        refine Real.sqrt_le_sqrt ?_
        rw [hVb, hVc, hVm q]
        have hidx : ∀ e : Fin n,
            vec4 (I := I) (basis b) (basis c) (basis (m q)) (basis e) =
              fun p : Fin 4 => basis ((Function.update ![b, c, m q, b] 3 e) p) := by
          intro e; funext p; fin_cases p <;> simp [vec4, Function.update]
        simp only [hidx]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (S.base.rm04 (t : Real) x₀) basis ![b, c, m q, b] 3
      -- Factor 2: `√(Σ_e (∇βq)(e)²) ≤ Nnab`, via `nablaRmFrozenSlot_eval`.
      have hf2 :
          Real.sqrt (∑ e : Fin n,
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)
                (fun _ : Fin 1 => basis e)) ^ 2) ≤ Nnab := by
        -- Each summand: `(∇βq e)² = (∇Rm04 (basis∘update(cons a m) q.succ e))²`.
        have hcomb : ∀ e : Fin n,
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀)
                (fun _ : Fin 1 => basis e)) ^ 2 =
              (nablaRm04Field (I := I) S (t : Real) x₀
                (fun p : Fin 5 =>
                  basis ((Function.update (Fin.cons a m : Fin 5 → Fin n) q.succ e) p))) ^ 2 := by
          intro e
          rw [tensor0S_curry_apply_cons]
          have hcons2 :
              (Fin.cons (X x₀) (fun _ : Fin 1 => basis e) : Fin 2 → TangentSpace I x₀) =
                vec2 (I := I) (X x₀) (basis e) := by
            funext p; fin_cases p <;> rfl
          rw [hcons2, nablaRmFrozenSlot_eval (I := I) S hS t q X Vm x₀
            (fun i _ => hVmcov i) (basis e)]
          have htuple :
              (Fin.cons (X x₀)
                  (Function.update (fun i : Fin 4 => Vm i x₀) q (basis e)) :
                    Fin 5 → TangentSpace I x₀) =
                fun p : Fin 5 =>
                  basis ((Function.update (Fin.cons a m : Fin 5 → Fin n) q.succ e) p) := by
            funext p
            refine Fin.cases ?_ (fun j => ?_) p
            · simp only [Fin.cons_zero]
              rw [Function.update_of_ne (Fin.succ_ne_zero q).symm, Fin.cons_zero, hXa]
            · simp only [Fin.cons_succ]
              by_cases hj : j = q
              · subst hj; rw [Function.update_self, Function.update_self]
              · rw [Function.update_of_ne hj,
                  Function.update_of_ne (fun h => hj (Fin.succ_injective _ h)),
                  Fin.cons_succ, hVm j]
          rw [htuple]
        rw [hNnab]
        refine Real.sqrt_le_sqrt ?_
        rw [Finset.sum_congr rfl (fun e (_ : e ∈ (Finset.univ : Finset (Fin n))) => hcomb e)]
        exact sum_sq_update_le_compNormSqMulti (I := I)
          (nablaRm04Field (I := I) S (t : Real) x₀) basis (Fin.cons a m) q.succ
      -- Combine: `card·(√·√) ≤ card·(NRm·Nnab) = card·(Nnab·NRm)`.
      refine le_trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hf1 hf2 (Real.sqrt_nonneg _) hNRmnn) hcardnn) ?_
      rw [mul_comm NRm Nnab]
    calc
      |nablaRm04Field (I := I) S (t : Real) x₀
            (vec5 (I := I) (X x₀) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (rmFrozenSlotField (I := I) S (t : Real) q Vm x₀)))| +
          |S.base.rm04 (t : Real) x₀
            (vec4 (I := I) (Vb x₀) (Vc x₀) (Vm q x₀)
              (cotangentSharp_gen (I := I) g x₀
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x₀
                  (nablaRmFrozenSlotField (I := I) S (t : Real) q Vm x₀) (X x₀))))|
          ≤ (Fintype.card (Fin n) : Real) * (Nnab * NRm) +
              (Fintype.card (Fin n) : Real) * (Nnab * NRm) := add_le_add hT1a hT1b
      _ = (2 : Real) * (Fintype.card (Fin n) : Real) * (Nnab * NRm) := by ring
  refine le_trans (Finset.sum_le_sum fun q _ => hper q) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

open TensorLieDeriv in
/-- **The `T₁` summand quantitative bound in the genuine orthonormal frame.**

At `x₀`, for a Ricci-flow solution at a regular time, in the `g`-orthonormal frame of
`exists_orthoBasisFrameAt`, the `T₁` summand of `nablaLapCommReactionTermF` is bounded
by `8·card·√(compNormSqMulti ∇Rm)·√(compNormSqMulti Rm)`.  The frame vectors are
realised by covariantly-constant sections (`exists_cov_zero_at_apply`); the `∇³Rm`
antisymmetrization is a tensor value at `x₀`, so its value on the (constant) frame
vectors equals its value on the cov-constant realisations. -/
theorem abs_nablaLapComm_T1_orthoBasis_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) (m : Fin 4 → Fin n) :
    |nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTupleF (I := I) frame x₀ a b c m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTupleF (I := I) frame x₀ a c b m)| ≤
      (8 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 4 → Fin n =>
            S.base.rm04 (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  have hconn := connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  -- Realise each basis vector by a covariantly-constant section at `x₀`.
  obtain ⟨Xa, hXa, hXacov⟩ := exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis a)
  obtain ⟨Vb, hVb, hVbcov⟩ := exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis b)
  obtain ⟨Vc, hVc, hVccov⟩ := exists_cov_zero_at_apply (I := I)
    (S.family.connection (t : Real)) hconn x₀ (basis c)
  -- The four `Rm`-slot sections.
  choose Vm hVm hVmcov using fun i : Fin 4 =>
    exists_cov_zero_at_apply (I := I)
      (S.family.connection (t : Real)) hconn x₀ (basis (m i))
  -- The frame-tuple values at `x₀` coincide with the cov-constant section values.
  -- The frame-tuple values at `x₀` coincide with the cov-constant section values.
  have hmtail : frameTuple (I := I) frame x₀ m = (fun i : Fin 4 => Vm i x₀) := by
    funext i
    show frame (m i) x₀ = Vm i x₀
    rw [hframe (m i), hVm i]
  have htuple_a :
      nabla3FrameTupleF (I := I) frame x₀ a b c m =
        Fin.cons (Xa x₀)
          (metricTraceInput (I := I) (Vb x₀) (Vc x₀) (fun i : Fin 4 => Vm i x₀)) := by
    simp only [nabla3FrameTupleF, nabla3InnerSlotsF, metricTraceInput]
    rw [hframe a, hframe b, hframe c, hXa, hVb, hVc, hmtail]
    rfl
  have htuple_acb :
      nabla3FrameTupleF (I := I) frame x₀ a c b m =
        Fin.cons (Xa x₀)
          (metricTraceInput (I := I) (Vc x₀) (Vb x₀) (fun i : Fin 4 => Vm i x₀)) := by
    simp only [nabla3FrameTupleF, nabla3InnerSlotsF, metricTraceInput]
    rw [hframe a, hframe c, hframe b, hXa, hVc, hVb, hmtail]
    rfl
  rw [htuple_a, htuple_acb]
  exact abs_nablaLapComm_T1_covConst_le (I := I) S hS t x₀ basis horth Xa Vb Vc Vm
    a b c m hXa hVb hVc hVm
    (hXacov Xa) (hVbcov Xa) (hVccov Xa) (fun i => hVmcov i Xa)

end SolutionT1Bound

/-! ## The full `k = 1` reaction bound and the producer connection

Combining the `T₁` bound (`abs_nablaLapComm_T1_orthoBasis_le`) with the `T₂` bound
(`abs_nablaLapComm_T2_orthoBasis_le`, `Evolution/NablaRiemannT2Bound.lean`) gives the
full reaction `nablaLapCommReactionTermF = T₁ + T₂` bounded by `C(card)·|Rm|·|∇Rm|`,
which the producer consumes through the diagonal trace of `nablaLapComm_orthoFrame`. -/

section ReactionBound

variable {n : ℕ}

/-- One-step decomposition of a function-space sum over `Fin (k+1) → Idx` (local copy
of the private helper of `Evolution/NablaRiemannT2Bound.lean`). -/
private theorem sum_pi_fin_succ {Idx : Type*} [Fintype Idx] {k : ℕ}
    (f : (Fin (k + 1) → Idx) → Real) :
    (∑ idx : Fin (k + 1) → Idx, f idx) =
      ∑ a : Idx, ∑ rest : Fin k → Idx, f (Fin.cons a rest) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Idx)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

/-- Rank-4 reindexing: `∑_{idx : Fin 4 → Idx} (A idx)² = compNormSq4` of the
basis-component array. -/
theorem compNormSqMulti_eq_compNormSq4_basis
    {x₀ : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x₀)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀)) :
    compNormSqMulti (fun idx : Fin 4 → Fin n => T (fun p => basis (idx p))) =
      compNormSq4 (fun i j k l : Fin n =>
        T (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) := by
  classical
  set A : (Fin 4 → Fin n) → Real := fun idx => T (fun p => basis (idx p)) with hA
  unfold compNormSqMulti compNormSq4
  rw [sum_pi_fin_succ (fun idx => (A idx) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons i idx)) ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons i (Fin.cons j idx))) ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons i (Fin.cons j (Fin.cons k idx)))) ^ 2)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (default : Fin 0 → Fin n)]
  · have htuple :
        (Fin.cons i (Fin.cons j (Fin.cons k
          (Fin.cons l (default : Fin 0 → Fin n)))) : Fin 4 → Fin n) =
          ![i, j, k, l] := by
      funext p; fin_cases p <;> rfl
    show (A (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l (default : Fin 0 → Fin n)))))) ^ 2 = _
    rw [htuple, hA]
    dsimp only
    have hvec : (fun p : Fin 4 => basis ((![i, j, k, l] : Fin 4 → Fin n) p)) =
        vec4 (I := I) (basis i) (basis j) (basis k) (basis l) := by
      funext p; fin_cases p <;> rfl
    rw [hvec]
  · intro y _ hy; exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The single-term `k = 1` reaction bound in a `g`-orthonormal basis.**

At `x₀`, in the orthonormal frame, every reaction term `nablaLapCommReactionTermF
frame a b c m = T₁ + T₂` is bounded by

`|reaction a b c m| ≤ 13·card·√(|Rm|²)·√(|∇Rm|²)`,

i.e. `C(card)·|Rm|·|∇Rm|`.  This is the literal `|T₁ + T₂| ≤ C·|Rm|·|∇Rm|`: the `T₁`
half is `abs_nablaLapComm_T1_orthoBasis_le`, the `T₂` half B's
`abs_nablaLapComm_T2_orthoBasis_le`. -/
theorem abs_nablaLapCommReactionTermF_orthoBasis_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) (m : Fin 4 → Fin n) :
    |nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a b c m| ≤
      (13 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
            S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  have horth' : ∀ i j : Fin n,
      (S.family.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := horth
  rw [nablaLapCommReactionTermF]
  refine le_trans (abs_add_le _ _) ?_
  have hT1 := abs_nablaLapComm_T1_orthoBasis_le (I := I) S hS t x₀ frame basis hframe
    horth a b c m
  rw [compNormSqMulti_eq_compNormSq4_basis (I := I) (S.base.rm04 (t : Real) x₀) basis] at hT1
  have hT2 := abs_nablaLapComm_T2_orthoBasis_le (I := I) S (t : Real) x₀ frame basis
    hframe horth' a b c m
  have hsum := add_le_add hT1 hT2
  refine le_trans hsum (le_of_eq ?_)
  ring

/-- **The full `k = 1` reaction bound in a `g`-orthonormal basis (diagonal trace).**

At `x₀`, for a Ricci-flow solution at a regular time, in the orthonormal frame, the
diagonal-trace reaction `∑_a nablaLapCommReactionTermF frame a a c m` is bounded by

`|∑_a reaction a a c m| ≤ 13·card²·√(|Rm|²)·√(|∇Rm|²)`,

i.e. `C(card)·|Rm|·|∇Rm|`, with `|Rm|² = compNormSq4` of the frame `Rm04` and
`|∇Rm|² = compNormSqMulti` of the frame `∇Rm`.  The constant `13·card²` is `8·card²`
(`T₁`) `+ 5·card²` (`T₂`).  Sums the single-term bound
`abs_nablaLapCommReactionTermF_orthoBasis_le`. -/
theorem abs_nablaLapCommReactionTerm_diag_orthoBasis_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (c : Fin n) (m : Fin 4 → Fin n) :
    |∑ a : Fin n, nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m| ≤
      (13 : Real) * (Fintype.card (Fin n) : Real) ^ 2 *
        (Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
            S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))))) := by
  classical
  set NRm : Real := Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
      S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))))
    with hNRm
  set Nnab : Real := Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))) with hNnab
  -- Per-`a` bound: the single-term reaction bound.
  have hper : ∀ a : Fin n,
      |nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m| ≤
        (13 : Real) * (Fintype.card (Fin n) : Real) * (NRm * Nnab) := by
    intro a
    have h := abs_nablaLapCommReactionTermF_orthoBasis_le (I := I) S hS t x₀
      frame basis hframe horth a a c m
    rw [← hNRm, ← hNnab] at h
    exact h
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun a _ => hper a) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  ring

/-- **The spatial Laplacian–covariant commutator bound for `∇Rm` in a genuine
orthonormal frame.**

At `x₀`, for a Ricci-flow solution at a regular time, there exist a `g`-orthonormal
frame `frame` (centre values a `Module.Basis`) and the Kronecker-delta inverse metric
with `InverseMetricOrthonormalAt` holding **genuinely**, such that the spatial commutator
`[Δ, ∇_c] Rm = Δ(∇Rm)(c) − ∇(ΔRm)(c)` is bounded by

`|Δ(∇Rm)(c) − ∇(ΔRm)(c)| ≤ 13·card²·√(rm04NormSqInFrame)·√(nablaRm04NormSqInFrame)`,

i.e. `C(card)·|Rm|·|∇Rm|`, in the producer's component-norm convention
(`rm04NormSqInFrame`/`nablaRm04NormSqInFrame` of `Evolution/RiemannNorm.lean`).

This assembles the spatial-commutator identity (`nablaLapCommF_orthonormalTrace`,
the diagonal trace of `nablaLapComm_orthoFrame`) with the full reaction bound
`abs_nablaLapCommReactionTerm_diag_orthoBasis_le`, in the genuine orthonormal frame of
`exists_orthoBasisFrameAt`.  Both `T₁` and `T₂` are bounded; `nablaLapCommReactionTerm`
is **fully bounded** by `C(card)·|Rm|·|∇Rm|`.

This is the spatial half of the `k = 1` Bernstein–Bando–Shi producer; the full
`NablaRm04NormHeatEquationOn` additionally needs the **time-derivative** assembly
(`iteratedRmComp_one_hasDerivWithinAt` with `hrm`/`hchr`/`hswap` instantiated from the
solution — `Evolution/NablaRiemannTimeDeriv.lean`), a separate frontier deferred there. -/
theorem abs_spatialCommNablaRm_orthoFrame_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric (t : Real)).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) ∧
      InverseMetricOrthonormalAt (M := M) (Idx := Fin n)
        (deltaInvMetric (M := M)) (t : Real) x₀ ∧
      ∀ (c : Fin n) (m : Fin 4 → Fin n),
        |roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m| ≤
          (13 : Real) * (Fintype.card (Fin n) : Real) ^ 2 *
            (Real.sqrt (rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
                (deltaInvMetric (M := M)) frame (t : Real) x₀) *
              Real.sqrt (nablaRm04NormSqInFrame (M := M)
                (fun s y i j k l p =>
                  nablaRm04Field (I := I) S s y (vec5 (I := I)
                    (frame i y) (frame j y) (frame k y) (frame l y) (frame p y)))
                (deltaInvMetric (M := M)) (t : Real) x₀)) := by
  classical
  obtain ⟨n, frame, basis, hframe, horth⟩ := exists_orthoBasisFrameAt (I := I) S (t : Real) x₀
  refine ⟨n, frame, ?_, deltaInvMetric_orthonormal (M := M) (t : Real) x₀, ?_⟩
  · intro i j; rw [hframe i, hframe j]; exact horth i j
  intro c m
  -- The commutator collapses to the diagonal reaction trace.
  rw [nablaLapCommF_orthonormalTrace (I := I) S hS t x₀ frame
    (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) (fun i j => rfl) c m]
  -- The diagonal reaction trace is bounded by the full reaction bound.
  have hbnd := abs_nablaLapCommReactionTerm_diag_orthoBasis_le (I := I) S hS t x₀
    frame basis hframe horth c m
  -- Convert the basis component norms to the producer's frame component norms.
  have hRm :
      compNormSq4 (fun i j k l : Fin n =>
          S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) =
        rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
          (deltaInvMetric (M := M)) frame (t : Real) x₀ := by
    rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
      (deltaInvMetric (M := M)) frame (t : Real) x₀
      (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
    rw [hframe i, hframe j, hframe k, hframe l]
  have hNab :
      compNormSqMulti (fun idx : Fin 5 → Fin n =>
          nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))) =
        nablaRm04NormSqInFrame (M := M)
          (fun s y i j k l p =>
            nablaRm04Field (I := I) S s y (vec5 (I := I)
              (frame i y) (frame j y) (frame k y) (frame l y) (frame p y)))
          (deltaInvMetric (M := M)) (t : Real) x₀ := by
    rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) _
      (deltaInvMetric (M := M)) (t : Real) x₀
      (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
    rw [compNormSqMulti_eq_compNormSq5
      (fun idx : Fin 5 → Fin n =>
        nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))]
    refine Finset.sum_congr rfl fun mi _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c' _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    dsimp only
    have htup : (fun p : Fin 5 => basis ((![mi, a, b, c', d] : Fin 5 → Fin n) p)) =
        vec5 (I := I) (frame mi x₀) (frame a x₀) (frame b x₀) (frame c' x₀) (frame d x₀) := by
      funext p; fin_cases p <;> simp [vec5, hframe]
    rw [htup]
  rw [hRm, hNab] at hbnd
  exact hbnd

end ReactionBound

end DifferentialGeometry.PDE.RicciFlow
