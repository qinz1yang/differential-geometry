import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Coordinates.MetricCompatibility
import RicciFlower.Coordinates.NablaComponents.Tensor0S
import RicciFlower.Coordinates.NablaComponents.TwoTensor
import RicciFlower.Tensor.RSTensor.NablaOnTensors.HigherOrder
import RicciFlower.VectorBundle.PartialMfderiv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Covariant Tensor Fibers

The metric on `T_x M` induces metrics on all covariant tensor powers.  The
construction is intrinsic on the fiber `Tensor0SSpace s I x`; coordinate
formulas are evaluation theorems for local frames.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MetricFiberData

variable {V W : Type*}

private def realFlatLinear : Real →ₗ[Real] Module.Dual Real Real where
  toFun := fun a =>
    { toFun := fun b => a * b
      map_add' := by
        intro b c
        ring
      map_smul' := by
        intro c b
        simp [smul_eq_mul, mul_left_comm] }
  map_add' := by
    intro a b
    ext
    simp
  map_smul' := by
    intro c a
    ext
    simp [smul_eq_mul]

/-- The standard metric on the real scalar fiber. -/
def real : MetricFiberData Real :=
  MetricFiberData.ofFlat realFlatLinear
    (by
      intro a b h
      have h1 := congrArg (fun φ : Module.Dual Real Real => φ 1) h
      simpa [realFlatLinear] using h1)
    (by
      intro a b
      change a * b = b * a
      ring)
    (by
      intro a
      change 0 <= a * a
      nlinarith [sq_nonneg a])

/-- Pull a metric back along a linear equivalence. -/
def pullback [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (e : V ≃ₗ[Real] W) (D : MetricFiberData W) : MetricFiberData V where
  flat := e.trans (D.flat.trans e.dualMap)
  symm := by
    intro v w
    change D.flat (e v) (e w) = D.flat (e w) (e v)
    exact D.symm (e v) (e w)
  nonneg := by
    intro v
    change 0 <= D.flat (e v) (e v)
    exact D.nonneg (e v)

/-- The Hilbert-Schmidt flat map on a finite-dimensional algebraic Hom fiber.

Expected construction: the flat map sends `A` to the functional
`B ↦ tr(A† ∘ B)`, where `A†` is the metric adjoint built from `DV` and `DW`.
The proof obligation is that this flat map is symmetric and positive
semidefinite, hence gives genuine metric data on `V →ₗ[Real] W`.

We use algebraic Hom here because the metric is fiberwise. Continuous Hom
models are connected to this one by finite-dimensional continuity equivalences
at the tensor-curry boundary. -/
private def homFlatLinear [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    (V →ₗ[Real] W) →ₗ[Real] Module.Dual Real (V →ₗ[Real] W) where
  toFun A :=
    { toFun := fun B =>
        LinearMap.trace Real V
          ((MetricFiberData.adjoint DV DW A).comp B)
      map_add' := by
        intro B C
        simp [LinearMap.comp_add, map_add]
      map_smul' := by
        intro c B
        simp [LinearMap.comp_smul, map_smul] }
  map_add' := by
    intro A B
    ext C
    have hdual :
        (A + B).dualMap = A.dualMap + B.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((A + B).dualMap).comp DW.flat.toLinearMap)).comp C) =
        LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (A.dualMap.comp DW.flat.toLinearMap)).comp C) +
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (B.dualMap.comp DW.flat.toLinearMap)).comp C)
    rw [hdual]
    simp [LinearMap.add_comp, LinearMap.comp_add, map_add]
  map_smul' := by
    intro c A
    ext B
    have hdual :
        (c • A).dualMap = c • A.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((c • A).dualMap).comp DW.flat.toLinearMap)).comp B) =
        c *
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (A.dualMap.comp DW.flat.toLinearMap)).comp B)
    rw [hdual]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, map_smul]

private theorem trace_adjoint_comp_eq_sum_inner
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      ∑ i : Fin (Module.finrank Real V),
        Inner.inner Real (A (stdOrthonormalBasis Real V i))
          (B (stdOrthonormalBasis Real V i)) := by
  rw [LinearMap.trace_eq_matrix_trace Real
    (stdOrthonormalBasis Real V).toBasis ((LinearMap.adjoint A).comp B)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show
      (LinearMap.toMatrix (stdOrthonormalBasis Real V).toBasis
        (stdOrthonormalBasis Real V).toBasis
        ((LinearMap.adjoint A).comp B)) i i =
        (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis Real V)
          ((LinearMap.adjoint A).comp B)) i i from rfl]
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  exact LinearMap.adjoint_inner_right A
    (stdOrthonormalBasis Real V i) (B (stdOrthonormalBasis Real V i))

private theorem trace_adjoint_comp_nonneg
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    0 <= LinearMap.trace Real V ((LinearMap.adjoint A).comp A) := by
  rw [trace_adjoint_comp_eq_sum_inner]
  exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg

private theorem trace_adjoint_comp_eq_zero_iff
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp A) = 0 ↔ A = 0 := by
  constructor
  · intro htrace
    have hsum :
        (∑ i : Fin (Module.finrank Real V),
          Inner.inner Real (A (stdOrthonormalBasis Real V i))
            (A (stdOrthonormalBasis Real V i))) = 0 := by
      simpa [trace_adjoint_comp_eq_sum_inner] using htrace
    have hzero :
        forall i : Fin (Module.finrank Real V),
          A (stdOrthonormalBasis Real V i) = 0 := by
      intro i
      have hi :
          Inner.inner Real (A (stdOrthonormalBasis Real V i))
            (A (stdOrthonormalBasis Real V i)) = 0 := by
        have hs := (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ)
          (f := fun i : Fin (Module.finrank Real V) =>
            Inner.inner Real (A (stdOrthonormalBasis Real V i))
              (A (stdOrthonormalBasis Real V i)))
          (by intro _ _; exact real_inner_self_nonneg)).1 hsum
        exact hs i (Finset.mem_univ i)
      exact (inner_self_eq_zero).1 hi
    apply (stdOrthonormalBasis Real V).toBasis.ext
    intro i
    simpa using hzero i
  · intro hA
    simp [hA]

private theorem trace_adjoint_comp_comm
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A B : V →ₗ[Real] W) :
    LinearMap.trace Real V ((LinearMap.adjoint A).comp B) =
      LinearMap.trace Real V ((LinearMap.adjoint B).comp A) := by
  rw [trace_adjoint_comp_eq_sum_inner, trace_adjoint_comp_eq_sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact (real_inner_comm (A (stdOrthonormalBasis Real V i))
    (B (stdOrthonormalBasis Real V i))).symm

private theorem metric_adjoint_eq_adjoint
    [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) (A : V →ₗ[Real] W) :
    letI : InnerProductSpace.Core Real V := DV.toCore
    letI : NormedAddCommGroup V :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
    letI : InnerProductSpace.Core Real W := DW.toCore
    letI : NormedAddCommGroup W :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
    letI : InnerProductSpace Real W :=
      @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
    MetricFiberData.adjoint DV DW A = LinearMap.adjoint A := by
  letI : InnerProductSpace.Core Real V := DV.toCore
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  letI : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  letI : InnerProductSpace.Core Real W := DW.toCore
  letI : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  letI : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  apply LinearMap.ext
  intro y
  apply ext_inner_right Real
  intro x
  change DV.inner (MetricFiberData.adjoint DV DW A y) x =
    DV.inner (LinearMap.adjoint A y) x
  rw [MetricFiberData.adjoint_inner]
  rw [← DW.toCore_inner y (A x), ← DV.toCore_inner (LinearMap.adjoint A y) x]
  exact (LinearMap.adjoint_inner_left A x y).symm

private theorem homFlatLinear_comm [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A B : V →ₗ[Real] W) :
    homFlatLinear DV DW A B = homFlatLinear DV DW B A := by
  letI : InnerProductSpace.Core Real V := DV.toCore
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  letI : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  letI : InnerProductSpace.Core Real W := DW.toCore
  letI : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  letI : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  have hA := metric_adjoint_eq_adjoint DV DW A
  have hB := metric_adjoint_eq_adjoint DV DW B
  change LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp B) =
    LinearMap.trace Real V ((MetricFiberData.adjoint DV DW B).comp A)
  rw [hA, hB]
  exact trace_adjoint_comp_comm A B

private theorem homFlatLinear_nonneg [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    0 <= homFlatLinear DV DW A A := by
  letI : InnerProductSpace.Core Real V := DV.toCore
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  letI : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  letI : InnerProductSpace.Core Real W := DW.toCore
  letI : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  letI : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  have hA := metric_adjoint_eq_adjoint DV DW A
  change 0 <= LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp A)
  rw [hA]
  exact trace_adjoint_comp_nonneg A

private theorem homFlatLinear_self_eq_zero_iff [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) :
    homFlatLinear DV DW A A = 0 ↔ A = 0 := by
  letI : InnerProductSpace.Core Real V := DV.toCore
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ _ _ DV.toCore
  letI : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  letI : InnerProductSpace.Core Real W := DW.toCore
  letI : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ _ _ DW.toCore
  letI : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  have hA := metric_adjoint_eq_adjoint DV DW A
  change LinearMap.trace Real V ((MetricFiberData.adjoint DV DW A).comp A) = 0 ↔ A = 0
  rw [hA]
  exact trace_adjoint_comp_eq_zero_iff A

private theorem hom_nonneg [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    Function.Injective (homFlatLinear DV DW) ∧
      (forall A B : V →ₗ[Real] W,
        homFlatLinear DV DW A B = homFlatLinear DV DW B A) ∧
      (forall A : V →ₗ[Real] W, 0 <= homFlatLinear DV DW A A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hAB
    have hflat : homFlatLinear DV DW (A - B) = 0 := by
      rw [map_sub, hAB, sub_self]
    have hdiag : homFlatLinear DV DW (A - B) (A - B) = 0 := by
      rw [hflat]
      rfl
    have hzero : A - B = 0 :=
      (homFlatLinear_self_eq_zero_iff DV DW (A - B)).1 hdiag
    exact sub_eq_zero.mp hzero
  · exact homFlatLinear_comm DV DW
  · exact homFlatLinear_nonneg DV DW

def hom [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →ₗ[Real] W) :=
  MetricFiberData.ofFlat (homFlatLinear DV DW)
    (hom_nonneg DV DW).1
    (hom_nonneg DV DW).2.1
    (hom_nonneg DV DW).2.2

/-- The Hilbert-Schmidt metric on continuous Hom fibers, obtained by
transporting the algebraic Hom metric across finite-dimensional automatic
continuity. -/
def homCLM [AddCommGroup V] [Module Real V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul Real V] [T2Space V]
    [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →L[Real] W) :=
  MetricFiberData.pullback
    (LinearMap.toContinuousLinearMap (𝕜 := Real) (E := V) (F' := W)).symm
    (MetricFiberData.hom DV DW)

end MetricFiberData

/-- The scalar metric on `(0,0)` tensor fibers. -/
def scalarMetricData (_g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 0 I x) :=
  MetricFiberData.pullback
    ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x).toLinearEquiv.trans
      (continuousMultilinearCurryFin0 Real (TangentSpace I x) Real).toLinearEquiv)
    MetricFiberData.real

/-- One recursive step for the metric on covariant tensor powers.

Using `tensor0S_curry`, a `(0,s+1)` tensor is a continuous linear map
`T_x M -> Tensor0SSpace s I x`. The metric is the Hilbert-Schmidt metric
on that Hom fiber. -/
def tensor0SMetricStep
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (D : MetricFiberData (Tensor0SSpace s I x)) :
    MetricFiberData (Tensor0SSpace (s + 1) I x) :=
  have hTopAdd0 : IsTopologicalAddGroup (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  letI : IsTopologicalAddGroup (Tensor0SSpace s I x) := hTopAdd0
  have hContAdd0 : ContinuousAdd (Tensor0SSpace s I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  letI : ContinuousAdd (Tensor0SSpace s I x) := hContAdd0
  have hContSMul0 : ContinuousSMul Real (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  letI : ContinuousSMul Real (Tensor0SSpace s I x) := hContSMul0
  letI : ContinuousConstSMul Real (Tensor0SSpace s I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd0
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd0
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd0
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance inferInstance hTopAdd0 hContSMul0
      inferInstance inferInstance inferInstance).finiteDimensional
  MetricFiberData.pullback
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x).toLinearEquiv
    (@MetricFiberData.homCLM
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd0 hContSMul0 inferInstance
      (tangentMetricData (I := I) g x).metric D)

/-- The Riemannian metric on covariant `s`-tensor fibers, constructed
recursively from `g`. -/
def tensor0SMetricData (g : SmoothMetric I M) (x : M) :
    (s : Nat) -> MetricFiberData (Tensor0SSpace s I x)
  | 0 => scalarMetricData (I := I) g x
  | 1 => cotangentMetricData (I := I) g x
  | s + 2 =>
      tensor0SMetricStep (I := I) g x (s + 1) (tensor0SMetricData g x (s + 1))

/-- Metric-induced inner product on covariant tensor fibers. -/
def inner0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) : Real :=
  (tensor0SMetricData (I := I) g x s).inner A B

/-- Metric flat map on covariant tensor fibers. -/
def flat0S
    (g : SmoothMetric I M) (x : M) (s : Nat) :
    Tensor0SSpace s I x ≃ₗ[Real] Module.Dual Real (Tensor0SSpace s I x) :=
  (tensor0SMetricData (I := I) g x s).flat

/-- Squared norm of a covariant tensor. -/
def normSq0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) : Real :=
  inner0S (I := I) g x s A A

@[simp] theorem normSq0S_eq_inner
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A = inner0S (I := I) g x s A A := by
  rfl

/-- The `(0,1)` tensor metric agrees with the cotangent metric. -/
theorem inner0S_one_eq_cotangent
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    inner0S (I := I) g x 1 α β =
      cotangentInner (I := I) g x α β := by
  rfl

/-- Component of a covariant tensor in a pointwise frame. -/
def tensor0SComponent {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) : Real :=
  A (fun a => frame (slots a))

@[simp] theorem tensor0SComponent_apply {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) :
    tensor0SComponent (I := I) A frame slots =
      A (fun a => frame (slots a)) := by
  rfl

/-- Coordinate contraction for the covariant tensor metric. -/
def coordInner0S
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) *
      tensor0SComponent (I := I) A (fun i => basis i) I0 *
        tensor0SComponent (I := I) B (fun i => basis i) J0

private theorem sum_fin_two_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

private theorem sum_fin_succ_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α] (s : Nat)
    (F : (Fin (s + 1) -> Idx) -> α) :
    (∑ I0 : Fin (s + 1) -> Idx, F I0) =
      ∑ i : Idx, ∑ tail : Fin s -> Idx, F (Fin.cons i tail) := by
  classical
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm
    F (fun p : Idx × (Fin s -> Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr 1
    exact (Fin.cons_self_tail I0).symm

private theorem sum_fin_one_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 -> Idx) -> α) :
    (∑ I0 : Fin 1 -> Idx, F I0) =
      ∑ i : Idx, F (fun _ : Fin 1 => i) := by
  classical
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Idx)
    F (fun i : Idx => F (fun _ : Fin 1 => i))]
  intro I0
  congr 1
  funext a
  simpa [Equiv.funUnique] using congrArg I0 (Subsingleton.elim a (0 : Fin 1))

private theorem basis_repr_eq_sum_inv_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Z : TangentSpace I x) (i : Idx) :
    basis.repr Z i =
      ∑ j : Idx, gInv i j * g.inner x Z (basis j) := by
  classical
  let Z' : TangentSpace I x :=
    ∑ i : Idx, (∑ j : Idx, gInv i j * g.inner x Z (basis j)) • basis i
  have hZ : Z = Z' := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro l
    calc
      g.inner x Z (basis l)
          = ∑ j : Idx, (if l = j then 1 else 0) *
              g.inner x Z (basis j) := by
            simp
      _ = ∑ j : Idx,
            (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
              g.inner x Z (basis j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [(hinv l j).2]
      _ = ∑ i : Idx,
            (∑ j : Idx, gInv i j * g.inner x Z (basis j)) *
              g.inner x (basis i) (basis l) := by
            calc
              (∑ j : Idx,
                  (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
                    g.inner x Z (basis j))
                  = ∑ j : Idx, ∑ i : Idx,
                      (g.inner x (basis l) (basis i) * gInv i j) *
                        g.inner x Z (basis j) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
              _ = ∑ i : Idx, ∑ j : Idx,
                      (g.inner x (basis l) (basis i) * gInv i j) *
                        g.inner x Z (basis j) := by
                      rw [Finset.sum_comm]
              _ = ∑ i : Idx,
                    (∑ j : Idx, gInv i j * g.inner x Z (basis j)) *
                      g.inner x (basis i) (basis l) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [g.symm x (basis l) (basis i)]
                      ring
      _ = g.inner x Z' (basis l) := by
            simp [Z', map_sum]
  calc
    basis.repr Z i = basis.repr Z' i := by rw [hZ]
    _ = ∑ j : Idx, gInv i j * g.inner x Z (basis j) := by
      change
        basis.repr
            (∑ i : Idx, (∑ j : Idx, gInv i j * g.inner x Z (basis j)) • basis i) i =
          ∑ j : Idx, gInv i j * g.inner x Z (basis j)
      rw [map_sum]
      rw [show
          (∑ x_1 : Idx,
              basis.repr
                ((∑ j : Idx, gInv x_1 j * g.inner x Z (basis j)) • basis x_1)) i =
          ∑ x_1 : Idx,
              (basis.repr
                ((∑ j : Idx, gInv x_1 j * g.inner x Z (basis j)) • basis x_1)) i by
        simp]
      simp only [map_smul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hi
        simp at hi

/-- Coordinate trace formula for an endomorphism in a basis with inverse metric
components. -/
theorem linearMap_trace_eq_sum_inv_inner_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : TangentSpace I x →ₗ[Real] TangentSpace I x) :
    LinearMap.trace Real (TangentSpace I x) A =
      ∑ i : Idx, ∑ j : Idx, gInv i j * g.inner x (A (basis i)) (basis j) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis A]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  exact basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv (A (basis i)) i

/-- Positivity of the trace of a tangent endomorphism from positivity of its
metric quadratic form. -/
theorem linearMap_trace_nonneg_of_metric_inner_apply_self_nonneg
    (g : SmoothMetric I M) (x : M)
    (A : TangentSpace I x →ₗ[Real] TangentSpace I x)
    (hA : ∀ v : TangentSpace I x, 0 <= g.inner x (A v) v) :
    0 <= LinearMap.trace Real (TangentSpace I x) A := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  rw [LinearMap.trace_eq_sum_inner A
    (stdOrthonormalBasis Real (TangentSpace I x))]
  exact Finset.sum_nonneg fun i _ => by
    have hi := hA (stdOrthonormalBasis Real (TangentSpace I x) i)
    have hinner :
        Inner.inner Real
            (A (stdOrthonormalBasis Real (TangentSpace I x) i))
            (stdOrthonormalBasis Real (TangentSpace I x) i) =
          g.inner x
            (A (stdOrthonormalBasis Real (TangentSpace I x) i))
            (stdOrthonormalBasis Real (TangentSpace I x) i) := by
      change D.inner
          (A (stdOrthonormalBasis Real (TangentSpace I x) i))
          (stdOrthonormalBasis Real (TangentSpace I x) i) =
        g.inner x
          (A (stdOrthonormalBasis Real (TangentSpace I x) i))
          (stdOrthonormalBasis Real (TangentSpace I x) i)
      rfl
    rw [real_inner_comm, hinner]
    exact hi

private theorem hom_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j)) := by
  change LinearMap.trace Real (TangentSpace I x)
      ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A).comp A) =
    ∑ i : Idx, ∑ j : Idx,
      gInv i j * D.inner (A (basis i)) (A (basis j))
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A).comp A)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change
    g.inner x
        ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A)
          (A (basis i)))
        (basis j) =
      D.inner (A (basis i)) (A (basis j))
  rw [← TangentMetricData.inner_eq (I := I)
    (tangentMetricData (I := I) g x)
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A)
      (A (basis i)))
    (basis j)]
  exact MetricFiberData.adjoint_inner
    (tangentMetricData (I := I) g x).metric D A (A (basis i)) (basis j)

private theorem hom_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j)) := by
  rw [MetricFiberData.homFlatLinear_comm
    (tangentMetricData (I := I) g x).metric D A B]
  change LinearMap.trace Real (TangentSpace I x)
      ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B).comp A) =
    ∑ i : Idx, ∑ j : Idx,
      gInv i j * D.inner (A (basis i)) (B (basis j))
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B).comp A)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change
    g.inner x
        ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B)
          (A (basis i)))
        (basis j) =
      D.inner (A (basis i)) (B (basis j))
  rw [← TangentMetricData.inner_eq (I := I)
    (tangentMetricData (I := I) g x)
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B)
      (A (basis i)))
    (basis j)]
  exact MetricFiberData.adjoint_inner
    (tangentMetricData (I := I) g x).metric D B (A (basis i)) (basis j)

private theorem homCLM_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j)) := by
  exact hom_normSq_eq_basis (I := I) g x basis gInv hinv D A.toLinearMap

private theorem homCLM_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j)) := by
  exact hom_inner_eq_basis (I := I) g x basis gInv hinv D A.toLinearMap B.toLinearMap

private theorem tensor0S_curry_one_apply
    {x : M} (A : Tensor0SSpace 2 I x)
    (X Y : TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A X)
        (fun _ : Fin 1 => Y) =
      A (fun a : Fin 2 => if a = 0 then X else Y) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (1 + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
        X)
        (fun _ : Fin 1 => Y)) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
        (fun a : Fin 2 => if a = 0 then X else Y)
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  funext a
  fin_cases a <;> simp [Fin.cons_zero]

private theorem tensor0S_curry_apply_cons
    {x : M} (s : Nat) (A : Tensor0SSpace (s + 1) I x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (s + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        X)
        tail) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        (Fin.cons X tail)
  rw [continuousMultilinearCurryLeftEquiv_apply]

/-- Direct coordinate squared-norm formula for `(0,2)` covariant tensors.

This is the checked bridge used by the Bochner layer while the fully general
`inner0S_eq_coord` induction remains open. -/
theorem normSq0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 2 A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  classical
  have hTopAdd1 : IsTopologicalAddGroup (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : IsTopologicalAddGroup (Tensor0SSpace 1 I x) := hTopAdd1
  have hContSMul1 : ContinuousSMul Real (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : ContinuousSMul Real (Tensor0SSpace 1 I x) := hContSMul1
  have hContAdd1 : ContinuousAdd (Tensor0SSpace 1 I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace 1 I x) := hContAdd1
  haveI : ContinuousConstSMul Real (Tensor0SSpace 1 I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace 1 I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd1
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd1
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd1
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance inferInstance hTopAdd1 hContSMul1
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold normSq0S inner0S MetricFiberData.inner
  change
    (tensor0SMetricStep (I := I) g x 1 (cotangentMetricData (I := I) g x)).flat A A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)
  unfold tensor0SMetricStep MetricFiberData.pullback MetricFiberData.homCLM
    MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric
      (cotangentMetricData (I := I) g x)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)
  rw [hom_normSq_eq_basis (I := I) g x basis gInv hinv
    (cotangentMetricData (I := I) g x)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)]
  calc
    (∑ i : Idx, ∑ k : Idx,
        gInv i k *
          (cotangentMetricData (I := I) g x).inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis k)))
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
            gInv i k *
              (gInv j l *
                A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
                  A (fun a : Fin 2 => if a = 0 then basis k else basis l)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [cotangentMetricData_inner_eq_coord (I := I) g x basis gInv hinv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [cotangentToDual_apply, cotangentToDual_apply]
          rw [tensor0S_curry_one_apply, tensor0S_curry_one_apply]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring

/-- Direct coordinate inner-product formula for `(0,2)` covariant tensors.

This is the bilinear analogue of `normSq0S_two_eq_coord`; it avoids the
currently open general tensor-power coordinate theorem. -/
theorem inner0S_two_eq_coord_direct
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  classical
  have hTopAdd1 : IsTopologicalAddGroup (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : IsTopologicalAddGroup (Tensor0SSpace 1 I x) := hTopAdd1
  have hContSMul1 : ContinuousSMul Real (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : ContinuousSMul Real (Tensor0SSpace 1 I x) := hContSMul1
  have hContAdd1 : ContinuousAdd (Tensor0SSpace 1 I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace 1 I x) := hContAdd1
  haveI : ContinuousConstSMul Real (Tensor0SSpace 1 I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace 1 I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd1
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd1
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd1
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance inferInstance hTopAdd1 hContSMul1
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold inner0S MetricFiberData.inner
  change
    (tensor0SMetricStep (I := I) g x 1 (cotangentMetricData (I := I) g x)).flat A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)
  unfold tensor0SMetricStep MetricFiberData.pullback MetricFiberData.homCLM
    MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric
      (cotangentMetricData (I := I) g x)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)
  rw [hom_inner_eq_basis (I := I) g x basis gInv hinv
    (cotangentMetricData (I := I) g x)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B).toLinearMap)]
  calc
    (∑ i : Idx, ∑ k : Idx,
        gInv i k *
          (cotangentMetricData (I := I) g x).inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B) (basis k)))
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
            gInv i k *
              (gInv j l *
                A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
                  B (fun a : Fin 2 => if a = 0 then basis k else basis l)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [cotangentMetricData_inner_eq_coord (I := I) g x basis gInv hinv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [cotangentToDual_apply, cotangentToDual_apply]
          rw [tensor0S_curry_one_apply, tensor0S_curry_one_apply]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring

private theorem inner0S_zero_eq
    (g : SmoothMetric I M) (x : M)
    (A B : Tensor0SSpace 0 I x) :
    inner0S (I := I) g x 0 A B = A Fin.elim0 * B Fin.elim0 := by
  unfold inner0S tensor0SMetricData scalarMetricData MetricFiberData.inner
    MetricFiberData.pullback MetricFiberData.real MetricFiberData.ofFlat
    MetricFiberData.realFlatLinear
  change
    ((continuousMultilinearCurryFin0 Real (TangentSpace I x) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x) A)) *
      ((continuousMultilinearCurryFin0 Real (TangentSpace I x) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x) B)) =
      A Fin.elim0 * B Fin.elim0
  simp [tensor0SSpace_continuousLinearEquiv]
  congr

private theorem coordInner0S_zero_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace 0 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 0 gInv A B basis =
      A Fin.elim0 * B Fin.elim0 := by
  classical
  unfold coordInner0S tensor0SComponent
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton]
  congr <;> funext a <;> exact Fin.elim0 a

private theorem coordInner0S_one_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (α β : Tensor0SSpace 1 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 1 gInv α β basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro j _
  simp [cotangentToDual_apply]

private theorem tensor0SMetricStep_inner_eq_coordStep
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData (Tensor0SSpace s I x))
    (A B : Tensor0SSpace (s + 1) I x) :
    (tensor0SMetricStep (I := I) g x s D).inner A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j)) := by
  classical
  have hTopAdd0 : IsTopologicalAddGroup (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  haveI : IsTopologicalAddGroup (Tensor0SSpace s I x) := hTopAdd0
  have hContSMul0 : ContinuousSMul Real (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  haveI : ContinuousSMul Real (Tensor0SSpace s I x) := hContSMul0
  have hContAdd0 : ContinuousAdd (Tensor0SSpace s I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace s I x) := hContAdd0
  haveI : ContinuousConstSMul Real (Tensor0SSpace s I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd0
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd0
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd0
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance inferInstance hTopAdd0 hContSMul0
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold MetricFiberData.inner tensor0SMetricStep MetricFiberData.pullback
    MetricFiberData.homCLM MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric D
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
  rw [hom_inner_eq_basis (I := I) g x basis gInv hinv D
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A).toLinearMap)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B).toLinearMap)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rfl

private theorem coordInner0S_succ_summand_eq
    {Idx : Type*}  {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) (tailI tailJ : Fin s -> Idx) :
    ((∏ a : Fin (s + 1),
        gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
          (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
        A (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
      B (fun a : Fin (s + 1) =>
        basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
      (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
          ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            (fun a : Fin s => basis (tailI a))) *
        ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
          (fun a : Fin s => basis (tailJ a)) := by
  rw [Fin.prod_univ_succ]
  rw [tensor0S_curry_apply_cons, tensor0S_curry_apply_cons]
  have hA :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))) =
        Fin.cons (basis i) (fun a : Fin s => basis (tailI a)) := by
    funext a
    cases a using Fin.cases <;> simp
  have hB :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
        Fin.cons (basis j) (fun a : Fin s => basis (tailJ a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hA, hB]
  simp [Fin.cons_zero, Fin.cons_succ]

private theorem coordInner0S_succ_eq
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) (s + 1) gInv A B basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordInner0S (I := I) (x := x) s gInv
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
            basis := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_succ_fun s]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ tailI : Fin s -> Idx,
        ∑ J0 : Fin (s + 1) -> Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)) (J0 a)) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
            B (fun a : Fin (s + 1) => basis (J0 a)))
        =
        ∑ tailI : Fin s -> Idx, ∑ j : Idx, ∑ tailJ : Fin s -> Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
                (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
            B (fun a : Fin (s + 1) =>
              basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) := by
          apply Finset.sum_congr rfl
          intro tailI _
          rw [sum_fin_succ_fun s]
    _ =
        ∑ tailI : Fin s -> Idx, ∑ j : Idx, ∑ tailJ : Fin s -> Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro tailI _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro tailJ _
          exact coordInner0S_succ_summand_eq (I := I) s gInv A B basis i j tailI tailJ
    _ =
        ∑ j : Idx, ∑ tailI : Fin s -> Idx, ∑ tailJ : Fin s -> Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ j : Idx,
          gInv i j *
            ∑ tailI : Fin s -> Idx, ∑ tailJ : Fin s -> Idx,
              (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
                ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                  (fun a : Fin s => basis (tailI a)) *
                  ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
                    (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailI _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailJ _
          ring

/-- Coordinate formula for the covariant tensor metric in a basis.

This is the general tensor-power contraction theorem. The `s = 1` theorem is
proved in `CotangentRiemannian`; the `s = 2` form used by Bochner is exposed
below. The remaining proof is finite-dimensional tensor-basis induction. -/
theorem inner0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      coordInner0S (I := I) (x := x) s gInv A B basis := by
  induction s with
  | zero =>
      rw [inner0S_zero_eq (I := I) g x A B,
        coordInner0S_zero_eq (I := I) gInv A B basis]
  | succ s ih =>
      cases s with
      | zero =>
          rw [inner0S_one_eq_cotangent (I := I) g x A B,
            cotangentInner_eq_coord (I := I) g x basis gInv hinv A B,
            coordInner0S_one_eq (I := I) gInv A B basis]
      | succ s =>
          rw [coordInner0S_succ_eq (I := I) (s + 1) gInv A B basis]
          unfold inner0S
          change
            (tensor0SMetricStep (I := I) g x (s + 1)
              (tensor0SMetricData (I := I) g x (s + 1))).inner A B =
              ∑ i : Idx, ∑ j : Idx,
                gInv i j *
                  coordInner0S (I := I) (x := x) (s + 1) gInv
                    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                      (basis i))
                    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                      (basis j))
                    basis
          rw [tensor0SMetricStep_inner_eq_coordStep (I := I) g x (s + 1)
            basis gInv hinv (tensor0SMetricData (I := I) g x (s + 1)) A B]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change
            gInv i j *
                inner0S (I := I) g x (s + 1)
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                    (basis i)))
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                    (basis j))) =
              gInv i j *
                coordInner0S (I := I) (x := x) (s + 1) gInv
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                    (basis i)))
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                    (basis j)))
                  basis
          rw [ih]

/-- Coordinate formula for the covariant tensor squared norm. -/
theorem normSq0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      coordInner0S (I := I) (x := x) s gInv A A basis := by
  rw [normSq0S_eq_inner, inner0S_eq_coord (I := I) g x s basis gInv hinv]

/-- The `(0,2)` coordinate formula in the nested-index form used by Ricci
calculations. -/
theorem inner0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  exact inner0S_two_eq_coord_direct (I := I) g x basis gInv hinv A B

private theorem sum5_swap_first_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F a j k l i) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.2 x.1.1.1.2 x.1.1.2 x.1.2 x.1.1.1.1) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.2, p.1.1.1.2), p.1.1.2), p.1.2), p.1.1.1.1)
            invFun := fun p => ((((p.2, p.1.1.1.2), p.1.1.2), p.1.2), p.1.1.1.1)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.2 p.1.1.1.2 p.1.1.2 p.1.2 p.1.1.1.1)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

private theorem sum5_swap_second_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i a k l j) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.2 x.1.1.2 x.1.2 x.1.1.1.2) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.1.1.1.1, p.2), p.1.1.2), p.1.2), p.1.1.1.2)
            invFun := fun p => ((((p.1.1.1.1, p.2), p.1.1.2), p.1.2), p.1.1.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.1.1.1.1 p.2 p.1.1.2 p.1.2 p.1.1.1.2)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

private theorem sum5_swap_third_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j a l k) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.2 x.1.2 x.1.1.2) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.2), p.1.2), p.1.1.2)
            invFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.2), p.1.2), p.1.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.2 p.1.2 p.1.1.2)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

private theorem sum5_swap_fourth_last
    {Idx : Type*} [Fintype Idx]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k l a) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, F i j k a l) := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2) =
      (∑ x : ((((Idx × Idx) × Idx) × Idx) × Idx),
        F x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.2 x.1.2) by
        let e : ((((Idx × Idx) × Idx) × Idx) × Idx) ≃
            ((((Idx × Idx) × Idx) × Idx) × Idx) :=
          { toFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.2), p.1.2)
            invFun := fun p => ((((p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.2), p.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨⟨i, j⟩, k⟩, l⟩, a⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
            (fun p => F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2)
            (by intro p; rfl))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

private theorem inner0S_two_metricCompatible_coord_corrA1
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * ((Γ i a * A a j) * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U a k * U j l * ((Γ a i * A i j) * B k l) := by
          simpa using sum5_swap_first_last (fun i j k l a : Idx =>
            U i k * U j l * ((Γ i a * A a j) * B k l))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U a k * U j l * (Γ a i * A i j * B k l))
                = (∑ a : Idx, Γ a i * U a k) * (U j l * A i j * B k l) := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l := by
                  ring

private theorem inner0S_two_metricCompatible_coord_corrA2
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * ((Γ j a * A i a) * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U a l * ((Γ a j * A i j) * B k l) := by
          simpa using sum5_swap_second_last (fun i j k l a : Idx =>
            U i k * U j l * ((Γ j a * A i a) * B k l))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U i k * U a l * (Γ a j * A i j * B k l))
                = U i k * (∑ a : Idx, Γ a j * U a l * (A i j * B k l)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = U i k * ((∑ a : Idx, Γ a j * U a l) * (A i j * B k l)) := by
                  rw [Finset.sum_mul]
            _ = U i k * (∑ a : Idx, Γ a j * U a l) * (A i j * B k l) := by
                  ring
            _ = U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l := by
                  ring

private theorem inner0S_two_metricCompatible_coord_corrB1
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * (A i j * (Γ k a * B a l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i a * U j l * (A i j * (Γ a k * B k l)) := by
          simpa using sum5_swap_third_last (fun i j k l a : Idx =>
            U i k * U j l * (A i j * (Γ k a * B a l)))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U i a * U j l * (A i j * (Γ a k * B k l)))
                = (∑ a : Idx, Γ a k * U i a) * (U j l * A i j * B k l) := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l := by
                  ring

private theorem inner0S_two_metricCompatible_coord_corrB2
    {Idx : Type*} [Fintype Idx]
    (U Γ A B : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a)))
        = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j l * (A i j * (Γ l a * B k a)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum]
          rw [Finset.mul_sum]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx,
            U i k * U j a * (A i j * (Γ a l * B k l)) := by
          simpa using sum5_swap_fourth_last (fun i j k l a : Idx =>
            U i k * U j l * (A i j * (Γ l a * B k a)))
    _ = (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          calc
            (∑ a : Idx, U i k * U j a * (A i j * (Γ a l * B k l)))
                = U i k * (∑ a : Idx, Γ a l * U j a * (A i j * B k l)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun a _ => ?_
                  ring
            _ = U i k * ((∑ a : Idx, Γ a l * U j a) * (A i j * B k l)) := by
                  rw [Finset.sum_mul]
            _ = U i k * (∑ a : Idx, Γ a l * U j a) * (A i j * B k l) := by
                  ring
            _ = U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l := by
                  ring

private theorem inner0S_two_metricCompatible_coord_DU_first
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a))) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      DU i k * U j l * A i j * B k l) =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) := by
  classical
  have hA1 := inner0S_two_metricCompatible_coord_corrA1 (U := U) (Γ := Γ) (A := A) (B := B)
  have hB1 := inner0S_two_metricCompatible_coord_corrB1 (U := U) (Γ := Γ) (A := A) (B := B)
  rw [hA1, hB1]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      DU i k * U j l * A i j * B k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (-(∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l -
          (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hDU i k]
          ring
    _ =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (∑ a : Idx, Γ a i * U a k) * U j l * A i j * B k l) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (∑ a : Idx, Γ a k * U i a) * U j l * A i j * B k l) := by
          simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

private theorem inner0S_two_metricCompatible_coord_DU_second
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a))) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * DU j l * A i j * B k l) =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
  classical
  have hA2 := inner0S_two_metricCompatible_coord_corrA2 (U := U) (Γ := Γ) (A := A) (B := B)
  have hB2 := inner0S_two_metricCompatible_coord_corrB2 (U := U) (Γ := Γ) (A := A) (B := B)
  rw [hA2, hB2]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * DU j l * A i j * B k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (-(U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) -
          U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hDU j l]
          ring
    _ =
      - (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * (∑ a : Idx, Γ a j * U a l) * A i j * B k l) -
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * (∑ a : Idx, Γ a l * U j a) * A i j * B k l) := by
          simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

private theorem inner0S_two_metricCompatible_coord_NA_sum
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DA NA : Idx -> Idx -> Real)
    (hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * A a q) -
          (∑ a : Idx, Γ q a * A p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (NA i j * B k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (DA i j * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (NA i j * B k l))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (U i k * U j l * (DA i j * B k l) -
          U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l) -
          U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hNA i j]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (DA i j * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)) := by
          simp [Finset.sum_sub_distrib]

private theorem inner0S_two_metricCompatible_coord_NB_sum
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DB NB : Idx -> Idx -> Real)
    (hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * B a q) -
          (∑ a : Idx, Γ q a * B p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * NB k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * DB k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * NB k l))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (U i k * U j l * (A i j * DB k l) -
          U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l)) -
          U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hNB k l]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * DB k l)) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))) -
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))) := by
          simp [Finset.sum_sub_distrib]

private theorem inner0S_two_metricCompatible_scalar_sum_algebra
    (P Q A1 A2 B1 B2 : Real) :
    (-A1 - B1) + (-A2 - B2) + P + Q =
      (P - A1 - A2) + (Q - B1 - B2) := by
  ring

private theorem inner0S_two_metricCompatible_coord_algebra
    {Idx : Type*} [Fintype Idx]
    (U Γ A B DA DB NA NB DU : Idx -> Idx -> Real)
    (hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U a q) + (∑ a : Idx, Γ a q * U p a)))
    (hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * A a q) -
          (∑ a : Idx, Γ q a * A p a))
    (hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * B a q) -
          (∑ a : Idx, Γ q a * B p a)) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
        U i k * U j l * (DA i j * B k l + A i j * DB k l))) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l)) := by
  classical
  let P : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (DA i j * B k l)
  let Q : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * DB k l)
  let A1 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ i a * A a j) * B k l)
  let A2 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * ((∑ a : Idx, Γ j a * A i a) * B k l)
  let B1 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ k a * B a l))
  let B2 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      U i k * U j l * (A i j * (∑ a : Idx, Γ l a * B k a))
  have hDU1 :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        DU i k * U j l * A i j * B k l) = -A1 - B1 := by
    simpa [A1, B1] using
      inner0S_two_metricCompatible_coord_DU_first
        (U := U) (Γ := Γ) (A := A) (B := B) (DU := DU) hDU
  have hDU2 :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * DU j l * A i j * B k l) = -A2 - B2 := by
    simpa [A2, B2] using
      inner0S_two_metricCompatible_coord_DU_second
        (U := U) (Γ := Γ) (A := A) (B := B) (DU := DU) hDU
  have hNA_sum :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l)) = P - A1 - A2 := by
    simpa [P, A1, A2] using
      inner0S_two_metricCompatible_coord_NA_sum
        (U := U) (Γ := Γ) (A := A) (B := B) (DA := DA) (NA := NA) hNA
  have hNB_sum :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (A i j * NB k l)) = Q - B1 - B2 := by
    simpa [Q, B1, B2] using
      inner0S_two_metricCompatible_coord_NB_sum
        (U := U) (Γ := Γ) (A := A) (B := B) (DB := DB) (NB := NB) hNB
  have hleft :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
          U i k * U j l * (DA i j * B k l + A i j * DB k l))) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          DU i k * U j l * A i j * B k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * DU j l * A i j * B k l) + P + Q := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
          U i k * U j l * (DA i j * B k l + A i j * DB k l)))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (DU i k * U j l * A i j * B k l +
            U i k * DU j l * A i j * B k l +
            U i k * U j l * (DA i j * B k l) +
            U i k * U j l * (A i j * DB k l)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          DU i k * U j l * A i j * B k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * DU j l * A i j * B k l) + P + Q := by
            simp [P, Q, Finset.sum_add_distrib, add_assoc]
  have hright :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l)) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (NA i j * B k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * NB k l)) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (U i k * U j l * (NA i j * B k l) +
            U i k * U j l * (A i j * NB k l)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (NA i j * B k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * NB k l)) := by
            simp [Finset.sum_add_distrib]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      ((DU i k * U j l + U i k * DU j l) * A i j * B k l +
        U i k * U j l * (DA i j * B k l + A i j * DB k l)))
        =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          DU i k * U j l * A i j * B k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * DU j l * A i j * B k l) + P + Q := hleft
    _ = (-A1 - B1) + (-A2 - B2) + P + Q := by
          rw [hDU1, hDU2]
    _ = (P - A1 - A2) + (Q - B1 - B2) := by
          exact inner0S_two_metricCompatible_scalar_sum_algebra P Q A1 A2 B1 B2
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (NA i j * B k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U i k * U j l * (A i j * NB k l)) := by
          rw [hNA_sum, hNB_sum]
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U i k * U j l * (NA i j * B k l + A i j * NB k l)) := hright.symm

private theorem deriv4sum
    {Idx : Type*} [Fintype Idx]
    (U A B : M -> Idx -> Idx -> Real)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x)
    (hA : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => A y i j) x)
    (hB : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => B y i j) x) :
    extDerivFun (I := I)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * A y i j * B y k l) x v =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v))) := by
  classical
  let F : Idx -> Idx -> Idx -> Idx -> M -> Real :=
    fun i j k l y => U y i k * U y j l * A y i j * B y k l
  have hterm (i j k l : Idx) :
      extDerivFun (I := I) (F i j k l) x v =
        ((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v)) := by
    have hUU := RicciFlower.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) v (hU i k) (hU j l)
    have hAB := RicciFlower.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) v (hA i j) (hB k l)
    have hAll := RicciFlower.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) v ((hU i k).mul (hU j l)) ((hA i j).mul (hB k l))
    calc
      extDerivFun (I := I) (F i j k l) x v =
          (U x i k * U x j l) *
              extDerivFun (I := I) (fun y : M => A y i j * B y k l) x v +
            extDerivFun (I := I) (fun y : M => U y i k * U y j l) x v *
              (A x i j * B x k l) := by
            simpa [F, mul_assoc] using hAll
      _ =
          ((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
              U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
              A x i j * B x k l +
            U x i k * U x j l *
              ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
                A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v)) := by
            rw [hUU, hAB]
            ring
  have hmdiff_l (i j k l : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F i j k l) x :=
    (((hU i k).mul (hU j l)).mul (hA i j)).mul (hB k l)
  let F3 : Idx -> Idx -> Idx -> M -> Real :=
    fun i j k => (Finset.univ : Finset Idx).sum (fun l : Idx => F i j k l)
  let F2 : Idx -> Idx -> M -> Real :=
    fun i j => (Finset.univ : Finset Idx).sum (fun k : Idx => F3 i j k)
  let F1 : Idx -> M -> Real :=
    fun i => (Finset.univ : Finset Idx).sum (fun j : Idx => F2 i j)
  let F0 : M -> Real :=
    (Finset.univ : Finset Idx).sum (fun i : Idx => F1 i)
  have hF3_mdiff (i j k : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F3 i j k) x := by
    dsimp [F3]
    exact
      RicciFlower.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun l : Idx => fun y : M => F i j k l y)
      (by
        intro l _hl
        exact hmdiff_l i j k l)
  have hF2_mdiff (i j : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F2 i j) x := by
    dsimp [F2]
    exact
      RicciFlower.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun k : Idx => F3 i j k)
      (by
        intro k _hk
        exact hF3_mdiff i j k)
  have hF1_mdiff (i : Idx) :
      MDifferentiableAt I 𝓘(Real, Real) (F1 i) x := by
    dsimp [F1]
    exact
      RicciFlower.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun j : Idx => F2 i j)
      (by
        intro j _hj
        exact hF2_mdiff i j)
  have hF0_mdiff :
      MDifferentiableAt I 𝓘(Real, Real) F0 x := by
    dsimp [F0]
    exact
      RicciFlower.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset Idx))
      (fun i : Idx => F1 i)
      (by
        intro i _hi
        exact hF1_mdiff i)
  have hF3_deriv (i j k : Idx) :
      extDerivFun (I := I) (F3 i j k) x v =
        ∑ l : Idx, extDerivFun (I := I) (F i j k l) x v := by
    dsimp [F3]
    exact
      RicciFlower.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun l : Idx => F i j k l) v
      (by
        intro l _hl
        exact hmdiff_l i j k l)
  have hF2_deriv (i j : Idx) :
      extDerivFun (I := I) (F2 i j) x v =
        ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := by
    have h := RicciFlower.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun k : Idx => F3 i j k) v
      (by
        intro k _hk
        exact hF3_mdiff i j k)
    simpa [F2, Finset.sum_apply, hF3_deriv] using h
  have hF1_deriv (i : Idx) :
      extDerivFun (I := I) (F1 i) x v =
        ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := by
    have h := RicciFlower.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun j : Idx => F2 i j) v
      (by
        intro j _hj
        exact hF2_mdiff i j)
    simpa [F1, Finset.sum_apply, hF2_deriv] using h
  have hF0_deriv :
      extDerivFun (I := I) F0 x v =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := by
    have h := RicciFlower.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (fun i : Idx => F1 i) v
      (by
        intro i _hi
        exact hF1_mdiff i)
    simpa [F0, Finset.sum_apply, hF1_deriv] using h
  have hF0_eq :
      (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        U y i k * U y j l * A y i j * B y k l) = F0 := by
    funext y
    simp [F0, F1, F2, F3, F]
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * A y i j * B y k l) x v =
      extDerivFun (I := I) F0 x v := by
        rw [hF0_eq]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          extDerivFun (I := I) (F i j k l) x v := hF0_deriv
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((extDerivFun (I := I) (fun y : M => U y i k) x v) * U x j l +
            U x i k * (extDerivFun (I := I) (fun y : M => U y j l) x v)) *
            A x i j * B x k l +
          U x i k * U x j l *
            ((extDerivFun (I := I) (fun y : M => A y i j) x v) * B x k l +
              A x i j * (extDerivFun (I := I) (fun y : M => B y k l) x v))) := by
        refine Finset.sum_congr rfl fun i _hi => ?_
        refine Finset.sum_congr rfl fun j _hj => ?_
        refine Finset.sum_congr rfl fun k _hk => ?_
        refine Finset.sum_congr rfl fun l _hl => ?_
        exact hterm i j k l

@[simp] private theorem fin2_apply_ite {α β : Type*} (f : α -> β) (i j : α) :
    (fun q : Fin 2 => f (if q = 0 then i else j)) =
      fun q : Fin 2 => if q = 0 then f i else f j := by
  funext q
  by_cases hq : q = 0 <;> simp [hq]

/-- Coordinate squared norms are independent of the chosen frame realization,
because both coordinate sums equal the intrinsic norm. -/
theorem coord_normSq0S_eq_coord
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    (A : Tensor0SSpace s I x) :
    coordInner0S (I := I) (x := x) s gInv₁ A A basis₁ =
      coordInner0S (I := I) (x := x) s gInv₂ A A basis₂ := by
  rw [← normSq0S_eq_coord (I := I) g x s basis₁ gInv₁ hinv₁ A,
    ← normSq0S_eq_coord (I := I) g x s basis₂ gInv₂ hinv₂ A]

private theorem totalNabla0SRealizes_eval_point_vector_smooth_slots
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : Nat} {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A nablaA)
    {x : M} (W : TangentSpace I x)
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    nablaA x (Fin.cons W (fun q : Fin s => V q x)) =
      extDerivFun (I := I)
        (fun y : M => A y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        A x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W)) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have h0 := TotalNabla0SRealizes.eval_smooth_slots
    (I := I) hA Wsec V x
  simpa [hWsec] using h0

private theorem cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (alpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (hAlpha : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M)
    (hSharp : MDiffAt
      (T% (fun y : M => cotangentSharp (I := I) g y (alpha y))) x) :
    cov (fun y : M => cotangentSharp (I := I) g y (alpha y)) x (X x) =
      cotangentSharp (I := I) g x
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
          (nablaAlpha x) (X x)) := by
  classical
  let Ysharp : (y : M) -> TangentSpace I y :=
    fun y => cotangentSharp (I := I) g y (alpha y)
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x)))
      Real (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  apply eq_of_inner_basis_eq (I := I) g x basis
  intro i
  obtain ⟨Zsec, hZsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (basis i)
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZ : MDiffAt (T% (fun y : M => Zsec y)) x :=
    Zsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc_apply :=
    RicciFlower.Connection.metric_compatible_apply (I := I) hmc
      (fun y : M => X y) Ysharp (fun y : M => Zsec y) hX hSharp hZ
  have hpair_fun :
      (fun y : M => g.inner y (Ysharp y) (Zsec y)) =
        fun y : M => alpha y (fun _ : Fin 1 => Zsec y) := by
    funext y
    simp [Ysharp, cotangentSharp_inner, cotangentToDual_apply]
  have hderiv_pair :
      mfderiv I 𝓘(Real, Real)
          (fun y : M => g.inner y (Ysharp y) (Zsec y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) := by
    rw [hpair_fun]
    exact (RicciFlower.extDerivFun_real_eq_mfderiv (I := I)
      (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x)).symm
  have hnabla_eval :=
    totalNabla0SRealizes_eval_point_vector_smooth_slots (I := I)
      hAlpha (X x) (fun _ : Fin 1 => Zsec)
  have hnabla_pair :
      g.inner x
          (cotangentSharp (I := I) g x
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (nablaAlpha x) (X x))) (Zsec x) =
        extDerivFun (I := I)
          (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) -
          alpha x (fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x)) := by
    rw [cotangentSharp_inner, cotangentToDual_apply]
    rw [tensor0S_curry_apply_cons]
    have hupdate :
        Function.update (fun r : Fin 1 => Zsec x) 0
            ((cov (fun y : M => Zsec y) x) (X x)) =
          fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x) := by
      funext q
      fin_cases q
      simp
    simpa [hupdate] using hnabla_eval
  calc
    g.inner x
        (cov (fun y : M => cotangentSharp (I := I) g y (alpha y)) x (X x))
        (basis i)
        = g.inner x
            (cov Ysharp x (X x)) (Zsec x) := by
          simp [Ysharp, hZsec]
    _ = extDerivFun (I := I)
          (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) -
          alpha x (fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x)) := by
          have hpair_cov :
              g.inner x (cov Ysharp x (X x)) (Zsec x) =
                extDerivFun (I := I)
                  (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x) -
                  g.inner x (Ysharp x)
                    ((cov (fun y : M => Zsec y) x) (X x)) := by
            let a := g.inner x (cov Ysharp x (X x)) (Zsec x)
            let b := g.inner x (Ysharp x)
              ((cov (fun y : M => Zsec y) x) (X x))
            let d := mfderiv I 𝓘(Real, Real)
              (fun y : M => g.inner y (Ysharp y) (Zsec y)) x (X x)
            let e := extDerivFun (I := I)
              (fun y : M => alpha y (fun _ : Fin 1 => Zsec y)) x (X x)
            change a = e - b
            have hs : d = a + b := by
              simpa [a, b, d] using hmc_apply
            have hd : d = e := by
              simpa [d, e] using hderiv_pair
            have hsum_eq : a + b = e := hs.symm.trans hd
            calc
              a = a + b - b := by ring
              _ = e - b := by rw [hsum_eq]
          rw [hpair_cov]
          rw [show
            g.inner x (Ysharp x) ((cov (fun y : M => Zsec y) x) (X x)) =
              alpha x (fun _ : Fin 1 => (cov (fun y : M => Zsec y) x) (X x)) by
                simp [Ysharp, cotangentSharp_inner, cotangentToDual_apply]]
    _ = g.inner x
          (cotangentSharp (I := I) g x
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (nablaAlpha x) (X x))) (Zsec x) := by
          exact hnabla_pair.symm
    _ = g.inner x
          (cotangentSharp (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
              (nablaAlpha x) (X x))) (basis i) := by
          simp [hZsec]

private theorem cotangentInner_metricCompatible_extDerivFun_of_sharp_mdiffAt
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (alpha beta : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (nablaAlpha nablaBeta :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (hAlpha : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (hBeta : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov beta nablaBeta)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M)
    (hSharpAlpha : MDiffAt
      (T% (fun y : M => cotangentSharp (I := I) g y (alpha y))) x)
    (hSharpBeta : MDiffAt
      (T% (fun y : M => cotangentSharp (I := I) g y (beta y))) x) :
    extDerivFun (I := I)
        (fun y : M => cotangentInner (I := I) g y (alpha y) (beta y))
        x (X x) =
      cotangentInner (I := I) g x
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
          (nablaAlpha x) (X x)) (beta x) +
        cotangentInner (I := I) g x (alpha x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaBeta x) (X x)) := by
  let Asharp : (y : M) -> TangentSpace I y :=
    fun y => cotangentSharp (I := I) g y (alpha y)
  let Bsharp : (y : M) -> TangentSpace I y :=
    fun y => cotangentSharp (I := I) g y (beta y)
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc_apply :=
    RicciFlower.Connection.metric_compatible_apply (I := I) hmc
      (fun y : M => X y) Asharp Bsharp hX (by simpa [Asharp] using hSharpAlpha)
      (by simpa [Bsharp] using hSharpBeta)
  have hcovA :
      cov Asharp x (X x) =
        cotangentSharp (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaAlpha x) (X x)) := by
    simpa [Asharp] using
      cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
        cov g hmc alpha nablaAlpha hAlpha X x hSharpAlpha
  have hcovB :
      cov Bsharp x (X x) =
        cotangentSharp (I := I) g x
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x
            (nablaBeta x) (X x)) := by
    simpa [Bsharp] using
      cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (I := I)
        cov g hmc beta nablaBeta hBeta X x hSharpBeta
  rw [RicciFlower.extDerivFun_real_eq_mfderiv]
  change
    mfderiv I 𝓘(Real, Real)
        (fun y : M => g.inner y (Asharp y) (Bsharp y)) x (X x) =
      _
  rw [hmc_apply]
  rw [hcovA, hcovB]
  rfl

/-- Differentiability of the induced `(0,2)` tensor inner product. -/
theorem inner0S_two_mdiff
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x := by
  classical
  let Idx : Type _ := RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
  let slots : Idx -> Idx -> Fin 2 -> Idx :=
    fun i j q => if q = 0 then i else j
  let U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      RicciFlower.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y)
  let Ac : M -> Idx -> Idx -> Real :=
    fun y i j => A y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let Bc : M -> Idx -> Idx -> Real :=
    fun y i j => B y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  have hx : x ∈ RicciFlower.Coordinates.coordinateFrameSet (I := I) x :=
    RicciFlower.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      RicciFlower.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hAmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Ac y i j) x := by
    intro i j
    have h := RicciFlower.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x (slots i j)
    have hfun :
        (fun y : M => A y
          (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Ac y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hBmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Bc y i j) x := by
    intro i j
    have h := RicciFlower.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x (slots i j)
    have hfun :
        (fun y : M => B y
          (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Bc y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hlocal :
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l := by
    filter_upwards
      [(RicciFlower.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    have h := inner0S_two_eq_coord (I := I) g y
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)
    simpa [U, Ac, Bc, frame, slots,
      RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
  have hsum :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l) x := by
    have hraw : MDifferentiableAt I 𝓘(Real, Real)
        (∑ i : Idx, fun y : M => ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l) x := by
      refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
        (t := (Finset.univ : Finset Idx)) ?_
      intro i _
      have hraw_j : MDifferentiableAt I 𝓘(Real, Real)
          (∑ j : Idx, fun y : M => ∑ k : Idx, ∑ l : Idx,
            U y i k * U y j l * Ac y i j * Bc y k l) x := by
        refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
          (t := (Finset.univ : Finset Idx)) ?_
        intro j _
        have hraw_k : MDifferentiableAt I 𝓘(Real, Real)
            (∑ k : Idx, fun y : M => ∑ l : Idx,
              U y i k * U y j l * Ac y i j * Bc y k l) x := by
          refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
            (t := (Finset.univ : Finset Idx)) ?_
          intro k _
          have hraw_l : MDifferentiableAt I 𝓘(Real, Real)
              (∑ l : Idx, fun y : M =>
                U y i k * U y j l * Ac y i j * Bc y k l) x := by
            refine MDifferentiableAt.sum (𝕜 := Real) (I := I)
              (t := (Finset.univ : Finset Idx)) ?_
            intro l _
            exact (((hUmdiff i k).mul (hUmdiff j l)).mul (hAmdiff i j)).mul
              (hBmdiff k l)
          exact hraw_l.congr_of_eventuallyEq
            (by filter_upwards with y; simp [Finset.sum_apply])
        exact hraw_k.congr_of_eventuallyEq
          (by filter_upwards with y; simp [Finset.sum_apply])
      exact hraw_j.congr_of_eventuallyEq
        (by filter_upwards with y; simp [Finset.sum_apply])
    exact hraw.congr_of_eventuallyEq
      (by filter_upwards with y; simp [Finset.sum_apply])
  exact hsum.congr_of_eventuallyEq hlocal

/-- Directional metric compatibility for the induced `(0,2)` tensor inner product.

This version is stated directly with `nabla0SFun`, so it can be used for
frozen auxiliary tensor fields without constructing a bundled total derivative. -/
theorem inner0S_two_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      inner0S (I := I) g x 2
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) +
        inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) := by
  classical
  let Idx : Type _ := RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
  let hframe : IsLocalFrameOn I E 1 frame
      (RicciFlower.Coordinates.coordinateFrameSet (I := I) x) :=
    RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x
  let slots : Idx -> Idx -> Fin 2 -> Idx :=
    fun i j q => if q = 0 then i else j
  let U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      RicciFlower.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y)
  let Ac : M -> Idx -> Idx -> Real :=
    fun y i j => A y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let Bc : M -> Idx -> Idx -> Real :=
    fun y i j => B y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let DA : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Ac y i j) x (X x)
  let DB : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Bc y i j) x (X x)
  let DU : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => U y i j) x (X x)
  let Γ : Idx -> Idx -> Real :=
    fun i j =>
      RicciFlower.Coordinates.christoffelAlongInFrame cov frame hframe x (X x) i j
  let NA : Idx -> Idx -> Real :=
    fun i j =>
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  let NB : Idx -> Idx -> Real :=
    fun i j =>
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  have hx : x ∈ RicciFlower.Coordinates.coordinateFrameSet (I := I) x :=
    RicciFlower.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      RicciFlower.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hAmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Ac y i j) x := by
    intro i j
    have h := RicciFlower.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x (slots i j)
    have hfun :
        (fun y : M => A y
          (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Ac y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hBmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Bc y i j) x := by
    intro i j
    have h := RicciFlower.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x (slots i j)
    have hfun :
        (fun y : M => B y
          (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Bc y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hlocal :
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l := by
    filter_upwards
      [(RicciFlower.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    have h := inner0S_two_eq_coord (I := I) g y
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)
    simpa [U, Ac, Bc, frame, slots,
      RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
  have hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U x a q) + (∑ a : Idx, Γ a q * U x p a)) := by
    intro p q
    have hzero := RicciFlower.Coordinates.gInvCovZeroAt
      (I := I) g cov X hmc x p q
    unfold RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompAlongInFrame at hzero
    have hzero' :
        DU p q +
          (∑ a : Idx, Γ a p * U x a q) +
          (∑ a : Idx, Γ a q * U x p a) = 0 := by
      simpa [DU, U, Γ, frame, hframe, Idx] using hzero
    linarith
  have hDA_coord (p q : Idx) :
      DA p q =
        RicciFlower.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
    have hfun :
        (fun y : M => Ac y p q) =
          fun y : M => A y
            (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DA p q =
          extDerivFun (I := I) (fun y : M => Ac y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => A y
              (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          RicciFlower.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
            simp [RicciFlower.extDerivFun_real_eq_mfderiv,
              RicciFlower.Coordinates.coordDeriv0SAt]
  have hDB_coord (p q : Idx) :
      DB p q =
        RicciFlower.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
    have hfun :
        (fun y : M => Bc y p q) =
          fun y : M => B y
            (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DB p q =
          extDerivFun (I := I) (fun y : M => Bc y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => B y
              (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          RicciFlower.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
            simp [RicciFlower.extDerivFun_real_eq_mfderiv,
              RicciFlower.Coordinates.coordDeriv0SAt]
  have hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
          (∑ a : Idx, Γ q a * Ac x p a) := by
    intro p q
    have hcoord := RicciFlower.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X A x
      (RicciFlower.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x A)
      p q
    have hs1 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            A x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Ac x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            A x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Ac x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (RicciFlower.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => A y) (slots p q) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  A x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  A x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
            rw [← hDA_coord p q, hs1, hs2]
    simpa [NA] using hcoord'
  have hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
          (∑ a : Idx, Γ q a * Bc x p a) := by
    intro p q
    have hcoord := RicciFlower.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X B x
      (RicciFlower.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x B)
      p q
    have hs1 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            B x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Bc x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            B x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Bc x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (RicciFlower.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => B y) (slots p q) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  B x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  B x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
            rw [← hDB_coord p q, hs1, hs2]
    simpa [NB] using hcoord'
  have hleft_deriv :
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
    calc
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            U y i k * U y j l * Ac y i j * Bc y k l) x (X x) := by
          exact RicciFlower.Coordinates.deriv_congr_nhds (I := I)
            (x := x) (X x) hlocal
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
          simpa [U, Ac, Bc, DA, DB, DU] using
            deriv4sum (I := I) (U := U) (A := Ac) (B := Bc)
              (x := x) (v := X x) hUmdiff hAmdiff hBmdiff
  have halg :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l)))) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) :=
    inner0S_two_metricCompatible_coord_algebra
      (U := U x) (Γ := Γ) (A := Ac x) (B := Bc x)
      (DA := DA) (DB := DB) (NA := NA) (NB := NB) (DU := DU)
      hDU hNA hNB
  have hsplit :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l)) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (U x i k * U x j l * (NA i j * Bc x k l) +
            U x i k * U x j l * (Ac x i j * NB k l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = _ := by
          simp [Finset.sum_add_distrib]
  have hRhsA :
      inner0S (I := I) g x 2
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hx)
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x)
    calc
      inner0S (I := I) g x 2
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * NA i j * Bc x k l := by
          simpa [U, Bc, NA, frame,
            RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  have hRhsB :
      inner0S (I := I) g x 2 (A x)
        (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hx)
      (A x)
      (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x)
    calc
      inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * Ac x i j * NB k l := by
          simpa [U, Ac, NB, frame,
            RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  calc
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
          U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) :=
        hleft_deriv
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) := halg
    _ = inner0S (I := I) g x 2
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X A x) (B x) +
        inner0S (I := I) g x 2 (A x)
          (nabla0SFun (E := E) (H := H) (I := I) (M := M) 2 cov X B x) := by
          rw [hsplit, ← hRhsA, ← hRhsB]

/-- Metric compatibility lifted to the induced inner product on `(0,2)`
covariant tensor fibers.

This is the tensor-metric API bridge needed by Bochner product rules.  The
base assumption `Connection.IsMetricCompatible` only differentiates tangent
inner products; this theorem is the induced compatibility statement for
`inner0S g x 2` and the total covariant derivative on `(0,2)` tensors.

The remaining lower frontier is the component-to-invariant assembly: in a
coordinate-frame neighborhood, rewrite `inner0S g y 2 (A y) (B y)` as the
four-index inverse-metric contraction, differentiate that local expression,
use localized `nabla gInv = 0`, then invoke
`inner0S_two_metricCompatible_coord_algebra`. -/
theorem inner0S_two_metricCompatible_extDerivFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA nablaB :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      inner0S (I := I) g x 2
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x)) (B x) +
        inner0S (I := I) g x 2 (A x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x)) := by
  classical
  let Idx : Type _ := RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
  let hframe : IsLocalFrameOn I E 1 frame
      (RicciFlower.Coordinates.coordinateFrameSet (I := I) x) :=
    RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x
  let slots : Idx -> Idx -> Fin 2 -> Idx :=
    fun i j q => if q = 0 then i else j
  let U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      RicciFlower.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y)
  let Ac : M -> Idx -> Idx -> Real :=
    fun y i j => A y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let Bc : M -> Idx -> Idx -> Real :=
    fun y i j => B y (fun q : Fin 2 => if q = 0 then frame i y else frame j y)
  let DA : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Ac y i j) x (X x)
  let DB : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => Bc y i j) x (X x)
  let DU : Idx -> Idx -> Real :=
    fun i j => extDerivFun (I := I) (fun y : M => U y i j) x (X x)
  let Γ : Idx -> Idx -> Real :=
    fun i j =>
      RicciFlower.Coordinates.christoffelAlongInFrame cov frame hframe x (X x) i j
  let NA : Idx -> Idx -> Real :=
    fun i j =>
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaA x) (X x)) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  let NB : Idx -> Idx -> Real :=
    fun i j =>
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaB x) (X x)) (fun q : Fin 2 => if q = 0 then frame i x else frame j x)
  have hx : x ∈ RicciFlower.Coordinates.coordinateFrameSet (I := I) x :=
    RicciFlower.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      RicciFlower.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hAmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Ac y i j) x := by
    intro i j
    have h := RicciFlower.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x (slots i j)
    have hfun :
        (fun y : M => A y
          (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Ac y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hBmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Bc y i j) x := by
    intro i j
    have h := RicciFlower.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x (slots i j)
    have hfun :
        (fun y : M => B y
          (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
            (slots i j a) y)) =
          fun y : M => Bc y i j := by
      funext y
      exact congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) i j)
    exact hfun ▸ h.mdifferentiableAt (by simp)
  have hlocal :
      (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U y i k * U y j l * Ac y i j * Bc y k l := by
    filter_upwards
      [(RicciFlower.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    have h := inner0S_two_eq_coord (I := I) g y
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)
    simpa [U, Ac, Bc, frame, slots,
      RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
  have hDU : ∀ p q : Idx,
      DU p q =
        - ((∑ a : Idx, Γ a p * U x a q) + (∑ a : Idx, Γ a q * U x p a)) := by
    intro p q
    have hzero := RicciFlower.Coordinates.gInvCovZeroAt
      (I := I) g cov X hmc x p q
    unfold RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompAlongInFrame at hzero
    have hzero' :
        DU p q +
          (∑ a : Idx, Γ a p * U x a q) +
          (∑ a : Idx, Γ a q * U x p a) = 0 := by
      simpa [DU, U, Γ, frame, hframe, Idx] using hzero
    linarith
  have hDA_coord (p q : Idx) :
      DA p q =
        RicciFlower.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
    have hfun :
        (fun y : M => Ac y p q) =
          fun y : M => A y
            (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => A y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DA p q =
          extDerivFun (I := I) (fun y : M => Ac y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => A y
              (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          RicciFlower.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => A y) (slots p q) := by
            simp [RicciFlower.extDerivFun_real_eq_mfderiv,
              RicciFlower.Coordinates.coordDeriv0SAt]
  have hDB_coord (p q : Idx) :
      DB p q =
        RicciFlower.Coordinates.coordDeriv0SAt (I := I)
          (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
    have hfun :
        (fun y : M => Bc y p q) =
          fun y : M => B y
            (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
              (slots p q a) y) := by
      funext y
      exact (congrArg (fun f : Fin 2 -> TangentSpace I y => B y f)
        (fin2_apply_ite (fun r : Idx => frame r y) p q)).symm
    calc
      DB p q =
          extDerivFun (I := I) (fun y : M => Bc y p q) x (X x) := rfl
      _ =
          extDerivFun (I := I)
            (fun y : M => B y
              (fun a : Fin 2 => RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (slots p q a) y)) x (X x) := by
            rw [hfun]
      _ =
          RicciFlower.Coordinates.coordDeriv0SAt (I := I)
            (fun y : M => X y) x (fun y : M => B y) (slots p q) := by
            simp [RicciFlower.extDerivFun_real_eq_mfderiv,
              RicciFlower.Coordinates.coordDeriv0SAt]
  have hNA : ∀ p q : Idx,
      NA p q =
        DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
          (∑ a : Idx, Γ q a * Ac x p a) := by
    intro p q
    have happ := TotalNabla0SRealizes.apply (I := I) hA X x
      (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
    have hcoord := RicciFlower.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X A x
      (RicciFlower.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x A)
      p q
    have hs1 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            A x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Ac x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            A x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Ac x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (RicciFlower.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => A y) (slots p q) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  A x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  A x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := by
            rw [← hDA_coord p q, hs1, hs2]
    calc
      NA p q =
          nablaA x (Fin.cons (X x)
            (fun r : Fin 2 => if r = 0 then frame p x else frame q x)) := by
            simp [NA, tensor0S_curry_apply_cons]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X A x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) := happ
      _ =
          DA p q - (∑ a : Idx, Γ p a * Ac x a q) -
            (∑ a : Idx, Γ q a * Ac x p a) := hcoord'
  have hNB : ∀ p q : Idx,
      NB p q =
        DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
          (∑ a : Idx, Γ q a * Bc x p a) := by
    intro p q
    have happ := TotalNabla0SRealizes.apply (I := I) hB X x
      (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
    have hcoord := RicciFlower.Coordinates.nabla0SFun_two_eval_coordFrame
      (I := I) cov X B x
      (RicciFlower.Coordinates.modelDeriv_eq_coordDeriv0SAt (I := I) X x B)
      p q
    have hs1 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) p a *
            B x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x)) =
          ∑ a : Idx, Γ p a * Bc x a q := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then a else q) x) =
            (fun r : Fin 2 => if r = 0 then frame a x else frame q x) :=
        fin2_apply_ite (fun r : Idx => frame r x) a q
      rw [hslot]
    have hs2 :
        (∑ a : Idx,
          RicciFlower.Coordinates.christoffelAlongInFrame cov
              (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
              (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
              x (X x) q a *
            B x (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x)) =
          ∑ a : Idx, Γ q a * Bc x p a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hslot :
          (fun r : Fin 2 =>
              RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                (if r = 0 then p else a) x) =
            (fun r : Fin 2 => if r = 0 then frame p x else frame a x) :=
        fin2_apply_ite (fun r : Idx => frame r x) p a
      rw [hslot]
    have hcoord' :
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) =
          DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
      calc
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x)
            =
          (RicciFlower.Coordinates.coordDeriv0SAt (I := I)
              (fun y : M => X y) x (fun y : M => B y) (slots p q) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) p a *
                  B x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then a else q) x)) -
              ∑ a : Idx,
                RicciFlower.Coordinates.christoffelAlongInFrame cov
                    (RicciFlower.Coordinates.coordinateFrameAt (I := I) x)
                    (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x)
                    x (X x) q a *
                  B x (fun r : Fin 2 =>
                    RicciFlower.Coordinates.coordinateFrameAt (I := I) x
                      (if r = 0 then p else a) x) := by
            simpa [frame, slots] using hcoord
        _ = DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := by
            rw [← hDB_coord p q, hs1, hs2]
    calc
      NB p q =
          nablaB x (Fin.cons (X x)
            (fun r : Fin 2 => if r = 0 then frame p x else frame q x)) := by
            simp [NB, tensor0S_curry_apply_cons]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x
              (fun r : Fin 2 => if r = 0 then frame p x else frame q x) := happ
      _ =
          DB p q - (∑ a : Idx, Γ p a * Bc x a q) -
            (∑ a : Idx, Γ q a * Bc x p a) := hcoord'
  have hleft_deriv :
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
    calc
      extDerivFun (I := I)
          (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            U y i k * U y j l * Ac y i j * Bc y k l) x (X x) := by
          exact RicciFlower.Coordinates.deriv_congr_nhds (I := I)
            (x := x) (X x) hlocal
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) := by
          simpa [U, Ac, Bc, DA, DB, DU] using
            deriv4sum (I := I) (U := U) (A := Ac) (B := Bc)
              (x := x) (v := X x) hUmdiff hAmdiff hBmdiff
  have halg :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
            U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l)))) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) :=
    inner0S_two_metricCompatible_coord_algebra
      (U := U x) (Γ := Γ) (A := Ac x) (B := Bc x)
      (DA := DA) (DB := DB) (NA := NA) (NB := NB) (DU := DU)
      hDU hNA hNB
  have hsplit :
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l)) := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (U x i k * U x j l * (NA i j * Bc x k l) +
            U x i k * U x j l * (Ac x i j * NB k l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = _ := by
          simp [Finset.sum_add_distrib]
  have hRhsA :
      inner0S (I := I) g x 2
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x)) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hx)
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaA x) (X x)) (B x)
    calc
      inner0S (I := I) g x 2
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaA x) (X x)) (B x) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * NA i j * Bc x k l := by
          simpa [U, Bc, NA, frame,
            RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  have hRhsB :
      inner0S (I := I) g x 2 (A x)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaB x) (X x)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
    have h := inner0S_two_eq_coord (I := I) g x
      (RicciFlower.Coordinates.coordinateFrameAt_basis (I := I) x hx)
      (U x) (RicciFlower.Coordinates.gInvBasisAt (I := I) g x hx)
      (A x)
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (nablaB x) (X x))
    calc
      inner0S (I := I) g x 2 (A x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * Ac x i j * NB k l := by
          simpa [U, Ac, NB, frame,
            RicciFlower.Coordinates.coordinateFrameAt_basis_apply] using h
      _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (Ac x i j * NB k l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  calc
    extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y 2 (A y) (B y)) x (X x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (((DU i k * U x j l + U x i k * DU j l) * Ac x i j * Bc x k l +
          U x i k * U x j l * (DA i j * Bc x k l + Ac x i j * DB k l))) :=
        hleft_deriv
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          U x i k * U x j l * (NA i j * Bc x k l + Ac x i j * NB k l) := halg
    _ = inner0S (I := I) g x 2
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaA x) (X x)) (B x) +
        inner0S (I := I) g x 2 (A x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaB x) (X x)) := by
          rw [hsplit, ← hRhsA, ← hRhsB]

end

end Tensor0SBundle
