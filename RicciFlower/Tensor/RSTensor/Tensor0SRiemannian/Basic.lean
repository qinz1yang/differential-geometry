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

def realFlatLinear : Real →ₗ[Real] Module.Dual Real Real where
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
def homFlatLinear [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
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

theorem trace_adjoint_comp_eq_sum_inner
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

theorem trace_adjoint_comp_nonneg
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [InnerProductSpace Real W] [FiniteDimensional Real W]
    (A : V →ₗ[Real] W) :
    0 <= LinearMap.trace Real V ((LinearMap.adjoint A).comp A) := by
  rw [trace_adjoint_comp_eq_sum_inner]
  exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg

theorem trace_adjoint_comp_eq_zero_iff
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

theorem trace_adjoint_comp_comm
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

theorem metric_adjoint_eq_adjoint
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

theorem homFlatLinear_comm [AddCommGroup V] [Module Real V]
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

theorem homFlatLinear_nonneg [AddCommGroup V] [Module Real V]
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

theorem homFlatLinear_self_eq_zero_iff [AddCommGroup V] [Module Real V]
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

theorem hom_nonneg [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
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

/-- Squared tensor norms induced by a Riemannian metric are nonnegative. -/
theorem normSq0S_nonneg
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    0 <= normSq0S (I := I) g x s A := by
  simpa [normSq0S, inner0S] using
    (MetricFiberData.inner_nonneg (tensor0SMetricData (I := I) g x s) A)

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


end

end Tensor0SBundle
