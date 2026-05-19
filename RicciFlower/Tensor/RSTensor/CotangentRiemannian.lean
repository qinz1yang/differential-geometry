import RicciFlower.Tensor.RSTensor.TangentRiemannian
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Basis

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Cotangent Fibers

The Riemannian metric on `T_x M` induces the dual metric on `T_x^* M` by
raising covectors with the tangent sharp map.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Interpret a realized cotangent vector as a continuous linear functional. -/
def cotangentToCLM {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real :=
  continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
    (Tensor0SSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α)

/-- Interpret a realized cotangent vector as an algebraic dual vector. -/
def cotangentToDual {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLM (I := I) α).toLinearMap

@[simp] theorem cotangentToDual_apply {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDual (I := I) α X = α (fun _ : Fin 1 => X) := by
  simpa [cotangentToDual, cotangentToCLM, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv] using
    congrArg (fun v : Fin 1 -> TangentSpace I x => α v)
    (funext fun i => by fin_cases i; rfl)

/-- The linear identification from realized one-covariant tensors to the
algebraic dual of the tangent space. -/
def cotangentToDualLinear {x : M} :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun := cotangentToDual (I := I)
  map_add' α β := by
    ext X
    rfl
  map_smul' c α := by
    ext X
    rfl

@[simp] theorem cotangentToDualLinear_apply {x : M}
    (α : Tensor0SSpace 1 I x) :
    cotangentToDualLinear (I := I) α = cotangentToDual (I := I) α := by
  rfl

theorem cotangentToDualLinear_injective {x : M} :
    Function.Injective (cotangentToDualLinear (I := I) (x := x)) := by
  intro α β h
  ext v
  have hv :
      (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  have h0 := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L (v 0)) h
  simpa [cotangentToDualLinear, cotangentToDual_apply, hv] using h0

/-- Realize an algebraic cotangent vector as a `(0,1)` tensor.

In finite dimension the algebraic linear functional is automatically continuous,
so it can be uncurried into the one-slot continuous multilinear tensor model. -/
def dualToCotangent {x : M} (α : Module.Dual Real (TangentSpace I x)) :
    Tensor0SSpace 1 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (LinearMap.toContinuousLinearMap α))

def dualToCotangentLinear {x : M} :
    Module.Dual Real (TangentSpace I x) →ₗ[Real] Tensor0SSpace 1 I x where
  toFun := dualToCotangent (I := I)
  map_add' α β := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext X
    change (α + β) X = α X + β X
    rfl
  map_smul' c α := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext X
    change (c • α) X = c * α X
    rfl

@[simp] theorem dualToCotangentLinear_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    dualToCotangentLinear (I := I) α = dualToCotangent (I := I) α := by
  rfl

@[simp] theorem dualToCotangent_apply {x : M}
    (α : Module.Dual Real (TangentSpace I x)) (X : TangentSpace I x) :
    dualToCotangent (I := I) α (fun _ : Fin 1 => X) = α X := by
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (LinearMap.toContinuousLinearMap α)) (fun _ : Fin 1 => X) = α X
  rfl

@[simp] theorem cotangentToDual_dualToCotangent {x : M}
    (α : Module.Dual Real (TangentSpace I x)) :
    cotangentToDual (I := I) (dualToCotangent (I := I) α) = α := by
  ext X
  simp

/-- The linear sharp map `T_x^*M -> T_xM` induced by `g`. -/
def cotangentSharpLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] TangentSpace I x :=
  ((tangentMetricData (I := I) g x).metric.sharp).toLinearMap.comp
    (cotangentToDualLinear (I := I) (x := x))

/-- Raise a realized cotangent vector using the Riemannian metric. -/
def cotangentSharp (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  cotangentSharpLinear (I := I) g x α

@[simp] theorem cotangentSharpLinear_apply
    (g : SmoothMetric I M) (x : M) (α : Tensor0SSpace 1 I x) :
    cotangentSharpLinear (I := I) g x α = cotangentSharp (I := I) g x α := by
  rfl

theorem cotangentSharpLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentSharpLinear (I := I) g x) := by
  intro α β h
  apply cotangentToDualLinear_injective (I := I) (x := x)
  exact ((tangentMetricData (I := I) g x).metric.sharp.injective h)

/-- The dual metric on cotangent vectors:
`<α, β> = g(α#, β#)`. -/
def cotangentInner (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x
    (cotangentSharpLinear (I := I) g x α)
    (cotangentSharpLinear (I := I) g x β)

@[simp] theorem cotangentInner_eq_sharp
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      g.inner x (cotangentSharp (I := I) g x α)
        (cotangentSharp (I := I) g x β) := by
  rfl

/-- The flat map on `T_x^*M`, obtained by pulling the tangent metric back along
the sharp map. -/
def cotangentFlatLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (Tensor0SSpace 1 I x) where
  toFun α :=
    { toFun := fun β => cotangentInner (I := I) g x α β
      map_add' := by
        intro β γ
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (β + γ) = S β + S γ := map_add S β γ
        change g.inner x (S α) (S (β + γ)) =
          g.inner x (S α) (S β) + g.inner x (S α) (S γ)
        rw [hS]
        simp
      map_smul' := by
        intro c β
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (c • β) = c • S β := map_smul S c β
        change g.inner x (S α) (S (c • β)) = c * g.inner x (S α) (S β)
        rw [hS]
        simp }
  map_add' α β := by
    ext γ
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (α + β) = S α + S β := map_add S α β
    change g.inner x (S (α + β)) (S γ) =
      g.inner x (S α) (S γ) + g.inner x (S β) (S γ)
    rw [hS]
    simp
  map_smul' c α := by
    ext β
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (c • α) = c • S α := map_smul S c α
    change g.inner x (S (c • α)) (S β) = c * g.inner x (S α) (S β)
    rw [hS]
    simp

@[simp] theorem cotangentFlatLinear_apply
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentFlatLinear (I := I) g x α β =
      cotangentInner (I := I) g x α β := by
  rfl

theorem cotangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentFlatLinear (I := I) g x) := by
  intro α β h
  have hsub : cotangentSharpLinear (I := I) g x (α - β) = 0 := by
    by_contra hsharp
    have hpos :
        0 <
          g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) :=
      g.pos x (cotangentSharpLinear (I := I) g x (α - β)) hsharp
    have h_eval :
        cotangentFlatLinear (I := I) g x α (α - β) =
          cotangentFlatLinear (I := I) g x β (α - β) :=
      congrArg
        (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β)) h
    have hdiff : cotangentFlatLinear (I := I) g x (α - β) (α - β) = 0 := by
      calc
        cotangentFlatLinear (I := I) g x (α - β) (α - β)
            = (cotangentFlatLinear (I := I) g x α -
                cotangentFlatLinear (I := I) g x β) (α - β) := by
                exact congrArg
                  (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β))
                  (map_sub (cotangentFlatLinear (I := I) g x) α β)
        _ = cotangentFlatLinear (I := I) g x α (α - β) -
              cotangentFlatLinear (I := I) g x β (α - β) := rfl
        _ = 0 := sub_eq_zero.mpr h_eval
    have hzero :
        g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) = 0 := by
      simpa [cotangentFlatLinear, cotangentInner] using hdiff
    exact (lt_irrefl (0 : Real)) (hzero ▸ hpos)
  apply cotangentSharpLinear_injective (I := I) g x
  have hdiff :
      cotangentSharpLinear (I := I) g x α -
        cotangentSharpLinear (I := I) g x β = 0 := by
    have hmap :
        cotangentSharpLinear (I := I) g x (α - β) =
          cotangentSharpLinear (I := I) g x α -
            cotangentSharpLinear (I := I) g x β :=
      map_sub (cotangentSharpLinear (I := I) g x) α β
    rwa [hmap] at hsub
  exact sub_eq_zero.mp hdiff

/-- Metric data on `T_x^*M` induced by the tangent Riemannian metric.

This is the pullback of the tangent metric along the sharp map
`T_x^*M -> T_xM`. -/
def cotangentMetricData (g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) :=
  MetricFiberData.ofFlat
    (cotangentFlatLinear (I := I) g x)
    (cotangentFlatLinear_injective (I := I) g x)
    (by
      intro α β
      change g.inner x
          (cotangentSharpLinear (I := I) g x α)
          (cotangentSharpLinear (I := I) g x β) =
        g.inner x
          (cotangentSharpLinear (I := I) g x β)
          (cotangentSharpLinear (I := I) g x α)
      exact g.symm x _ _)
    (by
      intro α
      by_cases hα : cotangentSharpLinear (I := I) g x α = 0
      · change 0 <=
          g.inner x
            (cotangentSharpLinear (I := I) g x α)
            (cotangentSharpLinear (I := I) g x α)
        rw [hα]
        simp
      · exact le_of_lt (g.pos x (cotangentSharpLinear (I := I) g x α) hα))

/-- The packaged cotangent metric computes the sharp-definition inner product. -/
theorem cotangentMetricData_inner
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      cotangentInner (I := I) g x α β := by
  rfl

/-- The inverse Gram-matrix predicate for an indexed finite family of
tangent vectors.

This is intentionally not used as a hypothesis for tensor coordinate
formulas: an arbitrary finite family with an inverse Gram matrix on its span
does not by itself give a basis of the tangent fiber. Use
`MetricInverseInBasis` for coordinate identities. -/
def MetricInverseOnFiniteFrameGram {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (frame k) (frame j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i) (frame k) * gInv k j) =
        (if i = j then 1 else 0)

/-- A basis inverse-metric predicate at one point. This is the correct
hypothesis for coordinate formulas: the indexed vectors must span the tangent
fiber, not just have an invertible Gram matrix on their own span. -/
def MetricInverseInBasis {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (basis k) (basis j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (basis i) (basis k) * gInv k j) =
        (if i = j then 1 else 0)

/-- Inverse-metric components in a basis are symmetric. -/
theorem invMetric_symm {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    forall i j : Idx, gInv i j = gInv j i := by
  classical
  let A : Matrix Idx Idx Real := fun i j => gInv i j
  let G : Matrix Idx Idx Real := fun i j => g.inner x (basis i) (basis j)
  have hAG : A * G = 1 := by
    ext i j
    simpa [A, G, Matrix.mul_apply] using (hinv i j).1
  have hGA : G * A = 1 := by
    ext i j
    simpa [A, G, Matrix.mul_apply] using (hinv i j).2
  have hGt : Matrix.transpose G = G := by
    ext i j
    simpa [G] using g.symm x (basis j) (basis i)
  have hAtG : Matrix.transpose A * G = 1 := by
    calc
      Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
      _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hGA]; simp
  have hAt : Matrix.transpose A = A := by
    calc
      Matrix.transpose A = Matrix.transpose A * 1 := by simp
      _ = Matrix.transpose A * (G * A) := by rw [hGA]
      _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
      _ = 1 * A := by rw [hAtG]
      _ = A := by simp
  intro i j
  have hentry := congrArg (fun B : Matrix Idx Idx Real => B j i) hAt
  simpa [A] using hentry

/-- Raising a covector is inverse to lowering by the metric. -/
theorem cotangentSharp_inner
    (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x α) X =
      cotangentToDual (I := I) α X := by
  have h :=
    congrArg
      (fun L : Module.Dual Real (TangentSpace I x) => L X)
      ((tangentMetricData (I := I) g x).metric.flat.apply_symm_apply
        (cotangentToDual (I := I) α))
  change
    (tangentMetricData (I := I) g x).metric.flat
        ((tangentMetricData (I := I) g x).metric.sharp
          (cotangentToDual (I := I) α)) X =
      cotangentToDual (I := I) α X
  exact h

/-- Fiberwise evaluation form of `cotangentSharp_inner`.

This is the convenient rewrite for moving between the sharped tangent field and
the original one-form slot evaluation. -/
theorem cotangentSharp_inner_eval
    (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    g.inner x (cotangentSharp (I := I) g x α) X =
      α (fun _ : Fin 1 => X) := by
  rw [cotangentSharp_inner, cotangentToDual_apply]

/-- Two tangent vectors are equal if they have the same metric pairing with a
basis. -/
theorem eq_of_inner_basis_eq
    {Idx : Type*} [Finite Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {X Y : TangentSpace I x}
    (h : forall i : Idx, g.inner x X (basis i) = g.inner x Y (basis i)) :
    X = Y := by
  letI : Fintype Idx := Fintype.ofFinite Idx
  apply tangentFlatLinear_injective (I := I) g x
  ext Z
  have hcoord (L : TangentSpace I x →ₗ[Real] Real) :
      L Z = ∑ i : Idx, basis.repr Z i • L (basis i) := by
    conv_lhs => rw [← basis.sum_repr Z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  calc
    tangentFlatLinear (I := I) g x X Z
        = ∑ i : Idx, basis.repr Z i • tangentFlatLinear (I := I) g x X (basis i) :=
          hcoord (tangentFlatLinear (I := I) g x X)
    _ = ∑ i : Idx, basis.repr Z i • tangentFlatLinear (I := I) g x Y (basis i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [tangentFlatLinear_apply, tangentFlatLinear_apply, h i]
    _ = tangentFlatLinear (I := I) g x Y Z := by
          exact (hcoord (tangentFlatLinear (I := I) g x Y)).symm

/-- Coordinate reconstruction of the raised covector. -/
theorem cotangentSharp_eq_sum_inv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharp (I := I) g x β =
      ∑ i : Idx,
        (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
          basis i := by
  apply eq_of_inner_basis_eq (I := I) g x basis
  intro l
  calc
    g.inner x (cotangentSharp (I := I) g x β) (basis l)
        = cotangentToDual (I := I) β (basis l) := by
          rw [cotangentSharp_inner]
    _ = ∑ j : Idx, (if l = j then 1 else 0) *
          cotangentToDual (I := I) β (basis j) := by
          simp
    _ = ∑ j : Idx,
          (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
            cotangentToDual (I := I) β (basis j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [(hinv l j).2]
    _ = ∑ i : Idx,
          (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) *
            g.inner x (basis i) (basis l) := by
          calc
            (∑ j : Idx,
                (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
                  cotangentToDual (I := I) β (basis j))
                = ∑ j : Idx, ∑ i : Idx,
                    (g.inner x (basis l) (basis i) * gInv i j) *
                      cotangentToDual (I := I) β (basis j) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [Finset.sum_mul]
            _ = ∑ i : Idx, ∑ j : Idx,
                    (g.inner x (basis l) (basis i) * gInv i j) *
                      cotangentToDual (I := I) β (basis j) := by
                    rw [Finset.sum_comm]
            _ = ∑ i : Idx,
                  (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) *
                    g.inner x (basis i) (basis l) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [g.symm x (basis l) (basis i)]
                    ring
    _ = g.inner x
          (∑ i : Idx,
            (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
              basis i)
          (basis l) := by
          simp [map_sum]

/-- Coordinate formula for the cotangent metric in a basis. -/
theorem cotangentInner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  calc
    cotangentInner (I := I) g x α β
        = g.inner x (cotangentSharp (I := I) g x α)
            (cotangentSharp (I := I) g x β) := rfl
    _ = cotangentToDual (I := I) α (cotangentSharp (I := I) g x β) := by
          rw [cotangentSharp_inner]
    _ = cotangentToDual (I := I) α
          (∑ i : Idx,
            (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) •
              basis i) := by
          rw [cotangentSharp_eq_sum_inv (I := I) g x basis gInv hinv β]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * cotangentToDual (I := I) α (basis i) *
            cotangentToDual (I := I) β (basis j) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul]
          change (∑ j : Idx, gInv i j * cotangentToDual (I := I) β (basis j)) *
              cotangentToDual (I := I) α (basis i) =
            ∑ j : Idx,
              gInv i j * cotangentToDual (I := I) α (basis i) *
                cotangentToDual (I := I) β (basis j)
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          change (gInv i j * cotangentToDual (I := I) β (basis j)) *
              cotangentToDual (I := I) α (basis i) =
            gInv i j * cotangentToDual (I := I) α (basis i) *
              cotangentToDual (I := I) β (basis j)
          ring

/-- Coordinate formula for the packaged cotangent metric. -/
theorem cotangentMetricData_inner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  rw [cotangentMetricData_inner, cotangentInner_eq_coord (I := I) g x basis gInv hinv]

end

end Tensor0SBundle
