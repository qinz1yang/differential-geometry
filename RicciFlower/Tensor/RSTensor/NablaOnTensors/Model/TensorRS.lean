import RicciFlower.Tensor.RSTensor.NablaOnTensors.Model.Christoffel

/-!
# Model-space covariant derivative for mixed tensors
-/
namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

/-!
## Implementation layer: model-space tensor formula

These definitions are the fixed-vector-space formulas used after trivializing
the tensor bundle in a chart.  They are deliberately lower-level than
`nabla0SFun` / `nablaRSFun`.
-/

/-- Pointwise model formula for the covariant derivative of a covariant tensor.

The input `dα_X` is the first-order derivative of the tensor components in the
direction `X`, while `ΓX` is the connection endomorphism acting on each input
slot. -/
theorem fderivWithin_tensorRSModel_eval_slots {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => (T z (β z)) (fun a : Fin s => V a z)) u y Xy =
      ((fderivWithin 𝕜 T u y Xy) (β y)) (fun a : Fin s => V a y) +
        (T y (fderivWithin 𝕜 β u y Xy)) (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          (T y (β y)) (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
  classical
  let α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun z => T z (β z)
  have hα : DifferentiableWithinAt 𝕜 α u y := hT.clm_apply hβ
  have hslots := fderivWithin_tensor0SModel_eval_slots
    (𝕜 := 𝕜) (E := E) (s := s) α V u y Xy hα hV hu
  have hαderiv :
      fderivWithin 𝕜 α u y =
        (T y).comp (fderivWithin 𝕜 β u y) +
          (fderivWithin 𝕜 T u y).flip (β y) := by
    simpa [α] using fderivWithin_clm_apply (𝕜 := 𝕜) (s := u) (x := y) hu hT hβ
  rw [hslots, hαderiv]
  simp [α, add_assoc, add_comm]

/-- Component of a model mixed tensor in a fixed basis.

This is the model-space analogue of `componentRS`, used before a manifold
fiber has been reconstructed. -/
noncomputable def tensorRSModelComp {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d) (lower : Fin s → Fin d) : 𝕜 :=
  (T ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
    (fun a : Fin s => basis (lower a))

/-- Differentiability of a fixed-basis mixed tensor component. -/
theorem differentiableWithinAt_tensorRSModelComp {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (T : E → TensorRSModel r s 𝕜 E)
    (u : Set E) (y : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (upper : Fin r → Fin d) (lower : Fin s → Fin d) :
    DifferentiableWithinAt 𝕜
      (fun z => tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper lower)
      u y := by
  let β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r :=
    fun _ => (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper
  let α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun z => T z (β z)
  have hβ : DifferentiableWithinAt 𝕜 β u y := differentiableWithinAt_const _
  have hα : DifferentiableWithinAt 𝕜 α u y := hT.clm_apply hβ
  simpa [tensorRSModelComp, α, β] using
    hα.continuousMultilinear_apply_const (fun a : Fin s => basis (lower a))

/-- Fixed-basis model mixed-tensor components commute with `fderivWithin`. -/
theorem fderivWithin_tensorRSModelComp {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (T : E → TensorRSModel r s 𝕜 E)
    (u : Set E) (y Y : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hu : UniqueDiffWithinAt 𝕜 u y)
    (upper : Fin r → Fin d) (lower : Fin s → Fin d) :
    fderivWithin 𝕜
        (fun z =>
          tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper lower)
        u y Y =
      tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
        (fderivWithin 𝕜 T u y Y) upper lower := by
  have h := fderivWithin_tensorRSModel_eval_slots
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    T
    (fun _ : E =>
      (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
    (fun a : Fin s => fun _ : E => basis (lower a))
    u y Y hT (differentiableWithinAt_const _)
    (fun _ => differentiableWithinAt_const _) hu
  have hzero :
      (∑ x : Fin s,
        ((T y) ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
          (Function.update (fun a : Fin s => basis (lower a)) x 0)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    exact ((T y) ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)).map_coord_zero x (by simp)
  simpa [tensorRSModelComp, hzero] using h

/-- Component `A^k_{ij}` of a model `(1,2)` tensor.

Here `A` represents a connection difference. The convention matches
`connectionEndomorphismCoeff basis ΓX j k = Γ^k_j`: the first two arguments are
the lower slots and the third argument is the upper slot. -/
noncomputable def connDiffCoeffModel {d : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (A : TensorRSModel 1 2 𝕜 E)
    (i j k : Fin d) : 𝕜 :=
  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis A
    (fun _ : Fin 1 => k)
    (fun q : Fin 2 => if q = 0 then i else j)

/-- Component of the model connection-difference action `A ⋄ T`.

The first lower slot of the output is the action direction.  If
`lower : Fin (s + 1) → Fin d`, then `lower 0` is the action slot and
`lower ∘ Fin.succ` are the original lower slots of `T`. -/
noncomputable def connActRSModelComp {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (A : TensorRSModel 1 2 𝕜 E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d) (lower : Fin (s + 1) → Fin d) : 𝕜 :=
  let X : Fin d := lower 0
  let tail : Fin s → Fin d := fun a => lower a.succ
  (∑ a : Fin r, ∑ k : Fin d,
      connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis A X k (upper a) *
        tensorRSModelComp (𝕜 := 𝕜) (E := E) basis T
          (Function.update upper a k) tail)
    -
    (∑ c : Fin s, ∑ k : Fin d,
      connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis A X (tail c) k *
        tensorRSModelComp (𝕜 := 𝕜) (E := E) basis T upper
          (Function.update (fun q : Fin s => tail q) c k))

/-- Raw fixed-chart scalar Leibniz rule for the component formula behind the
connection-difference action.

This is deliberately a model-component theorem, not a tensor-field product rule:
it differentiates the finite scalar expression used to reconstruct the action
components. -/
theorem fderivWithin_connActRSModelComp {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (A : E → TensorRSModel 1 2 𝕜 E)
    (T : E → TensorRSModel r s 𝕜 E)
    (u : Set E) (y Y : E)
    (hA : DifferentiableWithinAt 𝕜 A u y)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hu : UniqueDiffWithinAt 𝕜 u y)
    (upper : Fin r → Fin d) (lower : Fin (s + 1) → Fin d) :
    fderivWithin 𝕜
        (fun z =>
          connActRSModelComp (𝕜 := 𝕜) (E := E) basis (A z) (T z) upper lower)
        u y Y =
      connActRSModelComp (𝕜 := 𝕜) (E := E) basis
        (fderivWithin 𝕜 A u y Y) (T y) upper lower
      +
      connActRSModelComp (𝕜 := 𝕜) (E := E) basis
        (A y) (fderivWithin 𝕜 T u y Y) upper lower := by
  classical
  let X : Fin d := lower 0
  let tail : Fin s → Fin d := fun a => lower a.succ
  have hAcomp (i j k : Fin d) :
      DifferentiableWithinAt 𝕜
        (fun z => connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) i j k)
        u y := by
    simpa [connDiffCoeffModel] using
      differentiableWithinAt_tensorRSModelComp (𝕜 := 𝕜) (E := E) basis A u y hA
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j)
  have hTcomp (upper' : Fin r → Fin d) (lower' : Fin s → Fin d) :
      DifferentiableWithinAt 𝕜
        (fun z => tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper' lower')
        u y :=
    differentiableWithinAt_tensorRSModelComp (𝕜 := 𝕜) (E := E) basis T u y hT
      upper' lower'
  have hAderiv (i j k : Fin d) :
      fderivWithin 𝕜
        (fun z => connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) i j k)
        u y Y =
        connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
          (fderivWithin 𝕜 A u y Y) i j k := by
    simpa [connDiffCoeffModel] using
      fderivWithin_tensorRSModelComp (𝕜 := 𝕜) (E := E) basis A u y Y hA hu
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j)
  have hTderiv (upper' : Fin r → Fin d) (lower' : Fin s → Fin d) :
      fderivWithin 𝕜
        (fun z => tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper' lower')
        u y Y =
        tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
          (fderivWithin 𝕜 T u y Y) upper' lower' :=
    fderivWithin_tensorRSModelComp (𝕜 := 𝕜) (E := E) basis T u y Y hT hu
      upper' lower'
  let Up : TensorRSModel 1 2 𝕜 E → TensorRSModel r s 𝕜 E → 𝕜 :=
    fun A0 T0 =>
      ∑ a : Fin r, ∑ k : Fin d,
        connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis A0 X k (upper a) *
          tensorRSModelComp (𝕜 := 𝕜) (E := E) basis T0
            (Function.update upper a k) tail
  let Lo : TensorRSModel 1 2 𝕜 E → TensorRSModel r s 𝕜 E → 𝕜 :=
    fun A0 T0 =>
      ∑ c : Fin s, ∑ k : Fin d,
        connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis A0 X (tail c) k *
          tensorRSModelComp (𝕜 := 𝕜) (E := E) basis T0 upper
            (Function.update (fun q : Fin s => tail q) c k)
  have hUpDiff :
      DifferentiableWithinAt 𝕜 (fun z => Up (A z) (T z)) u y := by
    dsimp [Up]
    exact DifferentiableWithinAt.fun_sum fun a _ =>
      DifferentiableWithinAt.fun_sum fun k _ =>
        (hAcomp X k (upper a)).mul (hTcomp (Function.update upper a k) tail)
  have hLoDiff :
      DifferentiableWithinAt 𝕜 (fun z => Lo (A z) (T z)) u y := by
    dsimp [Lo]
    exact DifferentiableWithinAt.fun_sum fun c _ =>
      DifferentiableWithinAt.fun_sum fun k _ =>
        (hAcomp X (tail c) k).mul
          (hTcomp upper (Function.update (fun q : Fin s => tail q) c k))
  have hUp :
      (fderivWithin 𝕜 (fun z => Up (A z) (T z)) u y) Y =
        Up (fderivWithin 𝕜 A u y Y) (T y) +
          Up (A y) (fderivWithin 𝕜 T u y Y) := by
    dsimp [Up]
    have houter :
        fderivWithin 𝕜
          (fun z : E =>
            ∑ a : Fin r, ∑ k : Fin d,
              connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
                tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                  (Function.update upper a k) tail)
          u y =
        ∑ a : Fin r,
          fderivWithin 𝕜
            (fun z : E =>
              ∑ k : Fin d,
                connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
                  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                    (Function.update upper a k) tail)
            u y := by
      exact fderivWithin_fun_sum (𝕜 := 𝕜) (s := u) (x := y)
        (u := Finset.univ)
        (A := fun a : Fin r => fun z : E =>
          ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                (Function.update upper a k) tail)
        hu (fun a _ =>
          DifferentiableWithinAt.fun_sum fun k _ =>
            (hAcomp X k (upper a)).mul
              (hTcomp (Function.update upper a k) tail))
    have hinner (a : Fin r) :
        (fderivWithin 𝕜
          (fun z : E =>
            ∑ k : Fin d,
              connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
                tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                  (Function.update upper a k) tail)
          u y) Y =
        ∑ k : Fin d,
          (connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 A u y Y) X k (upper a) *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T y)
              (Function.update upper a k) tail +
          connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A y) X k (upper a) *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 T u y Y) (Function.update upper a k) tail) := by
      have hinnerSum :
          fderivWithin 𝕜
            (fun z : E =>
              ∑ k : Fin d,
                connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
                  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                    (Function.update upper a k) tail)
            u y =
          ∑ k : Fin d,
            fderivWithin 𝕜
              (fun z : E =>
                connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
                  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                    (Function.update upper a k) tail)
              u y := by
        exact fderivWithin_fun_sum (𝕜 := 𝕜) (s := u) (x := y)
          (u := Finset.univ)
          (A := fun k : Fin d => fun z : E =>
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                (Function.update upper a k) tail)
          hu (fun k _ =>
            (hAcomp X k (upper a)).mul
              (hTcomp (Function.update upper a k) tail))
      rw [hinnerSum]
      simp only [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [fderivWithin_fun_mul hu
        (hAcomp X k (upper a)) (hTcomp (Function.update upper a k) tail)]
      simp [hAderiv, hTderiv, mul_comm]
      ring
    calc
      (fderivWithin 𝕜
        (fun z : E =>
          ∑ a : Fin r, ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                (Function.update upper a k) tail)
        u y) Y
          = ∑ a : Fin r,
              (fderivWithin 𝕜
                (fun z : E =>
                  ∑ k : Fin d,
                    connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X k (upper a) *
                      tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z)
                        (Function.update upper a k) tail)
                u y) Y := by
            rw [houter]
            simp
      _ = ∑ a : Fin r, ∑ k : Fin d,
            (connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
                (fderivWithin 𝕜 A u y Y) X k (upper a) *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T y)
                (Function.update upper a k) tail +
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A y) X k (upper a) *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
                (fderivWithin 𝕜 T u y Y) (Function.update upper a k) tail) := by
            exact Finset.sum_congr rfl fun a _ => hinner a
      _ = (∑ a : Fin r, ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 A u y Y) X k (upper a) *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T y)
              (Function.update upper a k) tail) +
          (∑ a : Fin r, ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A y) X k (upper a) *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 T u y Y) (Function.update upper a k) tail) := by
            simp [Finset.sum_add_distrib]
  have hLo :
      (fderivWithin 𝕜 (fun z => Lo (A z) (T z)) u y) Y =
        Lo (fderivWithin 𝕜 A u y Y) (T y) +
          Lo (A y) (fderivWithin 𝕜 T u y Y) := by
    dsimp [Lo]
    have houter :
        fderivWithin 𝕜
          (fun z : E =>
            ∑ c : Fin s, ∑ k : Fin d,
              connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
                tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                  (Function.update (fun q : Fin s => tail q) c k))
          u y =
        ∑ c : Fin s,
          fderivWithin 𝕜
            (fun z : E =>
              ∑ k : Fin d,
                connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
                  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                    (Function.update (fun q : Fin s => tail q) c k))
            u y := by
      exact fderivWithin_fun_sum (𝕜 := 𝕜) (s := u) (x := y)
        (u := Finset.univ)
        (A := fun c : Fin s => fun z : E =>
          ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                (Function.update (fun q : Fin s => tail q) c k))
        hu (fun c _ =>
          DifferentiableWithinAt.fun_sum fun k _ =>
            (hAcomp X (tail c) k).mul
              (hTcomp upper (Function.update (fun q : Fin s => tail q) c k)))
    have hinner (c : Fin s) :
        (fderivWithin 𝕜
          (fun z : E =>
            ∑ k : Fin d,
              connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
                tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                  (Function.update (fun q : Fin s => tail q) c k))
          u y) Y =
        ∑ k : Fin d,
          (connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 A u y Y) X (tail c) k *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T y) upper
              (Function.update (fun q : Fin s => tail q) c k) +
          connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A y) X (tail c) k *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 T u y Y) upper
              (Function.update (fun q : Fin s => tail q) c k)) := by
      have hinnerSum :
          fderivWithin 𝕜
            (fun z : E =>
              ∑ k : Fin d,
                connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
                  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                    (Function.update (fun q : Fin s => tail q) c k))
            u y =
          ∑ k : Fin d,
            fderivWithin 𝕜
              (fun z : E =>
                connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
                  tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                    (Function.update (fun q : Fin s => tail q) c k))
              u y := by
        exact fderivWithin_fun_sum (𝕜 := 𝕜) (s := u) (x := y)
          (u := Finset.univ)
          (A := fun k : Fin d => fun z : E =>
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                (Function.update (fun q : Fin s => tail q) c k))
          hu (fun k _ =>
            (hAcomp X (tail c) k).mul
              (hTcomp upper (Function.update (fun q : Fin s => tail q) c k)))
      rw [hinnerSum]
      simp only [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [fderivWithin_fun_mul hu
        (hAcomp X (tail c) k)
        (hTcomp upper (Function.update (fun q : Fin s => tail q) c k))]
      simp [hAderiv, hTderiv, mul_comm]
      ring
    calc
      (fderivWithin 𝕜
        (fun z : E =>
          ∑ c : Fin s, ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                (Function.update (fun q : Fin s => tail q) c k))
        u y) Y
          = ∑ c : Fin s,
              (fderivWithin 𝕜
                (fun z : E =>
                  ∑ k : Fin d,
                    connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A z) X (tail c) k *
                      tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T z) upper
                        (Function.update (fun q : Fin s => tail q) c k))
                u y) Y := by
            rw [houter]
            simp
      _ = ∑ c : Fin s, ∑ k : Fin d,
            (connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
                (fderivWithin 𝕜 A u y Y) X (tail c) k *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T y) upper
                (Function.update (fun q : Fin s => tail q) c k) +
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A y) X (tail c) k *
              tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
                (fderivWithin 𝕜 T u y Y) upper
                (Function.update (fun q : Fin s => tail q) c k)) := by
            exact Finset.sum_congr rfl fun c _ => hinner c
      _ = (∑ c : Fin s, ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 A u y Y) X (tail c) k *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis (T y) upper
              (Function.update (fun q : Fin s => tail q) c k)) +
          (∑ c : Fin s, ∑ k : Fin d,
            connDiffCoeffModel (𝕜 := 𝕜) (E := E) basis (A y) X (tail c) k *
            tensorRSModelComp (𝕜 := 𝕜) (E := E) basis
              (fderivWithin 𝕜 T u y Y) upper
              (Function.update (fun q : Fin s => tail q) c k)) := by
            simp [Finset.sum_add_distrib]
  have hmain :
      (fderivWithin 𝕜 (fun z => Up (A z) (T z) - Lo (A z) (T z)) u y) Y =
        (Up (fderivWithin 𝕜 A u y Y) (T y) -
          Lo (fderivWithin 𝕜 A u y Y) (T y)) +
        (Up (A y) (fderivWithin 𝕜 T u y Y) -
          Lo (A y) (fderivWithin 𝕜 T u y Y)) := by
    rw [fderivWithin_fun_sub hu hUpDiff hLoDiff]
    simp [hUp, hLo]
    ring
  simpa [connActRSModelComp, Up, Lo, X, tail] using hmain

/-- Pointwise model formula for the covariant derivative of a mixed `(r,s)` tensor.

In the `Hom((0,r),(0,s))` model the connection acts on output covariant slots
with a minus sign and on input covariant slots with a plus sign. For `r = 1`,
`s = 0`, this recovers the usual `D Y(X) + Γ_X Y` vector-field formula under
the vector-as-`Hom(V*, 𝕜)` identification. -/
def covariantDeriv_tensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) := by
  rfl

/-- The model-space mixed covariant derivative is additive in the tensor field
and its directional component derivative. -/
theorem covariantDeriv_tensorRSModelAt_add (r s : ℕ)
    (dT_X dU_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T U : TensorRSModel r s 𝕜 E) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s (dT_X + dU_X) ΓX (T + U) =
      covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T +
        covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dU_X ΓX U := by
  unfold covariantDeriv_tensorRSModelAt
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  abel

/-- The model-space mixed covariant derivative is homogeneous under constant
scalar multiplication of the tensor field and its directional component
derivative. -/
theorem covariantDeriv_tensorRSModelAt_smul (r s : ℕ)
    (c : 𝕜) (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s (c • dT_X) ΓX (c • T) =
      c • covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T := by
  unfold covariantDeriv_tensorRSModelAt
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  module

/-- Evaluation form of the model-space covariant derivative of an `(r,s)`
tensor.

In the `Hom((0,r),(0,s))` model, the connection correction subtracts from the
output covariant slots and adds through the input covariant slots. -/
theorem covariantDeriv_tensorRSModelAt_eval (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) r) (v : Fin s → E) :
    (covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T β) v =
      (dT_X β) v -
        ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX) (T β)) v +
        (T ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) β)) v := by
  simp [covariantDeriv_tensorRSModelAt, sub_eq_add_neg, add_assoc]

/-- Model covariant differentiation commutes with the zero-upper-slot
embedding of covariant tensors.

This is the fixed-vector-space form of the naturality needed to use mixed
tensor derivative estimates on covariant tensors. -/
theorem covariantDeriv_tensorRSModelAt_toRS0 (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) 0 s
        (Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E) dα_X) ΓX
        (Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E) α) =
      Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E)
        (covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α) := by
  ext c slots
  rw [covariantDeriv_tensorRSModelAt_eval]
  rw [Tensor0SModel.toRS0_apply, Tensor0SModel.toRS0_apply]
  have hcorr0 : (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) 0 ΓX) c = 0 := by
    rw [lieDeriv_correctionL_apply, lieDeriv_correction_zero]
  rw [hcorr0]
  simp [Tensor0SModel.toRS0_apply, sub_eq_add_neg, add_comm]

def covariantDeriv_tensorRSModel (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderiv 𝕜 T x (X x)) (ΓX x) (T x)

/-- Within-set variant of `covariantDeriv_tensorRSModel`. -/
def covariantDeriv_tensorRSModelWithin (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (u : Set E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x)

/-- Within-set model covariant differentiation commutes with the zero-upper-slot
embedding, provided the ordinary derivative term is governed by the usual
within-set chain rule. -/
theorem covariantDeriv_tensorRSModelWithin_toRS0 (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E)
    (hα : DifferentiableWithinAt 𝕜 α u x)
    (hu : UniqueDiffWithinAt 𝕜 u x) :
    covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) 0 s X ΓX
        (fun y => Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E) (α y)) u x =
      Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E)
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x) := by
  let L : Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜] TensorRSModel 0 s 𝕜 E :=
    Tensor0SModel.toRS0L (𝕜 := 𝕜) (E := E)
  have hcomp :
      fderivWithin 𝕜 (fun y => L (α y)) u x =
        L.comp (fderivWithin 𝕜 α u x) := by
    have hlin : DifferentiableAt 𝕜 (fun T => L T) (α x) := L.differentiableAt
    have hcomp0 :=
      fderivWithin_comp (x := x) (f := α) (g := fun T => L T)
        (s := u) (t := Set.univ)
        (by simpa using hlin.differentiableWithinAt)
        hα (by intro z hz; simp) hu
    rw [L.fderivWithin (s := Set.univ) (x := α x) uniqueDiffWithinAt_univ] at hcomp0
    simpa [L, Function.comp_def] using hcomp0
  have hD :
      fderivWithin 𝕜
          (fun y => Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E) (α y)) u x (X x) =
        Tensor0SModel.toRS0 (𝕜 := 𝕜) (E := E)
          (fderivWithin 𝕜 α u x (X x)) := by
    change (fderivWithin 𝕜 (fun y => L (α y)) u x) (X x) =
      L ((fderivWithin 𝕜 α u x) (X x))
    rw [hcomp]
    rfl
  unfold covariantDeriv_tensorRSModelWithin covariantDeriv_tensor0SModelWithin
  rw [hD]
  exact covariantDeriv_tensorRSModelAt_toRS0 (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

/-- Hom-derivation form of the mixed model covariant derivative. Evaluating
`∇_X T` on a variable input covariant tensor and variable output slots equals
the directional derivative of the scalar evaluation, minus the covariant
derivative of the input and minus the covariant derivatives of the output
slots. -/
theorem covariantDeriv_tensorRSModelWithin_eval_derivation {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (u : Set E) (y : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y (β y)) (fun a : Fin s => V a y)
      =
        fderivWithin 𝕜
          (fun z : E => (T z (β z)) (fun a : Fin s => V a z))
          u y (X y)
        - (T y
          (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
            r X ΓX β u y))
          (fun a : Fin s => V a y)
        - ∑ a : Fin s,
          (T y (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y))) := by
  classical
  have hprod := fderivWithin_tensorRSModel_eval_slots
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    T β V u y (X y) hT hβ hV hu
  rw [covariantDeriv_tensorRSModelWithin]
  rw [covariantDeriv_tensorRSModelAt_eval]
  rw [hprod]
  have hβcov :
      ((T y)
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
          r X ΓX β u y)) (fun a : Fin s => V a y) =
        ((T y) (fderivWithin 𝕜 β u y (X y))) (fun a : Fin s => V a y) -
          ((T y) ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y)) (β y)))
            (fun a : Fin s => V a y) := by
    simp [covariantDeriv_tensor0SModelWithin, covariantDeriv_tensor0SModelAt,
      lieDeriv_correctionL_apply]
  have hCorrS :
      ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) ((T y) (β y)))
          (fun a : Fin s => V a y) =
        ∑ a : Fin s,
          ((T y) (β y))
            (Function.update (fun b : Fin s => V b y) a (ΓX y (V a y))) := by
    exact lieDeriv_correctionL_apply_slots (𝕜 := 𝕜) (E := E)
      (s := s) (ΓX y) ((T y) (β y)) (fun a : Fin s => V a y)
  have hsum :
      (∑ a : Fin s,
          ((T y) (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y)))) =
        (∑ a : Fin s,
          ((T y) (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y)))) +
        ∑ a : Fin s,
          ((T y) (β y))
            (Function.update (fun b : Fin s => V b y) a (ΓX y (V a y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact ((T y) (β y)).map_update_add
      (fun b : Fin s => V b y) a
      (fderivWithin 𝕜 (V a) u y (X y)) (ΓX y (V a y))
  rw [hβcov, hCorrS, hsum]
  abel

section ChristoffelModelRS

private theorem tensor0SModel_eval_update_basis_sum_modelRS {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Fin d, basis.coord k w *
        α (Function.update v i (basis k)) := by
  classical
  have hw : w = ∑ k : Fin d, basis.coord k w • basis k := by
    exact (basis.sum_repr w).symm
  calc
    α (Function.update v i w) =
        α (Function.update v i (∑ k : Fin d, basis.coord k w • basis k)) := by
      exact congrArg (fun z => α (Function.update v i z)) hw
    _ = ∑ k : Fin d,
        α (Function.update v i (basis.coord k w • basis k)) := by
      have h := α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset (Fin d)) i (fun k : Fin d => basis.coord k w • basis k) v
      simpa using h
    _ = ∑ k : Fin d, basis.coord k w *
        α (Function.update v i (basis k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [α.map_update_smul]
      simp [smul_eq_mul]

private theorem continuousMultilinearMap_basis_apply_basis {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (upper lower : Fin s → Fin d) :
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis s) upper)
        (fun b : Fin s => basis (lower b)) =
      if upper = lower then 1 else 0 := by
  have h := continuousMultilinearMap_basis_repr
    (𝕜 := 𝕜) (F := E) basis s
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis s) upper)
    lower
  simpa [Module.Basis.repr_self, Finsupp.single_apply] using h.symm

private theorem basis_coord_update_sum_comm {d r : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (upper lower : Fin r → Fin d)
    (a : Fin r) :
    (∑ k : Fin d,
        basis.coord k (ΓX (basis (lower a))) *
          (if upper = Function.update lower a k then (1 : 𝕜) else 0)) =
      ∑ k : Fin d,
        basis.coord (upper a) (ΓX (basis k)) *
          (if Function.update upper a k = lower then (1 : 𝕜) else 0) := by
  classical
  by_cases hout : ∀ b : Fin r, b ≠ a → upper b = lower b
  · have hleft_update : upper = Function.update lower a (upper a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Function.update, hb, hout b hb]
    have hright_update : Function.update upper a (lower a) = lower := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Function.update, hb, hout b hb]
    have hleft :
        (∑ k : Fin d,
          basis.coord k (ΓX (basis (lower a))) *
            (if upper = Function.update lower a k then (1 : 𝕜) else 0)) =
          basis.coord (upper a) (ΓX (basis (lower a))) := by
      rw [Finset.sum_eq_single (upper a)]
      · rw [if_pos hleft_update]
        simp
      · intro k _ hk
        have hne : upper ≠ Function.update lower a k := by
          intro h
          have ha := congrFun h a
          simp at ha
          exact hk ha.symm
        rw [if_neg hne]
        simp
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    have hright :
        (∑ k : Fin d,
          basis.coord (upper a) (ΓX (basis k)) *
            (if Function.update upper a k = lower then (1 : 𝕜) else 0)) =
          basis.coord (upper a) (ΓX (basis (lower a))) := by
      rw [Finset.sum_eq_single (lower a)]
      · rw [if_pos hright_update]
        simp
      · intro k _ hk
        have hne : Function.update upper a k ≠ lower := by
          intro h
          have ha : k = lower a := by
            simpa using congrFun h a
          exact hk ha
        rw [if_neg hne]
        simp
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [hleft, hright]
  · push Not at hout
    rcases hout with ⟨b, hb, hneq⟩
    have hleft_zero :
        (∑ k : Fin d,
          basis.coord k (ΓX (basis (lower a))) *
            (if upper = Function.update lower a k then (1 : 𝕜) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : upper ≠ Function.update lower a k := by
        intro h
        have hb_eq : upper b = lower b := by
          simpa [Function.update, hb] using congrFun h b
        exact hneq hb_eq
      simp [hne]
    have hright_zero :
        (∑ k : Fin d,
          basis.coord (upper a) (ΓX (basis k)) *
            (if Function.update upper a k = lower then (1 : 𝕜) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : Function.update upper a k ≠ lower := by
        intro h
        have hb_eq : upper b = lower b := by
          simpa [Function.update, hb] using congrFun h b
        exact hneq hb_eq
      simp [hne]
    rw [hleft_zero, hright_zero]

/-- Lower-slot expansion of the connection correction in basis components. -/
theorem lieDeriv_correctionL_apply_basis_slots_expanded {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (lower : Fin s → Fin d) :
    ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX α)
        (fun b : Fin s => basis (lower b))) =
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          α (Function.update
            (fun c : Fin s => basis (lower c))
            b
            (basis k)) := by
  classical
  rw [lieDeriv_correctionL_apply_slots]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [tensor0SModel_eval_update_basis_sum_modelRS basis α
    (fun c : Fin s => basis (lower c)) b (ΓX (basis (lower b)))]
  simp [connectionEndomorphismCoeff]

/-- The connection correction applied to a coordinate-basis covariant tensor.

For a basis covariant tensor with index `upper`, the correction changes the
`a`-th covariant input basis index from `upper a` to `k` with coefficient
`Γ^(upper a)_k`.  With the project convention
`connectionEndomorphismCoeff basis ΓX j k = Γ^k_j`, this is written as
`connectionEndomorphismCoeff basis ΓX k (upper a)`. -/
theorem lieDeriv_correctionL_apply_basisTensor0S {d r : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (upper : Fin r → Fin d) :
    lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX
      ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
    =
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) •
          ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
            (Function.update upper a k)) := by
  classical
  apply (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r).repr.injective
  ext lower
  rw [continuousMultilinearMap_basis_repr]
  simp only [map_sum, map_smul, Module.Basis.repr_self]
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  rw [lieDeriv_correctionL_apply_slots]
  change
    (∑ a : Fin r,
      ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
        (Function.update (fun b : Fin r => basis (lower b)) a (ΓX (basis (lower a))))) =
    ∑ a : Fin r,
      ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (if Function.update upper a k = lower then (1 : 𝕜) else 0)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensor0SModel_eval_update_basis_sum_modelRS basis
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
    (fun b : Fin r => basis (lower b)) a (ΓX (basis (lower a)))]
  simp only [connectionEndomorphismCoeff]
  trans
      ∑ k : Fin d,
        basis.coord k (ΓX (basis (lower a))) *
          (if upper = Function.update lower a k then (1 : 𝕜) else 0)
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    have hslots :
        Function.update (fun b : Fin r => basis (lower b)) a (basis k) =
          fun b : Fin r => basis (Function.update lower a k b) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Function.update, hb]
    rw [hslots, continuousMultilinearMap_basis_apply_basis]
  · exact basis_coord_update_sum_comm basis ΓX upper lower a

/-- Basis-slot Christoffel formula for the model covariant derivative of a
mixed `(r,s)` tensor. -/
theorem covariantDeriv_tensorRSModelAt_apply_basis_slots {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (dT_X : TensorRSModel r s 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    (covariantDeriv_tensorRSModelAt
        (𝕜 := 𝕜) (E := E) r s dT_X ΓX T
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (dT_X
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
        (fun b : Fin s => basis (lower b))
      +
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))
      -
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k)) := by
  classical
  rw [covariantDeriv_tensorRSModelAt_eval]
  have hupper := lieDeriv_correctionL_apply_basisTensor0S
    (𝕜 := 𝕜) (E := E) basis ΓX upper
  have hlower_expanded := lieDeriv_correctionL_apply_basis_slots_expanded
    (𝕜 := 𝕜) (E := E) basis ΓX
    (T ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
    lower
  rw [hupper, hlower_expanded]
  simp only [map_sum, map_smul,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  abel

/-- Subtracting two model covariant derivatives cancels the raw directional
derivative and leaves only the difference of the upper- and lower-slot
connection corrections.  This is the model-space algebra behind the first-order
connection-change formula used in MSM135 Chapter 4, Lemma "Norms of covariant
derivatives of tensors, I". -/
theorem covDerivRS_sub_apply {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (dT_X : TensorRSModel r s 𝕜 E)
    (ΓX ΓX' : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    ((covariantDeriv_tensorRSModelAt
          (𝕜 := 𝕜) (E := E) r s dT_X ΓX T -
        covariantDeriv_tensorRSModelAt
          (𝕜 := 𝕜) (E := E) r s dT_X ΓX' T)
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (((∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))) -
        (∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX' k (upper a) *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))))
      -
      ((∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))) -
        (∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX' (lower b) k *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))))) := by
  classical
  simp only [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [covariantDeriv_tensorRSModelAt_apply_basis_slots basis dT_X ΓX T upper lower]
  rw [covariantDeriv_tensorRSModelAt_apply_basis_slots basis dT_X ΓX' T upper lower]
  abel

/-- Within-set variant of
`covariantDeriv_tensorRSModelAt_apply_basis_slots`. -/
theorem covariantDeriv_tensorRSModelWithin_apply_basis_slots {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (X : E → E)
    (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E)
    (u : Set E)
    (x : E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    (covariantDeriv_tensorRSModelWithin
        (𝕜 := 𝕜) (E := E) r s X ΓX T u x
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (fderivWithin 𝕜 T u x (X x)
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
        (fun b : Fin s => basis (lower b))
      +
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis (ΓX x) k (upper a) *
          (T x
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))
      -
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis (ΓX x) (lower b) k *
          (T x
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k)) := by
  unfold covariantDeriv_tensorRSModelWithin
  exact covariantDeriv_tensorRSModelAt_apply_basis_slots
    (𝕜 := 𝕜) (E := E) basis
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x) upper lower

end ChristoffelModelRS

end ModelCovariantDerivative

end

end TensorLieDeriv
