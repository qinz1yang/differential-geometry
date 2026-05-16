import RicciFlower.Coordinates.NablaComponents.Tensor0S
import RicciFlower.Tensor.RSTensor.Components
import RicciFlower.Tensor.RSTensor.Field
import RicciFlower.Tensor.RSTensor.Basis
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.TensorRS

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate components of mixed tensor covariant derivatives

This file extends the coordinate-frame component API from covariant tensors to
mixed `(r,s)` tensors.  It stays independent of Ricci-flow evolution files and
only bridges the fixed-chart model derivative to the coordinate-frame scalar
component derivative.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Directional derivative of a mixed tensor coordinate-frame component.

The Hom-input tensor is kept constant in the chart centered at `x₀`; this avoids
the moving-center component derivative. -/
def coordDerivRSAt {r s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r x₀ β₀
  mfderiv I 𝓘(𝕜, 𝕜)
    (fun y : M =>
      (T y (β y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
    x₀ (X x₀)

/-- The chart-model derivative term appearing definitionally in `nablaRSFun`. -/
def modelDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let X' := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
    (fun x => X x) (Set.range I)
  let T' : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ T
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  (fderivWithin 𝕜 T'
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀)
      (X' (extChartAt I x₀ x₀))
    β₀)
    (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))

/-- Predicate recording that the fixed-chart model derivative agrees with the
manifold scalar derivative of mixed tensor coordinate components. -/
def ModelDerivEqCoordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x) :
    Prop :=
  forall upper lower,
    modelDerivRSAt (I := I) X x₀ T upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ T upper lower

private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(𝕜, 𝕜)) (c := (0 : 𝕜)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

private theorem extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
        exact mdifferentiableAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I)
                (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

private theorem extDerivFun_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

private theorem extDerivFun_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, 𝕜)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

private theorem coordinateFrameAt_basis_continuousLinearMapAt
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
        𝕜 x ((coordinateFrameAt_basis (I := I) x₀ hx) i) =
      (Module.finBasis 𝕜 E) i := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hxE : x ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, e] using hx
  have hframe :
      (coordinateFrameAt_basis (I := I) x₀ hx) i =
        e.symmL 𝕜 x ((Module.finBasis 𝕜 E) i) := by
    rw [coordinateFrameAt_basis_apply]
    rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
    rfl
  rw [hframe]
  exact e.continuousLinearMapAt_symmL (R := 𝕜) hxE ((Module.finBasis 𝕜 E) i)

private theorem coordinateFrameAt_basis_repr_eq_trivializationAt
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) :
    (coordinateFrameAt_basis (I := I) x₀ hx).repr v =
      (Module.finBasis 𝕜 E).repr
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
          𝕜 x v) := by
  classical
  let b := coordinateFrameAt_basis (I := I) x₀ hx
  let e := Module.finBasis 𝕜 E
  let L := (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
    𝕜 x
  have hLbasis : ∀ i, L (b i) = e i := by
    intro i
    exact coordinateFrameAt_basis_continuousLinearMapAt
      (I := I) x₀ hx i
  have hLv : L v = ∑ i, (b.repr v i) • e i := by
    calc
      L v = L (∑ i, (b.repr v i) • b i) := by
          exact congrArg L (b.sum_repr v).symm
      _ = ∑ i, L ((b.repr v i) • b i) := by
          rw [map_sum]
      _ = ∑ i, (b.repr v i) • L (b i) := by
          simp
      _ = ∑ i, (b.repr v i) • e i := by
          simp [hLbasis]
  rw [hLv]
  ext i
  exact (congrFun (e.repr_sum_self (fun i => b.repr v i)) i).symm

set_option backward.isDefEq.respectTransparency false in
/-- On the coordinate-frame domain, the fixed tensor-bundle basis section
`Tensor0SSpace.constInChart` is the basis tensor of the coordinate local frame.

This is the local-frame/trivialization normalization needed by the mixed
upper-slot contraction product rule. -/
theorem constInChart_basisTensor0S_coordFrame {r : ℕ}
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) :
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) x =
      basisTensor0S (I := I) (coordinateFrameAt_basis (I := I) x₀ hx) upper := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hxE : x ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [Tensor0SSpace.constInChart]
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (F := E) (E := TangentSpace I) x₀ x hxE]
  ext v
  simp [basisTensor0S, tensor0SBasis, continuousMultilinearMapBasis_apply,
    continuousMultilinearMapBasisElem, continuousMultilinearMap_basis,
    continuousMultilinearMap_basisElem, coframeOfBasis,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    coordinateFrameAt_basis_repr_eq_trivializationAt]

/-- Coordinate-frame expansion of evaluating a mixed tensor field on a
covariant input field.

Near `x₀`, the lower coordinate-frame component of `T θ` is the finite
contraction of the coordinate-frame components of `θ` with the fixed-chart
mixed components of `T`. -/
theorem applyInput_coordFrame_eventually {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (θ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (x₀ : M) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (fun y : M =>
        (T y (θ y))
          (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
      =ᶠ[𝓝 x₀]
    (fun y : M =>
      ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        θ y (fun a : Fin r => coordinateFrameAt (I := I) x₀ (upper a) y) *
          (T y
            (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) r x₀
              ((continuousMultilinearMap_basis
                (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) y))
            (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y)) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  have h :=
    Tensor0SBundle.componentRS_apply_input_eq_sum
      (I := I) basis (T y) (θ y) lower
  calc
    (T y (θ y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y)
        = component0S (I := I) basis (T y (θ y)) lower := by
          simp [basis, component0S_apply]
    _ = ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
          component0S (I := I) basis (θ y) upper *
            componentRS (I := I) basis (T y) upper lower := h
    _ = ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        θ y (fun a : Fin r => coordinateFrameAt (I := I) x₀ (upper a) y) *
          (T y
            (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) r x₀
              ((continuousMultilinearMap_basis
                (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) y))
            (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y) := by
          refine Finset.sum_congr rfl fun upper _ => ?_
          have hconst := constInChart_basisTensor0S_coordFrame
            (I := I) (M := M) (r := r) x₀ hy upper
          simp [basis, component0S_apply, componentRS_apply, hconst]

set_option backward.isDefEq.respectTransparency false in
theorem tensorRS_eval_constInChart_coordinateFrame_contMDiffAt {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (T y
          (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r x₀
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) y))
          (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
      x₀ := by
  classical
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis
      (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let βsec : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r p :=
    fun p : M => Tensor0SSpace.constInChart
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ β₀ p
  have hT : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, T p⟩ :
          TotalSpace (TensorRSModel r s 𝕜 E)
            (fun p : M => TensorRSSpace r s I p))) x₀ :=
    (T.contMDiff x₀).of_le (by simp :
      (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, βsec p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
    simpa [βsec, β₀] using
      tensor0SConstInChart_contMDiffAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ β₀
  have hV : ∀ b : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ (lower b) p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro b
    exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) (lower b)
  simpa [βsec, β₀] using
    tensorRS_eval_contMDiffAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (T := fun p : M => T p) (β := βsec)
      (V := fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b)) x₀ hT hβ hV

/-- Coordinate derivative product rule for evaluating a mixed tensor field on a
covariant input field.

This is the first-product producer for upper-slot contractions: differentiating
the coordinate component of `T θ` is the sum of the differentiated probe
components times the mixed tensor components, plus the probe components times
the differentiated mixed tensor components. -/
theorem coordDeriv0SAt_applyInput_eq_sum {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (θ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (x₀ : M) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordDeriv0SAt (I := I) (fun x => X x) x₀
        (fun y : M =>
          tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) (∞ : WithTop ℕ∞) T θ y)
        lower =
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => θ x) upper *
          coordComponentRSAt (I := I) (T x₀) upper lower) +
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        coordComponent0SAt (I := I) (θ x₀) upper *
          coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower) := by
  classical
  let θfun : (Fin r -> CoordinateIdx (𝕜 := 𝕜) E) -> M -> 𝕜 :=
    fun upper y => θ y
      (fun a : Fin r => coordinateFrameAt (I := I) x₀ (upper a) y)
  let βfun : (Fin r -> CoordinateIdx (𝕜 := 𝕜) E) -> M -> 𝕜 :=
    fun upper y =>
      (T y
        (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) r x₀
          ((continuousMultilinearMap_basis
            (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y)
  have hev := applyInput_coordFrame_eventually (I := I) T θ x₀ lower
  unfold coordDeriv0SAt
  change
    extDerivFun (I := I)
      (fun y : M =>
        (tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) (∞ : WithTop ℕ∞) T θ y)
          (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
      x₀ (X x₀) =
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => θ x) upper *
          coordComponentRSAt (I := I) (T x₀) upper lower) +
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
        coordComponent0SAt (I := I) (θ x₀) upper *
          coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower)
  have hderiv_congr :
      extDerivFun (I := I)
        (fun y : M =>
          (tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) (∞ : WithTop ℕ∞) T θ y)
            (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
        x₀ (X x₀) =
      extDerivFun (I := I)
        (fun y : M =>
          ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
            θfun upper y * βfun upper y) x₀ (X x₀) := by
    exact extDerivFun_congr_eventually (I := I) (X x₀) (by
      simpa [θfun, βfun, tensorRSField_applyInput_apply] using hev)
  rw [hderiv_congr]
  have hsum_fun :
      (fun y : M =>
          ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
            θfun upper y * βfun upper y) =
        Finset.univ.sum (fun upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E =>
          fun y : M => θfun upper y * βfun upper y) := by
    funext y
    simp
  rw [hsum_fun]
  rw [extDerivFun_finset_sum (I := I) (t := Finset.univ)
    (f := fun upper y => θfun upper y * βfun upper y) (x := x₀) (v := X x₀)]
  · calc
      (∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
          extDerivFun (I := I) (fun y : M => θfun upper y * βfun upper y)
            x₀ (X x₀))
          =
        ∑ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => θ x) upper *
            coordComponentRSAt (I := I) (T x₀) upper lower +
          coordComponent0SAt (I := I) (θ x₀) upper *
            coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower) := by
          refine Finset.sum_congr rfl fun upper _ => ?_
          rw [extDerivFun_mul (I := I) (f := θfun upper) (g := βfun upper)
        (x := x₀) (v := X x₀)]
          · have hθ0 :
            θfun upper x₀ =
              coordComponent0SAt (I := I) (θ x₀) upper := by
              simp [θfun, coordComponent0SAt, component0S]
            have hβ0 :
            βfun upper x₀ =
              coordComponentRSAt (I := I) (T x₀) upper lower := by
              have hconst := constInChart_basisTensor0S_coordFrame
                (I := I) (M := M) (r := r) x₀
                (coordinateFrameAt_mem (I := I) x₀) upper
              simp [βfun, coordComponentRSAt, componentRS_apply,
                coordinateFrameAt_toBasis, hconst]
            have hdθ :
            extDerivFun (I := I) (θfun upper) x₀ (X x₀) =
              coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => θ x) upper := by
              change (mfderiv I 𝓘(𝕜, 𝕜) (θfun upper) x₀) (X x₀) =
                coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => θ x) upper
              simp [θfun, coordDeriv0SAt]
            have hdβ :
            extDerivFun (I := I) (βfun upper) x₀ (X x₀) =
              coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower := by
              change (mfderiv I 𝓘(𝕜, 𝕜) (βfun upper) x₀) (X x₀) =
                coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
              simp [βfun, coordDerivRSAt]
            rw [hθ0, hβ0, hdθ, hdβ]
            ring
          · exact (tensor0S_eval_coordinateFrame_contMDiffAt
              (I := I) θ x₀ upper).mdifferentiableAt (by simp)
          · exact (tensorRS_eval_constInChart_coordinateFrame_contMDiffAt
              (I := I) T x₀ upper lower).mdifferentiableAt (by simp)
      _ = _ := by
          rw [Finset.sum_add_distrib]
  · intro upper _
    exact ((tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) θ x₀ upper).mdifferentiableAt (by simp)).mul
      ((tensorRS_eval_constInChart_coordinateFrame_contMDiffAt
        (I := I) T x₀ upper lower).mdifferentiableAt (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- At the base point, mixed tensor model components in the fixed
trivialization agree with coordinate-frame components. -/
theorem tensorRSModelAt_coordComponentRSAt {r s : ℕ} (x₀ : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ x₀ T
      ((continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
      (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))
    =
      coordComponentRSAt (I := I) T upper lower := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) :=
    Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := 𝕜) (E := E) r
  unfold tensorRSModelAt
  rw [coordComponentRSAt_apply, componentRS_apply]
  have hx : x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [TensorRSSpace.trivializationAt_basis_coord
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) (r := r) (s := s)
    (bE := Module.finBasis 𝕜 E) hx T upper lower]
  congr 2
  · change
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
          ((continuousMultilinearMap_basis
            (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) =
        basisTensor0S (I := I) (coordinateFrameAt_toBasis (I := I) x₀) upper
    ext v
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    change
      ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper)) v =
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) v
    have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hmodel := congrArg (fun A : Tensor0SModel r 𝕜 E => A v)
      (TensorLieDeriv.tensor0SModelAt_trivializationAt_symm
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
    dsimp at hmodel
    rw [TensorLieDeriv.tensor0SModelAt_apply] at hmodel
    conv at hmodel =>
      lhs
      arg 2
      ext a
      rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
      rw [mfderivWithin_range_extChartAt_symm]
    simpa [Trivialization.symmL_apply, mfderivWithin_range_extChartAt_symm] using hmodel
  · funext b
    have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
    rw [mfderivWithin_range_extChartAt_symm]
    rfl

private theorem model_RS_component_eq_coord_component_comp_eventually {r s : ℕ}
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    let β₀ : Tensor0SModel r 𝕜 E :=
      (continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
    (fun y : E =>
        (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s x₀ T y β₀)
          (fun b => (Module.finBasis 𝕜 E) (lower b))) =ᶠ[
      𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun y : E =>
        (T ((extChartAt I x₀).symm y)
          (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β₀ ((extChartAt I x₀).symm y)))
          (fun b =>
            coordinateFrameAt (I := I) x₀ (lower b)
              ((extChartAt I x₀).symm y))) := by
  intro β₀
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  unfold tensorRSModelInChart tensorRSModelAt Tensor0SSpace.constInChart
  rw [TensorRSSpace.trivializationAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := (extChartAt I x₀).symm y)
    (r := r) (s := s)]
  · congr 2
    funext b
    have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target hy
    have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
    rw [coordinateFrameAt_apply_of_mem (I := I) hy_base (lower b)]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hy_src]
    rfl
  · have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target hy
    simpa [trivializationAt] using hy_src

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-bundle chart derivative used by `nablaRSFun` agrees with the
manifold directional derivative of the corresponding coordinate-frame mixed
component. -/
theorem modelDeriv_eq_coordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x) := by
  classical
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI : NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := inferInstance
  intro upper lower
  let z₀ : E := extChartAt I x₀ x₀
  let S : Set E := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let u : Fin s -> E := fun b => (Module.finBasis 𝕜 E) (lower b)
  let Tchart : E -> TensorRSModel r s 𝕜 E :=
    fun y => tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s x₀ (fun x => T x) y
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    fun x => Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r x₀ β₀ x
  let f : M -> 𝕜 :=
    fun y => (T y (β y))
      (fun b => coordinateFrameAt (I := I) x₀ (lower b) y)
  have hS : S = Set.range I := by
    ext y
    simp [S]
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hzS : z₀ ∈ S := by
    simpa [hS] using hzRange
  have huniq : UniqueDiffWithinAt 𝕜 S z₀ := by
    simpa [hS, z₀] using I.uniqueDiffOn z₀ hzRange
  have hX :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hmodel_eventually :
      (fun y : E => (Tchart y β₀) u) =ᶠ[𝓝[S] z₀]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    have h := model_RS_component_eq_coord_component_comp_eventually
      (I := I) (M := M) (r := r) (s := s) x₀ (fun x => T x) upper lower
    simpa [S, z₀, Tchart, β₀, u, β, f, writtenInExtChartAt] using h
  have hT_model := by
    have h := T.contMDiff x₀
    rw [contMDiffAt_section] at h
    simpa [tensorRSModelAt] using h
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm S z₀ := by
    simpa [S, z₀] using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hT_model_center :
      ContMDiffAt I
        𝓘(𝕜, TensorRSModel r s 𝕜 E)
        (∞ : WithTop ℕ∞)
        (fun x : M =>
          tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s x₀ x (T x))
        ((extChartAt I x₀).symm z₀) := by
    simpa [z₀, extChartAt_to_inv] using hT_model
  have hTchart_cd := by
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(𝕜, E)) (I' := I)
      (I'' := 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (x := z₀) hT_model_center hsymm
    simpa [Tchart, tensorRSModelInChart, Function.comp, z₀] using hcomp
  have hTchart_diff :
      DifferentiableWithinAt 𝕜 Tchart S z₀ := by
    exact hTchart_cd.contDiffWithinAt.differentiableWithinAt (by simp)
  have hscalar_diff :
      DifferentiableWithinAt 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ := by
    have hfun_diff :
        DifferentiableWithinAt 𝕜 (fun y : E => Tchart y β₀) S z₀ :=
      hTchart_diff.clm_apply (differentiableWithinAt_const β₀)
    exact hfun_diff.continuousMultilinear_apply_const u
  have hwritten_diff :
      DifferentiableWithinAt 𝕜
        (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) (Set.range I) z₀ := by
    have hscalar_diff_range :
        DifferentiableWithinAt 𝕜 (fun y : E => (Tchart y β₀) u) (Set.range I) z₀ := by
      simpa [hS] using hscalar_diff
    have hmodel_range :
        (fun y : E => (Tchart y β₀) u) =ᶠ[𝓝[Set.range I] z₀]
          writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
      simpa [hS] using hmodel_eventually
    exact (hmodel_range.differentiableWithinAt_iff_of_mem hzRange).mp hscalar_diff_range
  have hf_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀ := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(𝕜, 𝕜))
      (x := x₀) (x' := x₀) (mem_chart_source H x₀)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, z₀, extChartAt, Function.comp_def] using hwritten_diff
  unfold modelDerivRSAt coordDerivRSAt
  change
    ((fderivWithin 𝕜 Tchart S z₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀)) β₀) u =
      (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (X x₀)
  rw [hX, hf_md.mfderiv]
  have happly₁ :
      (fderivWithin 𝕜 Tchart S z₀ (X x₀)) β₀ =
        fderivWithin 𝕜 (fun y : E => Tchart y β₀) S z₀ (X x₀) := by
    have hconst : DifferentiableWithinAt 𝕜 (fun _ : E => β₀) S z₀ :=
      differentiableWithinAt_const β₀
    have h :=
      congrArg (fun L => L (X x₀))
        (fderivWithin_clm_apply (𝕜 := 𝕜) (s := S) (x := z₀)
          huniq hTchart_diff hconst)
    simpa [fderivWithin_const_apply] using h.symm
  rw [happly₁]
  have hfun_diff :
      DifferentiableWithinAt 𝕜 (fun y : E => Tchart y β₀) S z₀ := by
    exact hTchart_diff.clm_apply (differentiableWithinAt_const β₀)
  have happly₂ :
      (fderivWithin 𝕜 (fun y : E => Tchart y β₀) S z₀ (X x₀)) u =
        fderivWithin 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ (X x₀) := by
    exact (fderivWithin_continuousMultilinear_apply_const_apply
      huniq hfun_diff u (X x₀)).symm
  rw [happly₂]
  have hfd :
      fderivWithin 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ =
        fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) S z₀ :=
    hmodel_eventually.fderivWithin_eq_of_mem hzS
  rw [hfd]
  rw [hS]
  rfl

/-- Coordinate-frame component formula for `nablaRSFun` in arbitrary mixed
valence. -/
theorem nablaRS_coordFrame_slots {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M) (hderiv : ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x))
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k) := by
  classical
  simp only [nablaRSFun, TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection]
  rw [← tensorRSModelAt_coordComponentRSAt (I := I) x₀
    (TensorLieDeriv.mcovariantDeriv_tensorRSWithin
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s X
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      T Set.univ x₀) upper lower]
  have hmodel := TensorLieDeriv.covariantDeriv_tensorRSModelWithin_apply_basis_slots
    (𝕜 := 𝕜) (E := E)
    (basis := Module.finBasis 𝕜 E)
    (X := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I))
    (ΓX := connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (T := tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s x₀ (fun x => T x))
    (u := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
    (x := extChartAt I x₀ x₀)
    (upper := upper)
    (lower := lower)
  unfold TensorLieDeriv.mcovariantDeriv_tensorRSWithin
  rw [TensorLieDeriv.tensorRSModelAt_trivializationAt_symm]
  refine hmodel.trans ?_
  simp_rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  change
    modelDerivRSAt (I := I) X x₀ (fun x => T x) upper lower
      +
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r)
              (Function.update upper a k)))
            (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b)))
      -
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
            (Function.update
              (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
              b ((Module.finBasis 𝕜 E) k))) =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower)
      -
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k))
  rw [hderiv upper lower]
  have hupperSum :
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r)
              (Function.update upper a k)))
            (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))) =
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold tensorRSModelInChart
    rw [extChartAt_to_inv]
    rw [tensorRSModelAt_coordComponentRSAt (I := I) x₀ (T x₀)
      (Function.update upper a k) lower]
  have hlowerSum :
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
            (Function.update
              (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
              b ((Module.finBasis 𝕜 E) k))) =
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold tensorRSModelInChart
    rw [extChartAt_to_inv]
    have hslots :
        Function.update
            (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
            b ((Module.finBasis 𝕜 E) k) =
          fun c : Fin s => (Module.finBasis 𝕜 E) (Function.update lower b k c) := by
      funext c
      by_cases hc : c = b
      · subst hc
        simp
      · simp [Function.update, hc]
    rw [hslots]
    rw [← tensorRSModelAt_coordComponentRSAt (I := I) x₀ (T x₀)
      upper (Function.update lower b k)]
  rw [hupperSum, hlowerSum]

/-- Coordinate-frame component formula for `nablaRSFun`, with the model/scalar
derivative bridge discharged by smoothness of the tensor field. -/
theorem nablaRS_coordFrame_slots_of_smooth {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k) := by
  exact nablaRS_coordFrame_slots (I := I) cov X T x₀
    (modelDeriv_eq_coordDerivRSAt (I := I) X x₀ T) upper lower

end Coordinates
end RicciFlower
