import RicciFlower.Coordinates.NablaComponents.TensorRS.Basic

/-!
# Mixed tensor coordinate input expansion

Hom-input expansion and scalar product-rule bridges for coordinate-frame mixed
tensor components.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

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

private theorem coordFrameRSComp_at {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    tensorRSComponentInFrame
        (I := I) (M := M)
        (Idx := CoordinateIdx (𝕜 := 𝕜) E)
        (u := coordinateFrameSet (I := I) x₀)
        (fun x => T x)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame (I := I) x₀)
        x₀ (coordinateFrameAt_mem (I := I) x₀) upper lower =
      coordComponentRSAt (I := I) (T x₀) upper lower := by
  rfl

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
              have hlocal :
                  βfun upper x₀ =
                    tensorRSComponentInFrame
                      (I := I) (M := M)
                      (Idx := CoordinateIdx (𝕜 := 𝕜) E)
                      (u := coordinateFrameSet (I := I) x₀)
                      (fun x => T x)
                      (coordinateFrameAt (I := I) x₀)
                      (coordinateFrameAt_isLocalFrame (I := I) x₀)
                      x₀ (coordinateFrameAt_mem (I := I) x₀) upper lower := by
                have hconst := constInChart_basisTensor0S_coordFrame
                  (I := I) (M := M) (r := r) x₀
                  (coordinateFrameAt_mem (I := I) x₀) upper
                simp [βfun, coordinateFrameAt_basis, hconst]
              exact hlocal.trans
                (coordFrameRSComp_at (I := I) T x₀ upper lower)
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

end Coordinates
end RicciFlower
