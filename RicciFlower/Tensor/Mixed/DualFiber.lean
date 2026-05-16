/-
Authors: Jack McCarthy
-/
import RicciFlower.Tensor.Mixed.Fiber
import RicciFlower.Tensor.Multilinear.Dual
import Mathlib.LinearAlgebra.Contraction
/-!
# Mixed multilinear bundle fiber as a tensor product

This file establishes the canonical bundle-fiber-level linear equivalence

  `(MLF r at x) →L[𝕜] (MLF s at x)  ≃ₗ[𝕜]  (mlf-of-dual r at x) ⊗[𝕜] (MLF s at x)`

where:
* `MLF r at x = ContinuousMultilinearMap 𝕜 (Fin r → E x) 𝕜` (definitionally equal to
  `Bundle.continuousMultilinearMap 𝕜 r F E x`).
* `mlf-of-dual r at x = ContinuousMultilinearMap 𝕜 (Fin r → (E x →L[𝕜] 𝕜)) 𝕜`
  (the multilinear bundle of the dual at `x`).

The construction proceeds in two steps:

1. **Tensor-hom helper** `homEquivCDualTensor`: a model-fiber-level linear equivalence
   `(V →L[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W)` for finite-dimensional normed spaces `V, W`,
   built by composing `LinearMap.toContinuousLinearMap.symm` with Mathlib's
   `dualTensorHomEquiv`.

2. **Substitution via the dual iso**: instantiate `homEquivCDualTensor` at
   `V := MLF r at x`, `W := MLF s at x`, then apply
   `dualMultilinearLinearEquivAt` (from `Multilinear/DualFiber.lean`) to the first
   tensor factor to convert `(MLF r at x →L[𝕜] 𝕜)` into the multilinear-of-dual fiber.

Crucially, we work entirely at the bundle-fiber level (over `E x`), not at the model
level (over `F`). The dual *bundle* of `E` has fibers `E x →L[𝕜] 𝕜`, not `F →L[𝕜] 𝕜`,
so the multilinear-of-dual bundle's fiber at `x` is multilinear maps on `E x →L[𝕜] 𝕜`.

## Main Definitions

* `ContinuousMultilinearMap.homEquivCDualTensor` : the abstract tensor-hom iso
  `(V →L[𝕜] W) ≃ₗ[𝕜] (V →L[𝕜] 𝕜) ⊗[𝕜] W`.
* `Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt` : the bundle-fiber-level
  iso between the mixed `(r, s)` fiber at `x` and `(mlf-of-dual r at x) ⊗ (MLF s at x)`.

## Tags

mixed tensor, dual, tensor product, vector bundle fiber
-/

noncomputable section

open Bundle TensorProduct

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (W : Type*) [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! ## Tensor-hom helper -/

/-- The canonical "tensor of duals" linear equivalence
`(V →L[𝕜] W) ≃ₗ[𝕜] (V →L[𝕜] 𝕜) ⊗[𝕜] W`
for finite-dimensional normed spaces `V` and `W`.

Built by composing `LinearMap.toContinuousLinearMap.symm` (in finite dimensions, all
linear maps are continuous), Mathlib's `Module.dualTensorHomEquiv` (which gives
`Module.Dual 𝕜 V ⊗[𝕜] W ≃ₗ[𝕜] V →ₗ[𝕜] W`), and `TensorProduct.congr` to bridge
between `Module.Dual` and the continuous dual. -/
noncomputable def homEquivCDualTensor :
    (V →L[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) := by
  let e1 : (V →L[𝕜] W) ≃ₗ[𝕜] (V →ₗ[𝕜] W) := LinearMap.toContinuousLinearMap.symm
  let e2 : (V →ₗ[𝕜] W) ≃ₗ[𝕜] (Module.Dual 𝕜 V ⊗[𝕜] W) :=
    (dualTensorHomEquiv 𝕜 V W).symm
  let cdualEquiv : (V →L[𝕜] 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 V :=
    LinearMap.toContinuousLinearMap.symm
  let e3 : (Module.Dual 𝕜 V ⊗[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) :=
    TensorProduct.congr cdualEquiv.symm (LinearEquiv.refl 𝕜 W)
  exact e1.trans (e2.trans e3)

/-- The model-level linear equivalence between the hom-space of `r`- and `s`-multilinear
maps on a finite-dimensional space `F`, and the tensor product of `r`-multilinear maps on
the dual `F →L[𝕜] 𝕜` with `s`-multilinear maps on `F`:
`(MLF r F →L[𝕜] MLF s F) ≃ₗ[𝕜] (MLF r (F →L[𝕜] 𝕜) ⊗[𝕜] MLF s F)`. -/
noncomputable def multilinearHomEquivDualMultilinearTensor
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r s : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃ₗ[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (F →L[𝕜] 𝕜)) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  (homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)).trans
    (TensorProduct.congr
      (dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      (LinearEquiv.refl 𝕜 _))

end ContinuousMultilinearMap

/-! ## Transport between bundle and unfolded multilinear-fiber forms -/

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

-- Note: a transport CLE between the bundle form
-- `Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x`
-- and the unfolded form `CMM 𝕜 (Fin r → E x) 𝕜 →L[𝕜] CMM 𝕜 (Fin s → E x) 𝕜` would be
-- needed to bridge `MixedSection.toFun` (which uses the bundle form) with
-- `multilinearHomTensorEquivAt` (stated on the unfolded form).
--
-- An attempt to define such a transport via `arrowCongr` of two identity CLEs failed
-- due to instance diamonds: even though the underlying types are equal (since
-- `Bundle.continuousMultilinearMap` is `def`'d as a `ContinuousMultilinearMap`), Lean's
-- elaborator inserts different `TopologicalSpace` and `AddCommMonoid` instances
-- depending on which path it takes through the typeclass graph.
--
-- This is the same diamond that `Mixed/Fiber.lean` navigates with its private
-- `mixed_type_eq` theorem. Lifting `multilinearHomTensorEquivAt` to the section level
-- requires a more invasive approach (e.g. routing through the model fiber over `F`).

/-! ## The bundle-fiber-level mixed iso -/

/-- The bundle-fiber-level linear equivalence between the mixed multilinear bundle
fiber at `x` (= `Hom(MLF r fiber, MLF s fiber)`) and `(mlf-of-dual r at x) ⊗ (MLF s at x)`.

Stated using the unfolded `ContinuousMultilinearMap` form on the fibers `E x` and
their duals to avoid the topology diamond.

The construction:
1. Apply `homEquivCDualTensor` at `V := MLF r at x`, `W := MLF s at x`. This gives
   `((MLF r at x) →L[𝕜] (MLF s at x)) ≃ₗ ((MLF r at x →L[𝕜] 𝕜) ⊗ (MLF s at x))`.
2. Use `dualMultilinearLinearEquivAt` (the bundle-fiber-level dual iso from
   `Multilinear/DualFiber.lean`) to convert `(MLF r at x →L[𝕜] 𝕜)` into the
   multilinear-of-dual fiber `mlf-of-dual r at x`. -/
noncomputable def multilinearHomTensorEquivAt (r s : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  let e1 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
        ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    ContinuousMultilinearMap.homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
  let e2 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 ≃ₗ[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    TensorProduct.congr
      (dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x)
      (LinearEquiv.refl 𝕜 _)
  exact e1.trans e2

/-- Untrivialize each factor of a tensor product of model multilinear fibers back to the
corresponding tensor product of bundle multilinear fibers at `x`. The first factor is
untrivialized to the dual bundle's `r`-multilinear fiber; the second to `E`'s `s`-multilinear
fiber.

This is `TensorProduct.congr` of two applications of `(continuousLinearEquivAt _ x).symm`,
the only point being to package the per-factor bundle-from-model untrivialization once. -/
noncomputable def dualTensorMultilinearUntrivializeAt (r s : ℕ) (x : B) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (F →L[𝕜] 𝕜)) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃ₗ[𝕜]
    (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  TensorProduct.congr
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
      (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The bundle-fiber-level linear equivalence between the mixed multilinear bundle
fiber at `x` and the tensor product `(r-multilinear bundle on the dual) ⊗ (s-multilinear
bundle on E)`, both stated in the `Bundle.continuousMultilinearMap` form.

This is the bundle-form analogue of `multilinearHomTensorEquivAt`. The source uses the
mixed-fiber bundle topology path (`instTopologicalSpaceContinuousMultilinearMap`), so we
cannot reuse `multilinearHomTensorEquivAt` directly — the topology diamond with the norm
topology on `ContinuousMultilinearMap` prevents Lean from unifying the two forms.

The construction routes through the model fiber: `mixedContinuousLinearEquivAt` to the
model form, then the model-level `multilinearHomEquivDualMultilinearTensor`, then
`dualTensorMultilinearUntrivializeAt` to lift each tensor factor back to its bundle fiber. -/
noncomputable def multilinearHomTensorEquivAt_bundle (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) ≃ₗ[𝕜]
    ((Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  ((mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toLinearEquiv.trans
    (ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor 𝕜 F r s)).trans
    (dualTensorMultilinearUntrivializeAt (𝕜 := 𝕜) (F := F) (E := E) r s x)

end Bundle.continuousMultilinearMap

end
