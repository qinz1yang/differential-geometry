/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Tensor
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
/-!
# The model-fiber product as a continuous bilinear map, and its Fréchet product rule

The model-fiber product `modelProduct s q : MLF s → MLF q → MLF (s+q)` (defined in
`DifferentialGeometry.Tensor.Multilinear.Tensor`) is bilinear, and since the model
multilinear-map spaces `MLF n = ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜` are
finite-dimensional (`continuousMultilinearMap_finiteDimensional`), bilinearity upgrades to
*continuous* bilinearity. This file packages that continuous bilinear map and proves the
Fréchet product rule for it.

This is the analytic foundation a covariant Leibniz rule for the model tensor product is
built on: the chart-based base case of `tensorCovDerivAt`/`mfderiv` differentiates a product
`y ↦ modelProduct (f y) (g y)`, and `hasFDerivAt_modelProduct` supplies the derivative in the
standard `precompR + precompL` shape.

## Main definitions

* `Bundle.continuousMultilinearMap.modelProductₗ` : the model-fiber product packaged as a
  `LinearMap`-valued bilinear map `MLF s →ₗ[𝕜] MLF q →ₗ[𝕜] MLF (s+q)`.
* `Bundle.continuousMultilinearMap.modelProductL` : the continuous bilinear version
  `MLF s →L[𝕜] MLF q →L[𝕜] MLF (s+q)`, obtained from finite-dimensionality.

## Main results

* `Bundle.continuousMultilinearMap.modelProductL_apply` : `modelProductL s q f g = modelProduct s q f g`.
* `Bundle.continuousMultilinearMap.isBoundedBilinearMap_modelProduct` : the uncurried product
  `fun p => modelProduct s q p.1 p.2` is a bounded bilinear map.
* `Bundle.continuousMultilinearMap.hasFDerivAt_modelProduct` : the Fréchet product rule — for
  `f g : X → MLF _` differentiable at `x`, `y ↦ modelProduct s q (f y) (g y)` is differentiable
  at `x` with derivative `(modelProductL s q).precompR X (f x) g' + (modelProductL s q).precompL X f' (g x)`.
-/

noncomputable section

open Bundle

open scoped TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-- The model-fiber product `modelProduct` packaged as a bilinear `LinearMap`,
`MLF s →ₗ[𝕜] MLF q →ₗ[𝕜] MLF (s+q)`. This is the same bilinear map underlying `modelFromTensor`,
named here so it can be upgraded to a continuous bilinear map. -/
def modelProductₗ (s q : ℕ) :
    (MLF s) →ₗ[𝕜] (MLF q) →ₗ[𝕜] (MLF (s + q)) :=
  LinearMap.mk₂ 𝕜 (modelProduct (𝕜 := 𝕜) (F := F) s q)
    (fun f₁ f₂ g => by ext v; simp [modelProduct_apply, add_mul])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)
    (fun f g₁ g₂ => by ext v; simp [modelProduct_apply, mul_add])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp]
theorem modelProductₗ_apply (s q : ℕ)
    (f : MLF s) (g : MLF q) :
    modelProductₗ (𝕜 := 𝕜) (F := F) s q f g = modelProduct s q f g :=
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
/-- The model-fiber product is submultiplicative for the operator norm:
`‖modelProduct s q f g‖ ≤ ‖f‖ * ‖g‖`. Pointwise, `modelProduct s q f g v` splits as
`f (v ∘ castAdd q) * g (v ∘ natAdd s)`, each factor estimated by `le_opNorm`, and the two index
products recombine to `∏ i, ‖v i‖` via `Fin.prod_univ_add`. -/
theorem modelProduct_norm_bound (s q : ℕ) (f : MLF s) (g : MLF q) :
    ‖modelProduct (𝕜 := 𝕜) (F := F) s q f g‖ ≤ 1 * ‖f‖ * ‖g‖ := by
  rw [one_mul]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v => ?_)
  rw [modelProduct_apply, norm_mul]
  calc ‖f (v ∘ Fin.castAdd q)‖ * ‖g (v ∘ Fin.natAdd s)‖
      ≤ (‖f‖ * ∏ i, ‖(v ∘ Fin.castAdd q) i‖) * (‖g‖ * ∏ i, ‖(v ∘ Fin.natAdd s) i‖) := by
        gcongr
        · exact f.le_opNorm _
        · exact g.le_opNorm _
    _ = ‖f‖ * ‖g‖ * ∏ i, ‖v i‖ := by
        rw [Fin.prod_univ_add (fun i => ‖v i‖)]
        simp only [Function.comp_apply]
        ring

/-- The continuous bilinear model-fiber product `MLF s →L[𝕜] MLF q →L[𝕜] MLF (s+q)`.

Bilinearity (`modelProductₗ`) upgrades to continuity via the submultiplicative operator-norm bound
`modelProduct_norm_bound` (the model multilinear-map spaces are finite-dimensional, so this bound
is automatic; here it is supplied explicitly with constant `1`). -/
def modelProductL (s q : ℕ) :
    (MLF s) →L[𝕜] (MLF q) →L[𝕜] (MLF (s + q)) :=
  LinearMap.mkContinuous₂ (modelProductₗ (𝕜 := 𝕜) (F := F) s q) 1
    (fun f g => modelProduct_norm_bound s q f g)

omit [CompleteSpace 𝕜] in
@[simp]
theorem modelProductL_apply (s q : ℕ)
    (f : MLF s) (g : MLF q) :
    modelProductL (𝕜 := 𝕜) (F := F) s q f g = modelProduct s q f g :=
  rfl

omit [CompleteSpace 𝕜] in
/-- The uncurried model-fiber product `fun p => modelProduct s q p.1 p.2` is a bounded bilinear
map, packaged from the continuous bilinear map `modelProductL`. -/
theorem isBoundedBilinearMap_modelProduct (s q : ℕ) :
    IsBoundedBilinearMap 𝕜
      (fun p : (MLF s) × (MLF q) => modelProduct (𝕜 := 𝕜) (F := F) s q p.1 p.2) :=
  (modelProductL (𝕜 := 𝕜) (F := F) s q).isBoundedBilinearMap

omit [CompleteSpace 𝕜] in
/-- The Fréchet product rule for the model-fiber product.

If `f : X → MLF s` and `g : X → MLF q` have Fréchet derivatives `f'`, `g'` at `x`, then
`y ↦ modelProduct s q (f y) (g y)` has Fréchet derivative
`(modelProductL s q).precompR X (f x) g' + (modelProductL s q).precompL X f' (g x)` at `x` — the
standard `precompR + precompL` shape of the continuous-bilinear chain rule for `modelProductL`
composed with the pair map `y ↦ (f y, g y)`.

Pointwise the derivative unfolds (via `precompR_apply`/`precompL_apply` and `modelProductL_apply`)
to `modelProduct s q (f x) (g' v) + modelProduct s q (f' v) (g x)`, the consumer-minimal shape the
chart base case of the bundle-level covariant Leibniz rule needs for the chain rule into
`mfderiv`/`tensorCovDerivAt`.

The proof rewrites `modelProduct` to the continuous bilinear map `modelProductL`
(`modelProductL_apply` is definitional) so the continuous-bilinear chain rule
`ContinuousLinearMap.hasFDerivAt_of_bilinear` (discharged by `fun_prop`) applies — the operator-norm
topology on `MLF n` coincides definitionally with `ContinuousMultilinearMap`'s uniform-convergence
topology, but the two instances are not syntactically equal, so feeding the `MLF`-valued
hypotheses through `fun_prop` is the route that bridges them. -/
theorem hasFDerivAt_modelProduct {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (s q : ℕ) {f : X → MLF s} {g : X → MLF q}
    {f' : X →L[𝕜] (MLF s)} {g' : X →L[𝕜] (MLF q)} {x : X}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => modelProduct (𝕜 := 𝕜) (F := F) s q (f y) (g y))
      ((modelProductL (𝕜 := 𝕜) (F := F) s q).precompR X (f x) g'
        + (modelProductL (𝕜 := 𝕜) (F := F) s q).precompL X f' (g x)) x := by
  simp only [← modelProductL_apply]
  fun_prop

end Bundle.continuousMultilinearMap
