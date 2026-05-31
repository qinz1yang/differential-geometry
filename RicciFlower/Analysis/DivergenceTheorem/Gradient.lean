import RicciFlower.Analysis.DivergenceTheorem.LocalFormula
import RicciFlower.Analysis.DivergenceTheorem.TangentAction
import RicciFlower.Analysis.Volume.ChartDensity
import RicciFlower.Analysis.Volume.Family
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Gradient of a smooth function on a Riemannian manifold

Given a smooth Riemannian metric `g` on the tangent bundle of a smooth manifold
`M` and a smooth scalar function `f : M → ℝ`, this file defines the gradient
`grad_g g hf` (where `hf` is a smoothness witness) as a smooth tangent
section, and establishes its defining duality with the differential of `f` and
basic algebraic properties.

## Construction

At each point `x : M`, the metric `g.inner x : E →L[ℝ] E →L[ℝ] ℝ` (where
`E := TangentSpace I x` definitionally) is a positive-definite continuous
bilinear form. The "musical flat" map `v ↦ g.inner x v` is an `ℝ`-linear map
from `E` into `E →ₗ[ℝ] ℝ`. By positive-definiteness it is injective; since `E`
is finite-dimensional, the spaces `E` and `E →ₗ[ℝ] ℝ` have the same dimension,
so the flat map is a linear equivalence.

The gradient at `x` is then defined as the preimage under this equivalence of
the differential `mfderiv I 𝓘(ℝ) f x`, viewed as a linear functional on
`TangentSpace I x`. This gives the duality identity
$$g(\nabla_g f, v) = (\mathrm{d}f)(v)$$
for all tangent vectors `v` at `x`.

## Smoothness

Smoothness of `grad_g g hf` is established by exhibiting it pointwise on each
chart base set as the linear combination
$$(\nabla_g f)(x) = \sum_{i,j} G^{ij}(x)\, \partial_j \tilde f(\varphi(x))\,
    e_i(x),$$
where `G^{ij}` is the entrywise inverse of the chart Gram matrix `G_{ij} =
g.inner x (e_i, e_j)`, the `e_i` are the chart-basis frame vectors, and
$\tilde f = f \circ \varphi^{-1}$ is the chart-pullback of `f`. The inverse
Gram matrix is smooth on the chart base set since the Gram matrix is smooth
and positive-definite there.

## Compact support

If `f : M → ℝ` has compact support, so does `grad_g g hf`: the gradient
vanishes wherever `mfderiv f x` does (in particular, off `tsupport f` where
`f` is locally zero).

## Main definitions

* `metricFlatMap g x` : the flat linear equivalence
  `TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ)` induced by `g.inner x`.
* `metricSharp g x α` : the gradient (sharp) of a covector `α` at `x`, defined
  as the inverse of `metricFlatMap g x`.
* `gradFun g f` : the underlying pointwise gradient function.
* `grad_g g hf` : the smooth gradient of a smooth scalar `f` (with smoothness
  proof `hf`) as a smooth tangent section.

## Main results

* `tangentSectionAction_grad_g_eq_inner` : duality with the differential.
* `inner_grad_g_symm` : symmetry of the metric on two gradients.
* `hasCompactSupport_grad_g` : compact support of the gradient when `f` has
  compact support.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace RicciFlower
namespace Analysis
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open RicciFlower.Analysis.Volume

/-! ## Pointwise flat map and its inverse

For each `x : M`, the metric `g.inner x` defines a continuous bilinear form on
`TangentSpace I x`. Currying gives a linear map `metricFlatLinear g x` from
the tangent space into its `ℝ`-linear dual; positive-definiteness makes this
map injective, and hence (by finite-dimensionality and equality of dimensions)
a linear equivalence. -/

/-- The "musical flat" linear map at `x : M`: sends a tangent vector `v` to the
linear functional `w ↦ g.inner x v w`. -/
def metricFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    rw [map_add, ContinuousLinearMap.add_apply]
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    rw [map_smul, ContinuousLinearMap.smul_apply]

@[simp] lemma metricFlatLinear_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatLinear (I := I) g x v w = g.inner x v w := rfl

/-- The flat linear map is injective: from positive-definiteness of `g.inner x`. -/
lemma metricFlatLinear_injective (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (metricFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : ∀ z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L z) hvw
    simp only [metricFlatLinear_apply] at h
    -- Goal: `g.inner x (v - w) z = 0`. By bilinearity, this equals
    -- `g.inner x v z - g.inner x w z`, which is `0` by `h`.
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl 0) (hzero (v - w) ▸ hpos)

/-- `TangentSpace I x` is finite-dimensional over `ℝ`. -/
private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- The flat map's domain and codomain have the same finite dimension over `ℝ`. -/
private lemma metricFlatLinear_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

/-- The flat linear equivalence `TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ)`
induced by the metric `g` at `x`. -/
def metricFlatMap (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (metricFlatLinear (I := I) g x)
    (metricFlatLinear_injective (I := I) g x)
    (metricFlatLinear_finrank_eq (I := I) (M := M) x)

@[simp] lemma metricFlatMap_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatMap (I := I) g x v w = g.inner x v w := rfl

/-- Defining property of `metricFlatMap.symm`: it sends a covector `α` to the
unique `v` with `g.inner x v w = α w` for all `w`. -/
lemma metricFlatMap_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x ((metricFlatMap (I := I) g x).symm α) w = α w := by
  have h := (metricFlatMap (I := I) g x).apply_symm_apply α
  have hh : metricFlatMap (I := I) g x ((metricFlatMap (I := I) g x).symm α) w = α w :=
    congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L w) h
  rw [metricFlatMap_apply] at hh
  exact hh

/-! ## Pointwise gradient (sharp) -/

/-- The pointwise gradient (sharp) of a covector at a point. -/
def metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) : TangentSpace I x :=
  (metricFlatMap (I := I) g x).symm α

@[simp] lemma metricSharp_def (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (I := I) g x α = (metricFlatMap (I := I) g x).symm α := rfl

/-- Defining identity for the sharp: `g.inner x (sharp α) w = α w`. -/
lemma inner_metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x (metricSharp (I := I) g x α) w = α w :=
  metricFlatMap_apply_symm (I := I) g x α w

/-- Symmetric form: `g.inner x w (sharp α) = α w`. -/
lemma inner_metricSharp_right (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x w (metricSharp (I := I) g x α) = α w := by
  rw [g.symm x w (metricSharp (I := I) g x α)]
  exact inner_metricSharp (I := I) g x α w

/-! ## The gradient as a function -/

/-- The pointwise gradient of a function `f : M → ℝ` at `x : M`. -/
def gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap

@[simp] lemma gradFun_def (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := rfl

/-- Defining identity: `g.inner x (gradFun g f x) v = mfderiv f x v`. -/
lemma inner_gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  rw [gradFun_def]
  exact inner_metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap v

/-- Symmetric form: `g.inner x v (gradFun g f x) = mfderiv f x v`. -/
lemma inner_gradFun_right (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  rw [g.symm x v (gradFun (I := I) g f x)]
  exact inner_gradFun (I := I) g f x v

/-- The gradient vanishes wherever the differential vanishes. -/
lemma gradFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {x : M}
    (hf : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  unfold gradFun metricSharp
  have htoLM : (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap =
      (0 : TangentSpace I x →ₗ[ℝ] ℝ) := by
    rw [hf]; rfl
  rw [htoLM]
  exact LinearEquiv.map_zero _

/-- Manifold chain rule for the real exponential target. -/
private lemma hasMFDerivAt_rexp
    {f : M → ℝ} {x : M} {f' : TangentSpace I x →L[ℝ] ℝ}
    (hf : HasMFDerivAt I 𝓘(ℝ, ℝ) f x f') :
    HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (f y)) x
      (Real.exp (f x) • f') := by
  refine ⟨Real.continuous_exp.continuousAt.comp hf.1, ?_⟩
  simpa [writtenInExtChartAt, Function.comp_def] using hf.2.exp

/-- Chain rule for the linear map underlying `d(exp(-f))`. -/
lemma mfderiv_exp_neg_toLinearMap
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(f y))) x).toLinearMap =
      (-Real.exp (-(f x))) •
        (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := by
  have hmf :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(f y))) x =
        (-Real.exp (-(f x))) • mfderiv I 𝓘(ℝ, ℝ) f x := by
    simpa [Pi.neg_apply, neg_smul] using
      (hasMFDerivAt_rexp (I := I) hf.hasMFDerivAt.neg).mfderiv
  rw [hmf]
  ext v
  rfl

/-- Pointwise chain rule for the gradient of `exp(-f)`. -/
lemma gradFun_exp_neg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (fun y : M => Real.exp (-(f y))) x =
      (-Real.exp (-(f x))) • gradFun (I := I) g f x := by
  unfold gradFun metricSharp
  rw [mfderiv_exp_neg_toLinearMap (I := I) hf]
  exact LinearEquiv.map_smul
    (metricFlatMap (I := I) g x).symm
    (-Real.exp (-(f x)))
    (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap

/-! ## Inverse Gram matrix and its smoothness -/

/-- The inverse Gram matrix at `(α, x)`. On the chart base set this is the
matrix inverse of the (positive-definite) Gram matrix; off the base set it is a
default value. -/
def chartInvGramMatrix (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹

/-- On the chart base set, the inverse Gram matrix is a one-sided inverse. -/
lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * chartGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

/-- Symmetric form. -/
lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

/-- Each adjugate entry of the Gram matrix is smooth on the trivialization base
set. The adjugate entry is the determinant of an updated submatrix, hence a
polynomial expression in the (smooth) Gram-matrix entries. -/
lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp : (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j) =
      (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) =
      (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (chartGramMatrix (I := I) g α x).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun x : M => chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-- Each entry of the inverse Gram matrix is smooth on the chart base set. -/
lemma chartInvGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- On the base set, `A⁻¹ = Ring.inverse A.det • adjugate A`. Hence the (i,j) entry is
  -- `Ring.inverse (det A) * adjugate A i j = (det A)⁻¹ * adjugate A i j`.
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    -- Now `A⁻¹ i j = (det⁻¹ʳ • adjugate A) i j`.
    change (Ring.inverse (chartGramMatrix (I := I) g α x).det •
            (chartGramMatrix (I := I) g α x).adjugate) i j =
      ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    -- For `ℝ` (a field), `Ring.inverse a = a⁻¹` (and `Ring.inverse 0 = 0`).
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · -- `(det · )⁻¹` is smooth where `det · ≠ 0`.
    have hdet_smooth : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => (chartGramMatrix (I := I) g α x).det)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

private lemma chartGramMatrixOnE_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j)
      (extChartAt I α).target := by
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

private lemma hasDerivAt_line_of_differentiableAt
    {F : E → ℝ} {y₀ : E} (v : E)
    (hF : DifferentiableAt ℝ F y₀) :
    HasDerivAt (fun t : ℝ => F (y₀ + t • v))
      (fderiv ℝ F y₀ v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => y₀ + t • v) v 0 := by
    have hscale : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id' (x := (0 : ℝ))).smul_const v
    have hsum : HasDerivAt (fun t : ℝ => y₀ + t • v) (0 + v) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := y₀)).add hscale
    simpa using hsum
  have hcomp :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
  simpa [Function.comp] using hcomp

lemma chartInvGramMatrix_symm
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g α x j i =
      chartInvGramMatrix (I := I) g α x i j := by
  have hherm :
      (chartInvGramMatrix (I := I) g α x).IsHermitian := by
    unfold chartInvGramMatrix
    exact (chartGramMatrix_isHermitian (I := I) g α x).inv
  simpa using hherm.apply i j

private lemma chartGramMatrixOnE_partial_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (p i j : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p
        (fun z : E =>
          chartGramMatrix (I := I) g α ((extChartAt I α).symm z) j i) y =
      partialDeriv (E := E) p
        (fun z : E =>
          chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y := by
  congr 2
  funext z
  have h := chartGramMatrix_isHermitian (I := I) g α ((extChartAt I α).symm z)
  simpa using h.apply i j

private lemma trace_invGram_mul_partialGram
    (g : SmoothRiemannianMetric I M) (α x : M)
    (p : Fin (Module.finrank ℝ E)) (y : E) :
    Matrix.trace
        (chartInvGramMatrix (I := I) g α x *
          Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            partialDeriv (E := E) p
              (fun z : E =>
                chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y))
      =
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          partialDeriv (E := E) p
            (fun z : E =>
              chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) p
              (fun z : E =>
                chartGramMatrix (I := I) g α ((extChartAt I α).symm z) j i) y)
        =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) p
              (fun z : E =>
                chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chartGramMatrixOnE_partial_symm (I := I) g α p i j y]
    _ = _ := rfl

/-- Point-centered chart-density logarithmic derivative in matrix form. This is
the density side of the later density/Christoffel-trace bridge. -/
theorem chartDensityOnE_partial_div_eq_half_trace_invGram_partialGram
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p (chartDensityOnE (I := I) g x) (extChartAt I x x) /
        chartDensityOnE (I := I) g x (extChartAt I x x)
      =
    (1 / 2 : ℝ) *
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            partialDeriv (E := E) p
              (fun y : E =>
                chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
              (extChartAt I x x) := by
  classical
  let y₀ : E := extChartAt I x x
  let v : E := (Module.finBasis ℝ E) p
  let Gline : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun t => chartGramMatrix (I := I) g x ((extChartAt I x).symm (y₀ + t • v))
  let Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i j =>
      partialDeriv (E := E) p
        (fun y : E => chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j) y₀
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [y₀, (extChartAt I x).map_source hxsrc]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hsymm_y₀ : (extChartAt I x).symm y₀ = x := by
    simp [y₀, (extChartAt I x).left_inv hxsrc]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensityOnE (I := I) g x y₀ := by
    simpa [chartDensityOnE, y₀, hsymm_y₀] using
      chartDensity_pos (I := I) g x hxbase
  have hρ_ne : chartDensityOnE (I := I) g x y₀ ≠ 0 := ne_of_gt hρ_pos
  have hρ_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_line : HasDerivAt
      (fun t : ℝ => chartDensityOnE (I := I) g x (y₀ + t • v))
      (partialDeriv (E := E) p (chartDensityOnE (I := I) g x) y₀) 0 := by
    simpa [partialDeriv, v] using
      hasDerivAt_line_of_differentiableAt (E := E)
        (F := chartDensityOnE (I := I) g x) (y₀ := y₀) v hρ_diff
  have hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun t : ℝ => Gline t i j) (Gprime i j) 0 := by
    intro i j
    have hentry_diff : DifferentiableAt ℝ
        (fun y : E => chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
        y₀ := by
      have hsmooth : ContDiffOn ℝ ∞
          (fun y : E => chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
          (extChartAt I x).target :=
        chartGramMatrixOnE_entry_contDiffOn (I := I) g x i j
      exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
        (by simp)
    simpa [Gline, Gprime, partialDeriv, v] using
      hasDerivAt_line_of_differentiableAt (E := E)
        (F := fun y : E =>
          chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
        (y₀ := y₀) v hentry_diff
  have hpos_det : 0 < (Gline 0).det := by
    simpa [Gline, y₀, v, hsymm_y₀] using
      chartGramMatrix_det_pos (I := I) g x hxbase
  have hjac := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := Gline) (G' := Gprime) (t := (0 : ℝ)) hEntries hpos_det
  have hjacρ : HasDerivAt
      (fun t : ℝ => chartDensityOnE (I := I) g x (y₀ + t • v))
      ((1 / 2 : ℝ) *
        Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) *
          chartDensityOnE (I := I) g x y₀) 0 := by
    simpa [Gline, Gprime, chartDensityOnE, chartDensity, y₀, v, hsymm_y₀] using hjac
  have hderiv :
      partialDeriv (E := E) p (chartDensityOnE (I := I) g x) y₀ =
        ((1 / 2 : ℝ) *
          Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) *
            chartDensityOnE (I := I) g x y₀) :=
    hρ_line.unique hjacρ
  have htrace :
      Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              partialDeriv (E := E) p
                (fun y : E =>
                  chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                y₀ := by
    simpa [Gprime, chartInvGramMatrix] using
      trace_invGram_mul_partialGram (I := I) (M := M) g x x p y₀
  calc
    partialDeriv (E := E) p (chartDensityOnE (I := I) g x) (extChartAt I x x) /
        chartDensityOnE (I := I) g x (extChartAt I x x)
        = partialDeriv (E := E) p (chartDensityOnE (I := I) g x) y₀ /
            chartDensityOnE (I := I) g x y₀ := by rfl
    _ = ((1 / 2 : ℝ) *
          Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) *
            chartDensityOnE (I := I) g x y₀) /
          chartDensityOnE (I := I) g x y₀ := by rw [hderiv]
    _ = (1 / 2 : ℝ) *
          Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) := by
      field_simp [hρ_ne]
    _ = (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              partialDeriv (E := E) p
                (fun y : E =>
                  chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                (extChartAt I x x) := by
      rw [htrace]

/-! ## `L¹` entry sum of the inverse Gram matrix

The pointwise sum of absolute values of all entries of the chart-`α` inverse
Gram matrix. This is a non-negative real-valued function on `M`, continuous on
the chart-`α` source. It plays the role of a pointwise operator-norm proxy in
chart-bridge estimates for the gradient. -/

/-- The chart-`α` inverse-Gram-matrix `L¹` entry sum at `x : M`. This is the
sum of absolute values of all entries of the inverse Gram matrix. -/
noncomputable def chartInvGramMatrix_l1Sum
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) : ℝ :=
  ∑ ij : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)),
    |chartInvGramMatrix (I := I) g α x ij.1 ij.2|

/-- `chartInvGramMatrix_l1Sum` is non-negative pointwise. -/
lemma chartInvGramMatrix_l1Sum_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x := by
  unfold chartInvGramMatrix_l1Sum
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `chartInvGramMatrix_l1Sum g α` is continuous on `(chartAt H α).source`. -/
lemma chartInvGramMatrix_l1Sum_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (chartInvGramMatrix_l1Sum (I := I) (M := M) g α)
      (chartAt H α).source := by
  classical
  unfold chartInvGramMatrix_l1Sum
  refine continuousOn_finset_sum _ (fun ij _ => ?_)
  -- The trivialization base set coincides with the chart source definitionally.
  have h_base_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := rfl
  have h1 :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x ij.1 ij.2)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α ij.1 ij.2
  have h_cont : ContinuousOn
      (fun x : M => chartInvGramMatrix (I := I) g α x ij.1 ij.2)
      (chartAt H α).source := by
    have := h1.continuousOn
    rw [h_base_eq] at this
    exact this
  exact h_cont.abs

/-! ## Chart-local representation of the gradient -/

/-- The `i`-th chart-basis component of the gradient at `x`, in the chart at `α`.
This is `∑_j G^{ij}(x) · ∂_j f̃(φ x)`. -/
def gradChartCoeff (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x i j *
      partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)

@[simp] lemma gradChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    gradChartCoeff (I := I) g α f i x =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) := rfl

/-- The chart-local representation of the gradient as a linear combination of
the chart-basis frame at `α`. -/
def gradChartLocal (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    gradChartCoeff (I := I) g α f i x •
      chartBasisVecFiber (I := I) α i x

/-! ## A version of `mfderiv_chartBasisVecFiber` requiring only `MDifferentiableAt` -/

/-- A version of `mfderiv_chartBasisVecFiber` that requires only
`MDifferentiableAt I 𝓘(ℝ, ℝ) f x` rather than full smoothness of `f`. -/
lemma mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hxchart : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) f x (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hxchart
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxchart
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  -- Differentiability of `scalarOnE α f` at `φ x`. Use that
  -- `scalarOnE α f = f ∘ (extChartAt I α).symm`, plus the fact that the symm
  -- map is mdiff at `φ x` and `f` is mdiff at `x = symm(φ x)`.
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  -- Use `EventuallyEq.mdifferentiableAt_iff` to lift `MDifferentiableAt` from `f` to the
  -- composition. Actually we already have `hcong`, we can use the symmetric form
  -- giving us `MDifferentiableAt (scalarOnE α f ∘ φ) x`.
  have hcomp_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x := by
    have h := hcong.mdifferentiableAt_iff (𝕜 := ℝ) (I := I) (I' := 𝓘(ℝ, ℝ))
    exact h.mp hf
  -- We need `MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE α f) (φ x)`. This follows
  -- because the composition `(scalarOnE α f) ∘ φ = (something differentiable at x)`
  -- and `φ` is a local diffeomorphism (in particular has nonsingular mfderiv).
  -- We use a more direct argument: the `extChartAt I α` near `x` is essentially the
  -- chart map; reading off the chain rule and the fact that the chart map is locally
  -- a homeomorphism, we can extract differentiability of the composite at `φ x`.
  -- Alternative: use that `scalarOnE α f =ᶠ[𝓝 (φ x)] f ∘ (φ.symm)`, and `f ∘ φ.symm`
  -- is mdiff at `φ x`.
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
    have htgt_int : (extChartAt I α).target ∈ 𝓝 (φ x) := by
      have hint_open : IsOpen (interior (extChartAt I α).target) := isOpen_interior
      exact mem_nhds_iff.mpr ⟨interior _, interior_subset, hint_open, hx_int⟩
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (φ x) :=
      (hcontMDiffOn (φ x) (interior_subset hx_int)).contMDiffAt htgt_int
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : (extChartAt I α).symm (φ x) = x := φ.left_inv hxsrc
  -- `f ∘ (extChartAt I α).symm` is mdiff at `φ x`.
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I α).symm (φ x)) := by
    rw [hsymm_at_x]; exact hf
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (f ∘ (extChartAt I α).symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  -- And `(scalarOnE α f) = f ∘ (extChartAt I α).symm` definitionally.
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ (extChartAt I α).symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (scalarOnE (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  -- Now apply chain rule.
  have hchain :
      mfderiv I 𝓘(ℝ, ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Identify `mfderiv (extChartAt I α) x (chartBasisVecFiber α i x) = (Module.finBasis ℝ E) i`.
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x)
        = (Module.finBasis ℝ E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hxchart]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : chartBasisVecFiber (I := I) α i x = T.symm x ((Module.finBasis ℝ E) i) :=
      rfl
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((Module.finBasis ℝ E) i))
          = (Module.finBasis ℝ E) i := by
      have heqsymm : T.symm x ((Module.finBasis ℝ E) i)
            = T.symmL ℝ x ((Module.finBasis ℝ E) i) := by
        rw [Trivialization.symmL_apply]
      rw [heqsymm, Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (chartBasisVecFiber (I := I) α i x))
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

/-! ## Identification of `gradChartLocal` with `gradFun` -/

/-- The inner product of `gradChartLocal` with a chart-basis frame vector `e_k` is
the `k`-th chart-pullback partial derivative of `f`. Pure linear-algebra step. -/
lemma inner_gradChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x (gradChartLocal (I := I) g α f x)
        (chartBasisVecFiber (I := I) α k x)
      = partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  unfold gradChartLocal
  -- LHS: g.inner x (∑ i, a_i • e_i) e_k = ∑ i, a_i * G_{ik} where a_i = gradChartCoeff i x.
  rw [show g.inner x (∑ i, gradChartCoeff (I := I) g α f i x •
            chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α k x) =
        ∑ i, gradChartCoeff (I := I) g α f i x *
          g.inner x (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · -- finite-sum expansion of g.inner.
    rw [show (g.inner x (∑ i, gradChartCoeff (I := I) g α f i x •
              chartBasisVecFiber (I := I) α i x)) =
          (∑ i, gradChartCoeff (I := I) g α f i x •
              g.inner x (chartBasisVecFiber (I := I) α i x)) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  -- Substitute `gradChartCoeff i x = ∑ j, G^{ij} ∂f j`.
  have ha : ∀ i, gradChartCoeff (I := I) g α f i x =
      ∑ j, chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) := fun i => rfl
  rw [show ∑ i, gradChartCoeff (I := I) g α f i x *
            g.inner x (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α k x) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)) *
              chartGramMatrix (I := I) g α x i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    -- chartGramMatrix g α x i k = g.inner x (e_i x) (e_k x)
    rfl
  -- Now interchange sums and use the Gram-inverse identity.
  -- ∑ i, (∑ j, Ginv_{ij} ∂f j) * G_{ik} = ∑ j, (∑ i, Ginv_{ij} G_{ik}) * ∂f j.
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              partialDeriv (E := E) j (scalarOnE (I := I) α f)
                (extChartAt I α x)) *
                chartGramMatrix (I := I) g α x i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) from ?_]
  swap
  · -- Step 1: factor each summand: (∑ j, Ginv ij * dfj) * G ik = ∑ j, (Ginv ij * dfj) * G ik
    -- = ∑ j, (Ginv ij * G ik) * dfj.
    rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                partialDeriv (E := E) j (scalarOnE (I := I) α f)
                  (extChartAt I α x)) *
                  chartGramMatrix (I := I) g α x i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α x i j *
                  chartGramMatrix (I := I) g α x i k) *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f)
                    (extChartAt I α x) from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  -- Now use ∑ i, Ginv_{ij} * G_{ik} = δ_{jk}, by the Gram-mul-inverse identity (G * G⁻¹ = 1)
  -- combined with the symmetry of G.
  have hsym : ∀ i, chartGramMatrix (I := I) g α x i k =
      chartGramMatrix (I := I) g α x k i := fun i => g.symm x _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
        chartGramMatrix (I := I) g α x i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) =
            (∑ i, chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    -- ∑ i, G_{k,i} * Ginv_{i,j} = (G * Ginv)_{k,j} = (1)_{k,j} = δ_{k,j}.
    have hidentity : (chartGramMatrix (I := I) g α x *
          chartInvGramMatrix (I := I) g α x) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
            chartGramMatrix (I := I) g α x i k) *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The chart-local representation `gradChartLocal` agrees with `gradFun` at every
chart-base-set point where `f` is differentiable and the chart map lands in the
interior of the chart target. -/
lemma gradChartLocal_eq_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    gradChartLocal (I := I) g α f x = gradFun (I := I) g f x := by
  classical
  have hxchart : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx; exact hx
  -- Set up an explicit CLM into ℝ for the mfderiv to avoid TangentSpace-vs-ℝ confusion.
  set f' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hf'_def
  -- The mfderiv evaluation: `mfderiv f x v = f' v` (by hf'_def, definitional).
  have hmfderiv_basis : ∀ k, f' (chartBasisVecFiber (I := I) α k x) =
      partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro k
    rw [hf'_def]
    exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) α hf hxchart hx_int k
  -- Both sides are determined by their inner product with arbitrary tangent vectors.
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradChartLocal (I := I) g α f x) v =
    g.inner x (gradFun (I := I) g f x) v
  rw [inner_gradFun (I := I) g f x v]
  -- Replace `mfderiv f x v` by `f' v`.
  change g.inner x (gradChartLocal (I := I) g α f x) v = f' v
  -- Decompose `v = ∑ k, c k • e_k x`.
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hx
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => b.repr v k
  have hv_decomp : v = ∑ k, c k • chartBasisVecFiber (I := I) α k x := by
    have h1 : v = ∑ k, b.repr v k • b k := (b.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartBasisFamily_apply (I := I) α hx k]
  rw [hv_decomp]
  -- Both sides are linear in `v`, so commute with the finite sum.
  -- LHS: g.inner x (gradChartLocal g α f x) (∑ k, c k • e_k x)
  -- RHS: f' (∑ k, c k • e_k x)
  rw [show g.inner x (gradChartLocal (I := I) g α f x)
        (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * g.inner x (gradChartLocal (I := I) g α f x)
          (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · -- Apply `g.inner x` linearity in the second argument over the sum.
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show f' (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * f' (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_gradChartLocal_chartBasis (I := I) g α f hx k, hmfderiv_basis k]

/-! ## Pointwise grad-norm chart bound

A pointwise upper bound for `g.inner x (gradFun g f x) (gradFun g f x)` in
terms of the chart-`α` inverse-Gram-matrix `L¹` entry sum and the sum of squares
of the chart-pullback partial derivatives of `f`. On a boundaryless model this
public bound only requires `hx ∈ (chartAt H α).source` and pointwise
differentiability of `f` at `x`. -/

/-- The pointwise `g`-norm bound on the gradient: for `f` differentiable at `x`
and `x` in the chart-`α` source on a boundaryless model,
`‖gradFun g f x‖_g² ≤ chartInvGramMatrix_l1Sum α x · (∑ k, |∂_k f̃(φ x)|²)`,
where `f̃ = f ∘ (extChartAt I α).symm` is the chart pullback of `f` and `φ` is
the extended chart. -/
theorem g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials
    (g : SmoothRiemannianMetric I M) [I.Boundaryless]
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) ≤
      chartInvGramMatrix_l1Sum (I := I) (M := M) g α x *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α f)
            (extChartAt I α x)) ^ 2 := by
  classical
  -- Derive the trivialization-base-set membership and the chart-target
  -- interior membership from `hx` and the boundaryless assumption.
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    have hxtgt : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hxtgt
  -- Step 1: identify `gradFun` with `gradChartLocal` at `x`.
  have hgrad_eq :
      gradFun (I := I) g f x = gradChartLocal (I := I) g α f x :=
    (gradChartLocal_eq_gradFun (I := I) g α hf hbase hx_int).symm
  rw [hgrad_eq]
  -- Step 2: write `gradChartLocal = ∑ i, c i • e_i x` with `c i = gradChartCoeff i x`.
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    gradChartCoeff (I := I) g α f i x with hc_def
  have hgcl_eq :
      gradChartLocal (I := I) g α f x =
        ∑ i, c i • chartBasisVecFiber (I := I) α i x := by
    unfold gradChartLocal
    rfl
  rw [hgcl_eq]
  -- Step 3: `g.inner = cᵀ G c` via `chartGramMatrix_dotProduct_mulVec`.
  set Gmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g α x with hGmat_def
  have hG_form : g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • chartBasisVecFiber (I := I) α j x)
      = dotProduct (star c) (Matrix.mulVec Gmat c) :=
    (chartGramMatrix_dotProduct_mulVec (I := I) g α x c).symm
  rw [hG_form]
  -- Step 4: `c = G⁻¹ d`, where `d j = partialDeriv j (scalarOnE α f) (φ x)`.
  set d : Fin (Module.finrank ℝ E) → ℝ := fun j =>
    partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)
    with hd_def
  set Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartInvGramMatrix (I := I) g α x with hGinv_def
  have hc_eq : ∀ i, c i = ∑ j, Ginv i j * d j := by
    intro i
    rfl
  -- Expand `cᵀ G c = ∑_{ij} c_i G_{ij} c_j`.
  have hcGc_expand :
      dotProduct (star c) (Matrix.mulVec Gmat c) =
        ∑ i, ∑ j, c i * c j * Gmat i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_dot : dotProduct (Gmat i) c =
        ∑ j', Gmat i j' * c j' := rfl
    ring
  rw [hcGc_expand]
  -- Reduction `∑_{ij} c_i G_{ij} c_j = ∑_{jk} G⁻¹_{jk} d_j d_k`.
  have h_cGc_eq_dGd :
      (∑ i, ∑ j, c i * c j * Gmat i j) =
        ∑ j, ∑ k, Ginv j k * d j * d k := by
    -- Rearrange: `∑_{ij} c_i c_j G_{ij} = ∑_j c_j (∑_i c_i G_{ij})`.
    have hstep1 :
        (∑ i, ∑ j, c i * c j * Gmat i j) =
          ∑ j, c j * (∑ i, c i * Gmat i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hstep1]
    -- `∑_i c_i G_{ij} = (G c)_j = d_j` (since `c = G⁻¹ d`).
    have h_dot_sum : ∀ j, (∑ i, c i * Gmat i j) = d j := by
      intro j
      have hsym : ∀ i, Gmat i j = Gmat j i := fun i => g.symm x _ _
      have h_step :
          (∑ i, c i * Gmat i j) =
            (∑ i, ∑ k, Ginv i k * d k * Gmat j i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hc_eq i]
        rw [hsym i]
        rw [Finset.sum_mul]
      rw [h_step]
      have h_swap : (∑ i, ∑ k, Ginv i k * d k * Gmat j i) =
          ∑ k, d k * (∑ i, Gmat j i * Ginv i k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [h_swap]
      have h_id : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          (Gmat * Ginv) j k := by
        intro k
        rfl
      have h_id_eq_one : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          if j = k then (1 : ℝ) else 0 := by
        intro k
        rw [h_id k, hGmat_def, hGinv_def]
        rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase]
        rw [Matrix.one_apply]
      rw [show (∑ k, d k * (∑ i, Gmat j i * Ginv i k)) =
            ∑ k, d k * (if j = k then (1 : ℝ) else 0) from
        Finset.sum_congr rfl (fun k _ => by rw [h_id_eq_one k])]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hjk
        rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ j) hk
    have hstep2 :
        (∑ j, c j * (∑ i, c i * Gmat i j)) =
          ∑ j, c j * d j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_dot_sum j]
    rw [hstep2]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hc_eq j]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [h_cGc_eq_dGd]
  -- Bound `∑_{jk} G⁻¹_{jk} d_j d_k ≤ (∑_{jk} |G⁻¹_{jk}|) · (∑ k, d_k²)`.
  -- Use `|d_j| ≤ √D` and `|d_k| ≤ √D`, so `|d_j d_k| ≤ D` with `D := ∑ k, d_k²`.
  set D : ℝ := ∑ k, (d k) ^ 2 with hD_def
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd_sq_le : ∀ j, (d j) ^ 2 ≤ D := by
    intro j
    rw [hD_def]
    refine Finset.single_le_sum (f := fun k => (d k) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hd_abs_le_sqrtD : ∀ j, |d j| ≤ Real.sqrt D := by
    intro j
    rw [show |d j| = Real.sqrt ((d j) ^ 2) by rw [Real.sqrt_sq_eq_abs]]
    exact Real.sqrt_le_sqrt (hd_sq_le j)
  have h_dj_dk_le_D : ∀ j k, |d j * d k| ≤ D := by
    intro j k
    rw [abs_mul]
    have h := mul_le_mul (hd_abs_le_sqrtD j) (hd_abs_le_sqrtD k)
      (abs_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hD_nn] at h
    exact h
  have h_main_le :
      (∑ j, ∑ k, Ginv j k * d j * d k) ≤
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α x * D := by
    unfold chartInvGramMatrix_l1Sum
    rw [Finset.sum_mul]
    rw [show (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            |chartInvGramMatrix (I := I) g α x ij.1 ij.2| * D) =
          ∑ j, ∑ k, |Ginv j k| * D from ?_]
    swap
    · rw [← Finset.sum_product']
      rfl
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun k _ => ?_)
    have h1 : Ginv j k * d j * d k ≤ |Ginv j k * (d j * d k)| := by
      have h := le_abs_self (Ginv j k * (d j * d k))
      have heq : Ginv j k * d j * d k = Ginv j k * (d j * d k) := by ring
      rw [heq]
      exact h
    refine h1.trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h_dj_dk_le_D j k) (abs_nonneg _)
  exact h_main_le

/-! ## Smoothness of `gradFun` -/

/-- `gradChartCoeff g α f i` is `C^∞` on the smoothness domain (the chart base
set restricted to where the chart map lands in the interior of the chart target). -/
private lemma gradChartCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · -- `chartInvGramMatrix g α x i j` is smooth on the chart base set.
    have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · -- The chart-pulled-back partial derivative is smooth on the smoothness domain.
    have hpartial : ContDiffOn ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := by
      have hbase : ContDiffOn ℝ ∞
          (scalarOnE (I := I) α f) (extChartAt I α).target :=
        scalarOnE_contDiffOn (I := I) α hf
      have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
          (interior (extChartAt I α).target) := hbase.mono interior_subset
      have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
          (interior (extChartAt I α).target) :=
        hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
      have hconst : ContDiffOn ℝ ∞ (fun _ : E => (Module.finBasis ℝ E) j)
          (interior (extChartAt I α).target) := contDiffOn_const
      exact hfderiv.clm_apply hconst
    have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := hpartial.contMDiffOn
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        (chartAt H α).source := contMDiffOn_extChartAt
    have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        ((extChartAt I α).source ∩
          (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
      refine hchart.mono ?_
      intro x hx
      have h1 : x ∈ (extChartAt I α).source := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
      exact h1
    have hsubset : (extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
          (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
      fun _ hx => hx.2
    exact hpartialM.comp hchart' hsubset

/-- The chart-local representation `gradChartLocal g α f` is smooth as a
tangent-bundle section on the smoothness domain. -/
private lemma gradChartLocal_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  -- Each summand is `gradChartCoeff α f i x • chartBasisVecFiber α i x`, smooth.
  -- Sum them.
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    fun i => gradChartCoeff_contMDiffOn (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    refine (chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeff (I := I) g α f i x • chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)
  -- Sum.
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ i, gradChartCoeff (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    ContMDiffOn.sum_section (fun i _ => hsmul i)
  exact hsum

/-- Under `[I.Boundaryless]`, the smoothness domain of `gradChartLocal` reduces to the
chart base set. -/
private lemma gradChartLocal_contMDiffOn_total_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      (chartAt H α).source := by
  refine (gradChartLocal_contMDiffOn_total (I := I) g α hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

/-- Under `[I.Boundaryless]`, `gradFun g f` is smooth as a tangent-bundle section. -/
lemma gradFun_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth_local : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradChartLocal (I := I) g x f y))
      (chartAt H x).source :=
    gradChartLocal_contMDiffOn_total_baseSet (I := I) g x hf
  have heq_on_src : ∀ y ∈ (chartAt H x).source,
      gradChartLocal (I := I) g x f y = gradFun (I := I) g f y := by
    intro y hy
    have hbase : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hy
    have hy_int : extChartAt I x y ∈ interior (extChartAt I x).target := by
      have hys : y ∈ (extChartAt I x).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy
      have hytgt : extChartAt I x y ∈ (extChartAt I x).target :=
        (extChartAt I x).map_source hys
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) x hytgt
    have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
      hf.mdifferentiable (by simp) y
    exact gradChartLocal_eq_gradFun (I := I) g x hf_mdiff hbase hy_int
  have hsmooth_local2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradFun (I := I) g f y))
      (chartAt H x).source := by
    refine hsmooth_local.congr ?_
    intro y hy
    -- Need: `gradFun = gradChartLocal` here. `heq_on_src` gives `gradChartLocal = gradFun`.
    have h := heq_on_src y hy
    change TotalSpace.mk' E y (gradFun (I := I) g f y) =
      TotalSpace.mk' E y (gradChartLocal (I := I) g x f y)
    rw [h]
  exact (hsmooth_local2 x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

/-! ## The smooth gradient as a `ContMDiffSection` -/

/-- The smooth gradient of a smooth scalar function `f` (with smoothness proof
`hf`) as a smooth tangent-bundle section. -/
def grad_g [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, gradFun_contMDiff_total (I := I) g hf⟩

@[simp] lemma grad_g_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x := rfl

/-! ## Duality with the tangent-section action -/

/-- **Duality of gradient and tangent action.** The action of a smooth tangent
section `X` on a smooth scalar `f` equals the metric inner product of `X` with
the gradient `grad_g g hf`. -/
theorem tangentSectionAction_grad_g_eq_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (X x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [grad_g_apply]
  rw [inner_gradFun_right (I := I) g f x (X x)]
  rfl

/-! ## Symmetry -/

/-- The metric inner product on two gradients is symmetric. -/
theorem inner_grad_g_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (x : M) :
    g.inner x ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) :=
  g.symm x _ _

/-! ## Compact support -/

/-- If `f` is locally zero near `x`, then the gradient of `f` vanishes at `x`. -/
lemma gradFun_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ))) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero
  rw [Filter.EventuallyEq.mfderiv_eq hf]
  rw [mfderiv_const]
  rfl

/-- The support of `gradFun g f` is contained in the topological support of `f`. -/
lemma support_gradFun_subset
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    Function.support (fun x : M => gradFun (I := I) g f x) ⊆ tsupport f := by
  intro x hx
  by_contra hxnotin
  have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hxnotin] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  exact hx (gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hev)

/-- If `f` has compact support, then so does the section `grad_g g hf`. -/
lemma hasCompactSupport_grad_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf_cs : HasCompactSupport f) :
    HasCompactSupport ((grad_g (I := I) g hf :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  show x ∈ tsupport f
  exact support_gradFun_subset (I := I) g f hx

end DivergenceTheorem
end Analysis
end RicciFlower
