import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.Tensor0SChartChristoffel
import DifferentialGeometry.Integral.Connection.LeviCivita

/-!
# Agreement of the chart-frame `(0, s)`-tensor covariant derivative with the abstract one

Given a smooth Riemannian manifold `(M, g)` and a chart center `α : M`, this file
records the agreement between the chart-frame covariant derivative
`chartTensor0SCovariantDerivative g α s T X b` (built in
`ChartTensor0SCovariantDerivative.lean` directly from chart-α Christoffel data)
and the abstract bundled covariant derivative
`Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita g) T b (X b)`
(built recursively in `Tensor0SNabla.lean` via the curry isomorphism into the
Hom-bundle), at points `b` of the chart Levi-Civita good set.

## Scope of this file

This file proves the **`s = 0` base case** of the agreement, packaged as
`chartTensor0SCovariantDerivative_eq_abstract_zero`. The proof uses only the
existing scalar bridge `scalarFn` together with the chart-`s = 0` evaluation
formulas, and is completely independent of the chart Levi-Civita data (the
`s = 0` case carries no Christoffel correction). The good-set hypothesis is
**not** required for `s = 0`, but is kept in the signature so that the
statement matches the expected uniform shape of the agreement theorem and so
that the lemma slots in directly as the base case for an inductive extension.

The `s + 1` step of the agreement is intentionally **not** proved here. The
abstract `tensor0SCovariantDerivative_succ_fun` is defined through the curry
isomorphism `tensor0S_curry` and the `homBundleCovariantDerivativeFun`
construction on the Hom-bundle of `(0, s)`-tensors, whereas the chart-frame
`chartTensor0SCovariantDerivative_succ` is built directly from per-slot
Christoffel corrections. Identifying these two formulations requires explicit
concrete per-slot identification of `tensor0SChartChristoffelCorrection` — the
"natural follow-up" mentioned in the docstring of
`Tensor0SChartChristoffel.lean`. That identification is mathematically
substantial and is not provided here; the file `Tensor0SChartChristoffel.lean`
currently defines the abstract Christoffel correction as the **residual** of
the abstract value after subtracting the intrinsic Fréchet-derivative piece,
without giving a per-slot formula.

## Main result

* `chartTensor0SCovariantDerivative_eq_abstract_zero` — the `s = 0` agreement,
  stated as equality of `(0, 0)`-tensor fibre values.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SNabla

/-- Evaluation of `(tensor0Iso x).symm a` at the unique empty input gives back
the scalar `a`. This is the round-trip identity for the `s = 0` fibre
isomorphism, applied at the empty tuple. -/
private lemma tensor0Iso_symm_apply_empty (x : M) (a : ℝ) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
        ((tensor0Iso (I := I) (M := M) x).symm a))
      (fun i => Fin.elim0 i) = a := by
  classical
  let T₀ : Π y : M, Tensor0SSpace 0 I y :=
    fun y => if h : y = x then h ▸ ((tensor0Iso (I := I) (M := M) x).symm a) else 0
  have hT0x : T₀ x = (tensor0Iso (I := I) (M := M) x).symm a := by
    simp [T₀]
  have hscalarFn :
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
          T₀ x) (0 : Fin 0 → TangentSpace I x) = scalarFn I M T₀ x :=
    (scalarFn_eq_apply_zero (I := I) (M := M) T₀ x).symm
  have hscalar :
      scalarFn I M T₀ x = a := by
    change (tensor0Iso (I := I) (M := M) x) (T₀ x) = a
    rw [hT0x]
    exact (tensor0Iso (I := I) (M := M) x).apply_symm_apply a
  have h_inputs : (fun i : Fin 0 => Fin.elim0 i) =
      (0 : Fin 0 → TangentSpace I x) :=
    Subsingleton.elim _ _
  rw [h_inputs]
  rw [← hT0x]
  rw [hscalarFn, hscalar]

/-- Scalar form of `extDerivFun`: applied to a scalar function and a tangent
vector, it is exactly the manifold-Fréchet derivative. Mirrors the helper
`extDerivFun_eq_mfderiv` used in `Realized/Realization/Embedding.lean`. -/
private lemma extDerivFun_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  rfl

/-- Pointwise rewrite of the manifold-Fréchet derivative applied to a scalar
section after identifying it with `scalarFn`. We use this to bridge between
the chart formulation (which uses the raw section evaluation) and the abstract
formulation (which uses `scalarFn`). -/
private lemma mfderiv_section_zero_eq_scalarFn
    (T : Π b : M, Tensor0SSpace 0 I b) (b : M) (v : TangentSpace I b) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i => Fin.elim0 i)) b v =
      mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) b v := by
  classical
  have h_funeq :
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i => Fin.elim0 i)) =
        scalarFn I M T := by
    funext b'
    rw [scalarFn_eq_apply_zero (I := I) (M := M) T b']
    congr 1
    funext i
    exact i.elim0
  rw [h_funeq]
  rfl

/-- **`s = 0` agreement.** For any smooth Riemannian manifold `(M, g)`, any
chart center `α : M`, any `(0, 0)`-tensor section `T`, any tangent vector field
`X`, and any point `b : M`, the chart-frame `(0, 0)`-covariant derivative of
`T` along `X` at `b` agrees with the abstract bundled covariant derivative
built from the Levi-Civita connection on the tangent bundle. The good-set
hypothesis is not used in this case (the `s = 0` chart-frame definition has
no Christoffel correction), but it is included for uniform-shape compatibility
with the higher-rank agreement theorems. -/
theorem chartTensor0SCovariantDerivative_eq_abstract_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b) (X : Π b : M, TangentSpace I b)
    {b : M} (_hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      Tensor0SNabla.tensor0SCovariantDerivative I M 0
          (LeviCivita (I := I) g) T b (X b) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i; exact i.elim0
  subst hm
  rw [chartTensor0SCovariantDerivative_zero_apply
      (I := I) g α T X b (fun i : Fin 0 => Fin.elim0 i)]
  rw [tensor0SCovariantDerivative_apply_zero
      (I := I) (M := M) (LeviCivita (I := I) g) T b (X b)]
  rw [mfderiv_section_zero_eq_scalarFn (I := I) (M := M) T b (X b)]
  rw [tensor0Iso_symm_apply_empty (I := I) (M := M) b
      (extDerivFun (I := I) (scalarFn I M T) b (X b))]
  exact (extDerivFun_apply_scalar (I := I) (scalarFn I M T) b (X b)).symm

example
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b) (X : Π b : M, TangentSpace I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      Tensor0SNabla.tensor0SCovariantDerivative I M 0
          (LeviCivita (I := I) g) T b (X b) :=
  chartTensor0SCovariantDerivative_eq_abstract_zero
    (I := I) (M := M) g α T X hb

end Connection
end Integral
end DifferentialGeometry
