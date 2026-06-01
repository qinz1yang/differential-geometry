import DifferentialGeometry.Integral.Connection.Tensor0SNabla
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian

/-!
# Chart-coordinate decomposition for the `(0, s)`-tensor covariant derivative

Given a smooth Riemannian manifold `(M, g)` and a chart-center `α : M`, this
file constructs a chart-coordinate "intrinsic Fréchet derivative + Christoffel
correction" decomposition for the bundled covariant derivative
`tensor0SCovariantDerivative I M s cov` on the `(0, s)`-tensor bundle.

For a smooth `(0, s)`-tensor section `T : Π b : M, Tensor0SSpace s I b` and a
base point `b : M`, the headline identity decomposes the value
`(tensor0SCovariantDerivative s cov T) b` (a CLM
`TangentSpace I b →L[ℝ] Tensor0SSpace s I b`) as the sum of two pieces:

```
(tensor0SCovariantDerivative s cov T) b =
  tensor0SIntrinsicChartCLM s α T b
    + tensor0SChartChristoffelCorrection s α T b,
```

where the intrinsic piece is built from the Fréchet derivative of the
chart-α-trivialised `Tensor0SModel s ℝ E`-valued representation of `T` pulled
back through `(extChartAt I α).symm`, and the Christoffel correction is the
**residual** of the abstract value after subtracting the intrinsic piece.

## Strategy

The chart-α Christoffel correction is defined as the residual:

```
tensor0SChartChristoffelCorrection s α T b :=
  (tensor0SCovariantDerivative s cov T) b - tensor0SIntrinsicChartCLM s α T b.
```

The headline decomposition is then a definitional identity. The concrete
per-slot Γ-action identification — analogous to `christoffelCorrection` of
`LeviCivitaChartLocal.lean` for the tangent bundle — is the natural follow-up,
with the present file providing the algebraic framework.

## Main declarations

* `tensor0SChartE_section_repr s α T`: the chart-α-trivialised
  `Tensor0SModel s ℝ E`-valued representation of `T : Π b, Tensor0SSpace s I b`.
* `tensor0SChartFiberFromModel s α b`: the fibre right-inverse of the chart-α
  trivialisation, as a CLM `Tensor0SModel s ℝ E →L[ℝ] Tensor0SSpace s I b`.
* `tensor0SIntrinsicChartCLM s α T b`: the intrinsic chart-α piece, a CLM
  `TangentSpace I b →L[ℝ] Tensor0SSpace s I b`.
* `tensor0SChartChristoffelCorrection cov s α T b`: the chart-α Christoffel
  correction, defined as the residual.
* `tensor0SCovariantDerivative_chart_decomp`: the headline decomposition
  theorem (CLM identity).
* `tensor0SCovariantDerivative_chart_decomp_apply` /
  `_vectorField`: pointwise and vector-field forms of the decomposition.
* `tensor0SIntrinsicChartCLM_add_section` / `_smul_section`: linearity of the
  intrinsic piece in `T`, in chart-pullback form.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- The chart-α-trivialised `Tensor0SModel s ℝ E`-valued representation of a
`(0, s)`-tensor section. -/
noncomputable def tensor0SChartE_section_repr (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) : Tensor0SModel s ℝ E :=
  (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b (T b)

/-- Pointwise unfolding. -/
@[simp] lemma tensor0SChartE_section_repr_apply (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    tensor0SChartE_section_repr (I := I) s α T b =
      (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b (T b) :=
  rfl

/-- The trivialised representation is additive in the section. -/
lemma tensor0SChartE_section_repr_add (s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace s I b) :
    tensor0SChartE_section_repr (I := I) s α (T₁ + T₂) =
      tensor0SChartE_section_repr (I := I) s α T₁ +
        tensor0SChartE_section_repr (I := I) s α T₂ := by
  funext b
  unfold tensor0SChartE_section_repr
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        ((T₁ + T₂) b) = _
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        (T₁ b + T₂ b) = _
  exact map_add _ (T₁ b) (T₂ b)

/-- The trivialised representation is scalar-multiplicative in the section. -/
lemma tensor0SChartE_section_repr_smul (s : ℕ) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace s I b) :
    tensor0SChartE_section_repr (I := I) s α (c • T) =
      c • tensor0SChartE_section_repr (I := I) s α T := by
  funext b
  unfold tensor0SChartE_section_repr
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        ((c • T) b) = _
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        (c • T b) = _
  exact map_smul _ c (T b)

/-- The fibre right-inverse of the chart-α trivialisation on the base set,
sending a model fibre value back to a section fibre value. -/
noncomputable def tensor0SChartFiberFromModel (s : ℕ) (α : M) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SSpace s I b :=
  (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).symmL ℝ b

/-- The chart-α intrinsic Fréchet derivative CLM. The action on a tangent
vector `v` is
`tensor0SChartFiberFromModel s α b
  (fderiv (tensor0SChartE_section_repr s α T ∘ (extChartAt I α).symm)(φ b)(triv v))`,
where `φ = extChartAt I α` and `triv = trivToE α b`. -/
noncomputable def tensor0SIntrinsicChartCLM (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    TangentSpace I b →L[ℝ] Tensor0SSpace s I b :=
  (tensor0SChartFiberFromModel (I := I) s α b).comp
    ((fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α T ∘ (extChartAt I α).symm)
        (extChartAt I α b)).comp
      (trivToE (I := I) α b))

/-- Pointwise formula. -/
lemma tensor0SIntrinsicChartCLM_apply (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) (v : TangentSpace I b) :
    tensor0SIntrinsicChartCLM (I := I) s α T b v =
      tensor0SChartFiberFromModel (I := I) s α b
        (fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T ∘ (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b v)) := by
  classical
  unfold tensor0SIntrinsicChartCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

/-- Additivity in the section, parametrised by Fréchet-differentiability of
the chart pullback. -/
lemma tensor0SIntrinsicChartCLM_add_section (s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace s I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) s α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) s α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensor0SIntrinsicChartCLM (I := I) s α (T₁ + T₂) b =
      tensor0SIntrinsicChartCLM (I := I) s α T₁ b +
        tensor0SIntrinsicChartCLM (I := I) s α T₂ b := by
  classical
  have hsum_pull :
      (tensor0SChartE_section_repr (I := I) s α (T₁ + T₂) ∘
          (extChartAt I α).symm) =
        (tensor0SChartE_section_repr (I := I) s α T₁ ∘
            (extChartAt I α).symm) +
          (tensor0SChartE_section_repr (I := I) s α T₂ ∘
            (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensor0SChartE_section_repr_add (I := I) s α T₁ T₂)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α (T₁ + T₂) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T₁ ∘
            (extChartAt I α).symm) (extChartAt I α b) +
        fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T₂ ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsum_pull]
    exact fderiv_add h₁ h₂
  unfold tensor0SIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.add_apply, map_add]

/-- Scalar homogeneity in the section, parametrised by Fréchet-differentiability
of the chart pullback. -/
lemma tensor0SIntrinsicChartCLM_smul_section (s : ℕ) (α : M)
    (c : ℝ) (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensor0SIntrinsicChartCLM (I := I) s α (c • T) b =
      c • tensor0SIntrinsicChartCLM (I := I) s α T b := by
  classical
  have hsmul_pull :
      (tensor0SChartE_section_repr (I := I) s α (c • T) ∘
          (extChartAt I α).symm) =
        c • (tensor0SChartE_section_repr (I := I) s α T ∘
          (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensor0SChartE_section_repr_smul (I := I) s α c T)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α (c • T) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      c • fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsmul_pull]
    exact fderiv_const_smul hT c
  unfold tensor0SIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.smul_apply, map_smul]

variable
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- The chart-α Christoffel correction CLM of the `(0, s)`-tensor covariant
derivative, defined as the residual of the abstract value after subtracting
the intrinsic chart-α Fréchet-derivative piece. -/
noncomputable def tensor0SChartChristoffelCorrection (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    TangentSpace I b →L[ℝ] Tensor0SSpace s I b :=
  (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b -
    tensor0SIntrinsicChartCLM (I := I) s α T b

/-- Definitional unfolding of the chart-α Christoffel correction. -/
lemma tensor0SChartChristoffelCorrection_def (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    tensor0SChartChristoffelCorrection (I := I) cov s α T b =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b -
        tensor0SIntrinsicChartCLM (I := I) s α T b := rfl

/-- **Headline decomposition (CLM-form).** -/
theorem tensor0SCovariantDerivative_chart_decomp (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b =
      tensor0SIntrinsicChartCLM (I := I) s α T b +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b := by
  classical
  rw [tensor0SChartChristoffelCorrection_def]
  abel

/-- **Pointwise headline decomposition.** -/
theorem tensor0SCovariantDerivative_chart_decomp_apply (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) (v : TangentSpace I b) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b v =
      tensor0SIntrinsicChartCLM (I := I) s α T b v +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b v := by
  classical
  rw [tensor0SCovariantDerivative_chart_decomp (I := I) cov s α T b]
  rw [ContinuousLinearMap.add_apply]

/-- **Vector-field form of the headline decomposition.** -/
theorem tensor0SCovariantDerivative_chart_decomp_vectorField
    (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b (X b) =
      tensor0SIntrinsicChartCLM (I := I) s α T b (X b) +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b (X b) :=
  tensor0SCovariantDerivative_chart_decomp_apply (I := I) cov s α T b (X b)

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (v : TangentSpace I b) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b v =
      tensor0SIntrinsicChartCLM (I := I) s α T b v +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b v :=
  tensor0SCovariantDerivative_chart_decomp_apply (I := I) cov s α T b v

end Connection
end Integral
end DifferentialGeometry

end
