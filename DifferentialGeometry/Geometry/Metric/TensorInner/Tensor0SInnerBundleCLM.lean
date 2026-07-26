import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The pointwise (0,s) inner product as a continuous bilinear pairing

Given a smooth Riemannian metric `g` on a manifold `M` and an inner-product
structure on the model fibre `E`, this file packages the pointwise
`(0, s)`-tensor inner product `tensorInnerPointwise_0s s g b` as a continuous
bilinear pairing, first on the model fibre `Tensor0SModel s ℝ E`
(`innerModelCLM`) and then transferred to the bundle fibre `Tensor0SSpace s I b`
(`innerBundleCLM`) via the continuous linear equivalence between them. The
symmetry and positive-definiteness of the bundle pairing are recorded as
`innerBundleCLM_symm` and `innerBundleCLM_pos`.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- File-local instance: install the strong topology on `Tensor0SSpace s I b →L[ℝ] ℝ`.
The standard `ContinuousLinearMap.topologicalSpace` instance is not picked up
automatically through Lean's typeclass synthesis on the bundle topology of
`Tensor0SSpace s I b`; we register it explicitly here at file scope. -/
private instance bundleDualTopologicalSpace (s : ℕ) (b : M) :
    TopologicalSpace (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace
    (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := Tensor0SSpace s I b) (F := ℝ)

/-! ## The pointwise (0,s) inner product on the model fibre as a CLM

The pointwise inner product `tensorInnerPointwise_0s` is defined on the model
fibres `Tensor0SModel s ℝ E = Tensor0SModel s ℝ E`.
It is bilinear (proved in `PointwiseInner.Algebra`) and the model fibre is a
finite-dimensional normed space, so the bilinear map is automatically a
continuous bilinear map. We package it as a `→L[ℝ] · →L[ℝ] ·` CLM. -/

/-- Underlying bilinear (`LinearMap`-valued) pairing on the model fibre. -/
private def innerModelBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => tensorInnerPointwise_0s (I := I) (M := M) s g b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_left (I := I) (M := M) g b s c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_0s_add_right (I := I) (M := M) g b s T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_right (I := I) (M := M) g b s c T S)

@[simp] private lemma innerModelBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelBilin (I := I) (M := M) g s b T S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S := rfl

/-- The "outer" linear map: for each `T`, the inner-argument `S ↦ inner T S` is
linear and (since the model fibre is finite-dimensional) continuous. We package
this as a CLM. -/
private def innerModelLinearOuter
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] (Tensor0SModel s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilin (I := I) (M := M) g s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise_0s (I := I) (M := M) s g b (T₁ + T₂) S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b T₁ S +
        tensorInnerPointwise_0s (I := I) (M := M) s g b T₂ S
    exact tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise_0s (I := I) (M := M) s g b (c • T) S =
      c • tensorInnerPointwise_0s (I := I) (M := M) s g b T S
    rw [tensorInnerPointwise_0s_smul_left]
    rfl

/-- The pointwise `(0, s)` inner product as a continuous bilinear pairing on
the model fibre. -/
def innerModelCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuter (I := I) (M := M) g s b)

@[simp] lemma innerModelCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelCLM (I := I) (M := M) g s b T S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S := rfl

/-! ## Transferring the inner CLM to the bundle fibre

The bundle fibre `Tensor0SSpace s I b` shares the same underlying type as the
model fibre, but with the bundle topology. We have a CLE
`tensor0SSpace_continuousLinearEquiv` between them. To define the bundle-level
inner CLM `Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ`, we precompose
the model-level CLM `innerModelCLM` with this CLE on each argument. -/

/-- Shorthand for the CLE between the bundle fibre and the model fibre. -/
private def bundleCLE (s : ℕ) (b : M) :
    Tensor0SSpace s I b ≃L[ℝ]
      Tensor0SModel s ℝ E :=
  Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M) s b

/-- The forward CLM of `bundleCLE`. -/
private def bundleToModelCLM (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SModel s ℝ E :=
  (bundleCLE (I := I) (M := M) (E := E) s b).toContinuousLinearMap

@[simp] private lemma bundleToModelCLM_apply (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    bundleToModelCLM (I := I) (M := M) (E := E) s b T =
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T := rfl

/-- The inverse CLM of `bundleCLE`. -/
private def modelToBundleCLM (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SSpace s I b :=
  (bundleCLE (I := I) (M := M) (E := E) s b).symm.toContinuousLinearMap

/-- The "pre-compose into bundle" CLM, post-composing a model-fibre CLM
`Tensor0SModel s ℝ E →L[ℝ] ℝ` with `bundleToModelCLM`. We define this via
`arrowCongr`, which avoids metric-topology requirements: `arrowCongr` requires
only `IsTopologicalAddGroup` on its codomains, which `ℝ` and the bundle fibre
both satisfy. -/
private def precompBundleCLM (s : ℕ) (b : M) :
    (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (Tensor0SSpace s I b →L[ℝ] ℝ) :=

  ((bundleCLE (I := I) (M := M) (E := E) s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

@[simp] private lemma precompBundleCLM_apply (s : ℕ) (b : M)
    (f : Tensor0SModel s ℝ E →L[ℝ] ℝ) (T : Tensor0SSpace s I b) :
    precompBundleCLM (I := I) (M := M) (E := E) s b f T =
      f (Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
  rfl

/-- The `(0, s)` pointwise inner product packaged as a continuous bilinear
pairing on the bundle fibre `Tensor0SSpace s I b`.

We construct it by composing the model-fibre CLM with `precompBundleCLM` on
the codomain side (transferring the inner-CLM domain through the CLE) and then
with `bundleToModelCLM` on the source side. -/
def innerBundleCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SSpace s I b →L[ℝ] ℝ :=

  let stepA : Tensor0SModel s ℝ E →L[ℝ] (Tensor0SSpace s I b →L[ℝ] ℝ) :=
    (precompBundleCLM (I := I) (M := M) (E := E) s b).comp
      (innerModelCLM (I := I) (M := M) g s b)

  stepA.comp (bundleToModelCLM (I := I) (M := M) (E := E) s b)

@[simp] lemma innerBundleCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) S) := by
  rfl

/-! ## Algebraic properties

The `symm` and `pos` properties of `innerBundleCLM` follow from the
corresponding properties of `tensorInnerPointwise_0s` together with
linearity of the CLE `bundleCLE`. -/

/-- Symmetry of the bundle inner product: `inner b T S = inner b S T`. -/
lemma innerBundleCLM_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b S T := by
  rw [innerBundleCLM_apply, innerBundleCLM_apply]
  exact tensorInnerPointwise_0s_symm (I := I) (M := M) g b s _ _

/-- Positive-definiteness on the diagonal: `inner b T T > 0` for `T ≠ 0`. -/
lemma innerBundleCLM_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < innerBundleCLM (I := I) (M := M) g s b T T := by
  rw [innerBundleCLM_apply]

  have hTm :
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.Tensor0SSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (0 : Tensor0SSpace s I b) = 0 :=
      Tensor0SBundle.Tensor0SSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn :
      0 ≤ tensorInnerPointwise_0s (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
    tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_0s_eq_zero_iff
      (I := I) (M := M) g b s _).mp heq.symm

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
