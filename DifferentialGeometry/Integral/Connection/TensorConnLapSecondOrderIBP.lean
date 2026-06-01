import DifferentialGeometry.Integral.Connection.TensorConnLapGreenIdentity
import DifferentialGeometry.Integral.Connection.TensorConnLapLoweredIBP
import DifferentialGeometry.Integral.Connection.TensorRicciCommutator
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartFrameTrace

/-!
# Second-order directional integration by parts for the `(0, 2)` connection-Laplacian Green identity

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file develops the *second-order directional*
integration-by-parts identity that lies at the heart of the integrated Green
identity for the rough (connection) Laplacian on `(0, 2)`-tensor fields.

The per-direction content is: for a smooth tangent vector field `B`, the
integral of the lowered inner product of the two first directional covariant
derivatives `(∇_B T)`, `(∇_B v)` integrates by parts onto the second covariant
derivative `(∇_B (∇_B T))` of the first argument plus a divergence correction:

```
∫_M ⟨(∇_B T)ᵇ, (∇_B v)ᵇ⟩ dvol_g
  = − ∫_M ⟨(∇_B (∇_B T))ᵇ, vᵇ⟩ dvol_g
    − ∫_M ⟨(∇_B T)ᵇ, vᵇ⟩ · divᵍ B dvol_g,
```

where `(·)ᵇ` denotes metric index-lowering of the `(0, 2)`-tensor value to a
covariant `(0, 0 + 2)`-tensor and `⟨·, ·⟩` the covariant `(0, 0 + 2)` inner
product.

The key device is the observation that the *un-lowered* first directional
covariant derivative `y ↦ ∇_{B y} T y` of a smooth `(0, 2)`-tensor section `T`
is itself a smooth `(0, 2)`-tensor section (a section of the
`TensorRSModel 0 2` bundle), so the committed *first-order* covariant
integration-by-parts identity `integral_tensorInner_covDeriv_split_eq`, applied
at rank `(0, 2)` to the first directional derivative in place of the original
section, immediately yields the second-order identity. No new
integration-by-parts machinery is needed at the lowered rank `(0, 0 + 2)`; the
metric index-lowering of an `(r, s)`-covariant derivative coincides with the
lowered directional derivative `loweredCovDerivAt`
(`loweredCovDerivAt_eq_lower_tensorCovDerivAt`), so the two presentations agree
on the nose.

## Main results

* `covDerivAlongVFSection` — the un-lowered first directional covariant
  derivative `y ↦ ∇_{B y} T y` of a smooth `(0, 2)`-tensor section `T` along a
  smooth tangent vector field `B`, bundled as a smooth `(0, 2)`-tensor section.
* `covDerivAlongVFSection_lowered_eq` — its metric-lowering coincides
  pointwise with the lowered directional derivative `loweredCovDerivAt`.
* `covDerivAlong_covDerivAlongVFSection_eq` — the value `∇_B (∇_B T)` of the
  covariant derivative of the first directional derivative is the
  un-symmetrised second covariant derivative `tensorSecondCovDeriv g 0 2 B B T`
  plus the `∇_{∇_B B} T` correction.
* `toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq` — the metric
  index-lowering of the lowered second directional derivative is the lowering of
  that Hessian-plus-correction tensor.
* `integral_secondOrder_combined_eq_zero` — the headline per-direction
  second-order combined integration-by-parts identity (the integral of
  `⟨(∇_B (∇_B T))ᵇ, vᵇ⟩ + ⟨(∇_B T)ᵇ, (∇_B v)ᵇ⟩ + ⟨∇_B T, v⟩ · divᵍ B` vanishes),
  obtained by applying the committed first-order combined identity at rank
  `(0, 2)` with the first directional derivative in place of the original
  section.
* `covDerivAlong_secondOrder_eq_fixedFrame_summand` — the per-direction
  un-lowered second-order term is the summand of `rawTensorConnLap_fixedFrame`;
  summed over an orthonormal frame this reconstructs the rough Laplacian.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The un-lowered first directional covariant derivative `y ↦ ∇_{B y} T y` of a
smooth `(0, 2)`-tensor section `T` along a smooth tangent vector field `B`, as a
raw `(0, 2)`-tensor section. -/
def covDerivAlongVFraw
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace 0 2 I y :=
  covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

@[simp] lemma covDerivAlongVFraw_apply
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFraw (I := I) (M := M) g T B y =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

/-- **Smoothness of the un-lowered first directional covariant derivative.** For
a smooth `(0, 2)`-tensor section `T` and a smooth tangent vector field `B`, the
section `y ↦ ∇_{B y} T y` is a `C^∞` section of the `(0, 2)`-tensor bundle, in
total-space form. -/
lemma covDerivAlongVFraw_contMDiff
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y
        (covDerivAlongVFraw (I := I) (M := M) g T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

/-- **The un-lowered first directional covariant derivative, bundled as a smooth
section.** -/
def covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFraw (I := I) (M := M) g T B y)
    (covDerivAlongVFraw_contMDiff (I := I) (M := M) g T B)

@[simp] lemma covDerivAlongVFSection_apply
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSection (I := I) (M := M) g T B y =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

/-- **The lowering of the un-lowered first directional derivative is the lowered
directional derivative.** At each point `y`, the metric index-lowering of
`(covDerivAlongVFSection g T B) y = ∇_{B y} T y` equals the model coercion of the
lowered directional derivative `loweredCovDerivAt g 0 2 T y (B y)`. -/
lemma covDerivAlongVFSection_lowered_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 2 y
        (TensorRSSpace.toModel (covDerivAlongVFSection (I := I) (M := M) g T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 T y (B y)) := by
  rw [(loweredCovDerivAt_eq_lower_tensorCovDerivAt
    (I := I) (M := M) g T y (B y))]
  rfl

/-- The lifted `(0, 0 + 2)`-tensor section of the first directional derivative
coincides, after model coercion, with the lowered directional derivative. -/
lemma toModel_liftedTensorSection_covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSection_lowered_eq (I := I) (M := M) g T B y

/-- **The second directional derivative is the Hessian plus the frame
correction.** The covariant derivative of the first directional derivative
`covDerivAlongVFSection g T B` along `B` equals the un-symmetrised second
covariant derivative `tensorSecondCovDeriv g 0 2 B B T` plus the correction
`∇_{(∇_B B)(y)} T`. -/
lemma covDerivAlong_covDerivAlongVFSection_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T B) B y =
      tensorSecondCovDeriv (I := I) g 0 2
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g 0 2 =
      tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) from rfl]
  abel

/-- The model coercion of the lowered second directional derivative
`loweredCovDerivAlongVF g 0 2 (∇_B T) B x` equals the metric index-lowering of
the un-symmetrised second covariant derivative `tensorSecondCovDeriv g 0 2 B B T`
plus the lowering of the `∇_{∇_B B} T` correction. -/
lemma toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T B) B x) =
      lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g 0 2
            (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) x +
          (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
            (fun b : M => T b) x
            ((LeviCivita (I := I) g).toFun (fun b : M => B b) x (B x)))) := by
  rw [loweredCovDerivAlongVF_apply]
  rw [loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g
    (covDerivAlongVFSection (I := I) (M := M) g T B) x (B x)]
  congr 1
  exact congrArg TensorRSSpace.toModel
    (covDerivAlong_covDerivAlongVFSection_eq (I := I) (M := M) g T B x)

/-- **Per-direction second-order combined integration by parts.** For smooth
`(0, 2)`-tensor sections `T`, `v` and a smooth tangent vector field `B` on a
closed Riemannian manifold, the integral of the second-order covariant Leibniz
expression vanishes:

```
∫_M (⟨(∇_B (∇_B T))ᵇ, vᵇ⟩ + ⟨(∇_B T)ᵇ, (∇_B v)ᵇ⟩ + ⟨∇_B T, v⟩ · divᵍ B) dvol_g = 0.
```

No integrability hypothesis is exposed: it is discharged internally by the
committed first-order combined identity (which itself relies only on smoothness
of the inner-product scalar, discharged through `tensorInnerScalar_contMDiff`). -/
theorem integral_secondOrder_combined_eq_zero
    (g : SmoothRiemannianMetric I M)
    (T v : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) B x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2 v x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))
          + tensorInnerScalar (I := I) (M := M) g 0 2
              (covDerivAlongVFSection (I := I) (M := M) g T B) v x
            * divergence_g (I := I) g B x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g T B) v B

/-- **Per-direction un-lowered second-order term as the fixed-frame summand.**
The un-lowered second-order covariant term
`∇_B (∇_B T) (b) − ∇_{(∇_B B)(b)} T` equals the summand of
`rawTensorConnLap_fixedFrame` for the frame value `B b`. This is the bridge
between the per-direction second-order IBP terms of this file and the
fixed-frame raw connection Laplacian. -/
lemma covDerivAlong_secondOrder_eq_fixedFrame_summand
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T B) B b -
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) b
        (covApply (LeviCivita (I := I) g) (fun y : M => B y) (fun y : M => B y) b) =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
            (fun y : M => B y) (fun y : M => T y)) b (B b) -
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) := rfl

end Connection
end Integral
end DifferentialGeometry

end
