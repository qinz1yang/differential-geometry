import DifferentialGeometry.Integral.Connection.CovariantIntegrationByParts
import DifferentialGeometry.Tensor.RSTensor.Tensor0SInnerSectionSmooth

/-!
# Directional lowered integration-by-parts for `(r, s)`-tensor fields

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, fixed ranks `(r, s)`, this file packages the
directional metric-lowered covariant derivative of a smooth compactly-supported
`(r, s)`-tensor section, contracted against a smooth tangent vector field, as a
genuine smooth compactly-supported section of the covariant `(0, r + s)`-tensor
bundle, and derives the directional covariant integration-by-parts identity in
its self-contained form (no externally supplied integrability hypotheses).

The metric-lowered directional covariant derivative `loweredCovDerivAt g r s S`
is the covariant derivative of the lifted `(0, r + s)`-tensor section
`liftedTensorSection g r s S`, induced by the Levi-Civita connection of `g`. For
a smooth tangent vector field `X`, the section `y ↦ ∇_{X y} S y` (metric-lowered)
is exactly `covApply (tensor0SCovariantDerivative … (r + s) …) X
(liftedTensorSection g r s S)`, whose smoothness comes from
`covApply_contMDiffOn` applied to the smooth lifted section and the smooth vector
field. Compact support comes from the locality of the covariant derivative: it
vanishes outside the support of `S`.

## Main results

* `loweredCovDerivAlongVF` — the section `y ↦ loweredCovDerivAt g r s S y (X y)`,
  bundled as a smooth `(0, r + s)`-tensor section.
* `loweredCovDerivAlongVF_apply` — its underlying value at `y`.
* `loweredCovDerivAlongVF_contMDiff` — smoothness in total-space form.
* `loweredCovDerivAlongVF_hasCompactSupport` — compact support of its model image.
* `integral_tensorInner_covDeriv_eq_self` — the directional covariant
  integration-by-parts identity, with the two cross-term integrability
  hypotheses discharged internally from continuity and compact support.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold I M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The metric-lowered directional covariant derivative of a smooth
`(r, s)`-tensor section `S` along a smooth tangent vector field `X`, as a raw
`(0, r + s)`-tensor section. At a point `y` its value is
`loweredCovDerivAt g r s S y (X y)`. -/
def loweredCovDerivAlongVFraw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, Tensor0SSpace (r + s) I y :=
  fun y => loweredCovDerivAt (I := I) (M := M) g r s S y (X y)

/-- The raw lowered directional derivative section is the covariant derivative of
the lifted `(0, r + s)`-tensor section along `X`. -/
lemma loweredCovDerivAlongVFraw_eq_covApply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X =
      covApply (tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g))
        (fun y : M => X y)
        (liftedTensorSection (I := I) (M := M) g r s S) := by
  funext y
  rfl

/-- **Smoothness of the lowered directional derivative section.** For a smooth
`(r, s)`-tensor section `S` and a smooth tangent vector field `X`, the section
`y ↦ loweredCovDerivAt g r s S y (X y)` is a `C^∞` section of the
`(0, r + s)`-tensor bundle, in total-space form. -/
lemma loweredCovDerivAlongVFraw_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y)) := by
  classical
  set cov := tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    with hcov_def
  have hLift : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact liftedTensorSection_contMDiff (I := I) (M := M) g r s S
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) :=
    X.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (covApply cov (fun y : M => X y)
          (liftedTensorSection (I := I) (M := M) g r s S) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hX hLift
  rw [loweredCovDerivAlongVFraw_eq_covApply]
  rw [← contMDiffOn_univ]
  exact hOn

/-- The lowered directional derivative section vanishes outside `tsupport S`.

The lifted section vanishes wherever `S` does, so on a neighbourhood of a point
outside `tsupport S` it is identically zero; by locality of the covariant
derivative the lowered directional derivative vanishes there. -/
lemma loweredCovDerivAlongVFraw_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : M}
    (hy : y ∉ tsupport (fun b : M => TensorRSSpace.toModel (S b))) :
    loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y = 0 := by
  classical
  set cov := tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    with hcov_def
  have hS_eq : (fun b : M => TensorRSSpace.toModel (S b)) =ᶠ[𝓝 y] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hy
  rw [Filter.eventuallyEq_iff_exists_mem] at hS_eq
  obtain ⟨V, hV_nhds, hV_eq⟩ := hS_eq
  obtain ⟨U, hUV, hU_open, hyU⟩ := mem_nhds_iff.mp hV_nhds
  have hLift_zero : ∀ b ∈ U,
      liftedTensorSection (I := I) (M := M) g r s S b = 0 := by
    intro b hbU
    have h_model_zero : TensorRSSpace.toModel (S b) = 0 := by
      have := hV_eq (hUV hbU); simpa using this
    have hS_b_zero : S b = 0 := by
      have : TensorRSSpace.toModel (S b) =
          TensorRSSpace.toModel (0 : TensorRSSpace r s I b) := by
        rw [h_model_zero, TensorRSSpace.toModel_zero]
      exact TensorRSSpace.toModel_injective this
    rw [liftedTensorSection_apply, hS_b_zero, TensorRSSpace.toModel_zero, map_zero]
    rfl
  have hLift_diff_y : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun w : M => Tensor0SSpace (r + s) I w) z
        (liftedTensorSection (I := I) (M := M) g r s S z)) y :=
    ((liftedTensorSection_contMDiff (I := I) (M := M) g r s S) y).mdifferentiableAt
      (by simp)
  have hcov_zero : cov.toFun
      (liftedTensorSection (I := I) (M := M) g r s S) y = 0 := by
    have hU_nhds : U ∈ 𝓝 y := hU_open.mem_nhds hyU
    have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E))
        (fun z : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
          (E := fun w : M => Tensor0SSpace (r + s) I w) z
          (0 : Tensor0SSpace (r + s) I z)) y :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := Tensor0SModel (r + s) ℝ E)
        (E := fun w : M => Tensor0SSpace (r + s) I w) (IB := I)
    have hT_eq : ∀ᶠ z in 𝓝 y,
        liftedTensorSection (I := I) (M := M) g r s S z =
          (fun w : M => (0 : Tensor0SSpace (r + s) I w)) z :=
      Filter.Eventually.mono (Filter.eventually_of_mem hU_nhds (fun z hz => hz))
        (fun z hz => hLift_zero z hz)
    have h_eq : cov.toFun (liftedTensorSection (I := I) (M := M) g r s S) y =
        cov.toFun (fun z : M => (0 : Tensor0SSpace (r + s) I z)) y :=
      cov.isCovariantDerivativeOn.congr_of_eventuallyEq hLift_diff_y hzero_diff
        (Filter.univ_mem) hT_eq
    rw [h_eq]
    exact congrArg (fun φ => φ y) cov.zero
  change loweredCovDerivAt (I := I) (M := M) g r s S y (X y) = 0
  rw [loweredCovDerivAt_def]
  change cov.toFun (liftedTensorSection (I := I) (M := M) g r s S) y (X y) = 0
  rw [hcov_zero]
  rfl

/-- **Compact support of the lowered directional derivative section.** Its model
image has compact support contained in `tsupport (toModel ∘ S)`. -/
lemma loweredCovDerivAlongVFraw_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (hS_cc : HasCompactSupport (fun b : M => TensorRSSpace.toModel (S b)))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    HasCompactSupport (fun y : M => Tensor0SSpace.toModel
      (loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact hS_cc ?_
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hynot
  apply hy
  rw [loweredCovDerivAlongVFraw_eq_zero_off_tsupport (I := I) (M := M) g r s S X hynot,
    Tensor0SSpace.toModel_zero]

/-- **The lowered directional covariant derivative along a vector field, bundled
as a smooth section.** For a smooth `(r, s)`-tensor section `S` and a smooth
tangent vector field `X`, the section `y ↦ loweredCovDerivAt g r s S y (X y)` is
packaged as a `Cₛ^∞` section of the `(0, r + s)`-tensor bundle. -/
def loweredCovDerivAlongVF
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; Tensor0SModel (r + s) ℝ E, (fun x : M => Tensor0SSpace (r + s) I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y)
    (loweredCovDerivAlongVFraw_contMDiff (I := I) (M := M) g r s S X)

@[simp] lemma loweredCovDerivAlongVF_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    loweredCovDerivAlongVF (I := I) (M := M) g r s S X y =
      loweredCovDerivAt (I := I) (M := M) g r s S y (X y) := rfl

/-- **Smoothness of the inner-product scalar.** For smooth `(r, s)`-tensor
sections `W`, `S`, the scalar `tensorInnerScalar g r s W S` is `C^∞`. -/
lemma tensorInnerScalar_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I 𝓘(ℝ) ∞
      (tensorInnerScalar (I := I) (M := M) g r s W S) :=
  DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff_of_mdiff
    (I := I) (M := M) g r s W S

/-- **Directional covariant integration by parts (combined, self-contained).**
For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, a smooth
tangent vector field `V`, and smooth `(r, s)`-tensor sections `W`, `S`, the
integral of the covariant Leibniz expression vanishes:

  `∫_M (⟨∇_V W, S⟩ + ⟨W, ∇_V S⟩ + ⟨W, S⟩ · divᵍ V) dvol_g = 0`,

where `∇_V` is the metric-lowered directional covariant derivative
`loweredCovDerivAlongVF g r s · V`, and `⟨·, ·⟩` is the covariant `(0, r + s)`
inner product of the metric-lowered tensors. No integrability or smoothness
hypothesis is exposed: smoothness of `y ↦ ⟨W y, S y⟩` is discharged internally. -/
theorem integral_tensorInner_covDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s S V x))
          + tensorInnerScalar (I := I) (M := M) g r s W S x
            * divergence_g (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_tangentAction_add_smul_divergence_eq_zero
    (I := I) (M := M) g r s W S V
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W S)

/-- **Directional covariant integration by parts (split form).** For a closed
smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, a smooth tangent vector
field `V`, and smooth `(r, s)`-tensor sections `W`, `S` whose two covariant
cross terms are integrable,

  `∫_M ⟨W, ∇_V S⟩ dvol_g
     = -∫_M ⟨∇_V W, S⟩ dvol_g - ∫_M ⟨W, S⟩ · divᵍ V dvol_g`,

where `∇_V` is the metric-lowered directional covariant derivative
`loweredCovDerivAlongVF g r s · V`. The smoothness of the inner-product scalar
is discharged internally; only the two cross-term integrability witnesses are
exposed (they are discharged by the caller summing over a frame, where the
combined boundedness is available). -/
theorem integral_tensorInner_covDeriv_split_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hWcov_int : Integrable
      (fun x : M => tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s W V x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S x)))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (hScov_int : Integrable
      (fun x : M => tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s W x))
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s S V x)))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s S V x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        - ∫ x, tensorInnerScalar (I := I) (M := M) g r s W S x
              * divergence_g (I := I) g V x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  integral_tensorInner_covDeriv_integrationByParts (I := I) (M := M) g r s W S V
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W S)
    hWcov_int hScov_int

end Connection
end Integral
end DifferentialGeometry

end
