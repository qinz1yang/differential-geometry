import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import Mathlib.Analysis.Calculus.Gradient.Basic



noncomputable section

open Bundle Manifold InnerProductSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry.Connection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace


def conformalEuclideanMetric (f : V → ℝ) (hf : ContDiff ℝ ∞ f) :
    SmoothRiemannianMetric 𝓘(ℝ, V) V :=
  conformalMetric (euclideanMetric V) f hf.contMDiff

@[simp] theorem conformalEuclideanMetric_inner (f : V → ℝ)
    (hf : ContDiff ℝ ∞ f) (x v w : V) :
    (conformalEuclideanMetric f hf).inner x v w =
      Real.exp (2 * f x) * inner ℝ v w := rfl

private theorem conformal_bilinear_hasFDerivAt {f : V → ℝ} {z : V}
    (hf : DifferentiableAt ℝ f z) :
    HasFDerivAt (fun y => Real.exp (2 * f y) • (innerSL ℝ (E := V)))
      ((Real.exp (2 * f z) • ((2 : ℝ) • fderiv ℝ f z)).smulRight (innerSL ℝ)) z := by
  exact ((hf.hasFDerivAt.const_mul 2).exp).smul_const (innerSL ℝ (E := V))

private theorem conformal_bilinear_coercive (f : V → ℝ) (z : V) :
    IsCoercive (Real.exp (2 * f z) • (innerSL ℝ (E := V))) := by
  refine ⟨Real.exp (2 * f z), Real.exp_pos _, ?_⟩
  intro v
  change Real.exp (2 * f z) * ‖v‖ * ‖v‖ ≤ Real.exp (2 * f z) * inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  nlinarith

variable [FiniteDimensional ℝ V]


def conformalEuclideanCorrection (f : V → ℝ) (z v w : V) : V :=
  fderiv ℝ f z v • w + fderiv ℝ f z w • v - inner ℝ v w • gradient f z

private theorem conformal_koszulVec {f : V → ℝ} {z : V}
    (hf : DifferentiableAt ℝ f z) (v w : V) :
    MetricKoszul.koszulVec (conformal_bilinear_coercive f z)
      (fderiv ℝ (fun y => Real.exp (2 * f y) • (innerSL ℝ (E := V))) z) v w =
      conformalEuclideanCorrection f z v w := by
  apply (conformal_bilinear_coercive f z).bilin_injective
  rw [MetricKoszul.koszulVec, IsCoercive.apply_sharp]
  ext u
  rw [MetricKoszul.koszul_cov_apply, (conformal_bilinear_hasFDerivAt hf).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  change (1 / 2 : ℝ) *
      (Real.exp (2 * f z) * (2 * fderiv ℝ f z v) * inner ℝ w u +
       Real.exp (2 * f z) * (2 * fderiv ℝ f z w) * inner ℝ v u -
       Real.exp (2 * f z) * (2 * fderiv ℝ f z u) * inner ℝ v w) =
    Real.exp (2 * f z) * inner ℝ (conformalEuclideanCorrection f z v w) u
  simp only [conformalEuclideanCorrection, inner_sub_left,
    inner_add_left, real_inner_smul_left, inner_gradient_left]
  ring




theorem leviCivita_conformalEuclidean {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    {Y : V → V} {z : V} (hY : DifferentiableAt ℝ Y z) (v : V) :
    LeviCivita (conformalEuclideanMetric f hf) Y z v =
      fderiv ℝ Y z v + conformalEuclideanCorrection f z v (Y z) := by
  let B : V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun y => Real.exp (2 * f y) • innerSL ℝ
  have hB : (fun y => tangentBilinearFormToModel y
      ((conformalEuclideanMetric f hf).inner y)) = B := by
    funext y
    ext u w
    rfl
  have hYs : MDifferentiableAt 𝓘(ℝ, V) (𝓘(ℝ, V).prod 𝓘(ℝ, V))
      (fun y => (⟨y, Y y⟩ : TangentBundle 𝓘(ℝ, V) V)) z := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_id, ?_⟩
    convert! hY.mdifferentiableAt with y
    simp
  have h := cov_eq_fderiv_add (conformalEuclideanMetric f hf) B
    (Filter.EventuallyEq.of_eq hB)
    (conformal_bilinear_hasFDerivAt (hf.differentiable (by simp) z)).differentiableAt
    (conformal_bilinear_coercive f z) Y hYs v
  change LeviCivita (conformalEuclideanMetric f hf) Y z v = _ at h
  rw [conformal_koszulVec (hf.differentiable (by simp) z)] at h
  exact h

end DifferentialGeometry.Geometry
