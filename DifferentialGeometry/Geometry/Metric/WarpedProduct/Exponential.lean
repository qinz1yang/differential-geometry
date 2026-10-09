import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.ProductSlice
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry

private theorem halfLineT2 : T2Space (EuclideanHalfSpace 1) := by
  unfold EuclideanHalfSpace
  infer_instance

attribute [local instance] halfLineT2

private def halfLineMetric : SmoothRiemannianMetric (𝓡∂ 1) (EuclideanHalfSpace 1) :=
  (euclideanMetric (E := EuclideanSpace ℝ (Fin 1))).pullback
    (𝓡∂ 1) (𝓡∂ 1).contMDiff (fun _ => by
      rw [(𝓡∂ 1).hasMFDerivAt.mfderiv]
      exact Function.injective_id)

private theorem halfLineMetric_inner (p : EuclideanHalfSpace 1)
    (v w : EuclideanSpace ℝ (Fin 1)) :
    halfLineMetric.inner p v w = v 0 * w 0 := by
  unfold halfLineMetric
  erw [SmoothRiemannianMetric.pullback_inner,
    (𝓡∂ 1).hasMFDerivAt.mfderiv, euclideanMetric_inner]
  change inner ℝ v w = v 0 * w 0
  simp [PiLp.inner_apply, mul_comm]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem contMDiff_exponentialDepth (κ : ℝ) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (fun r : EuclideanHalfSpace 1 => Real.exp (-κ * r.val 0)) := by
  have hcoord : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (fun r : EuclideanHalfSpace 1 => r.val 0) :=
    (PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0).contDiff.contMDiff.comp
      (𝓡∂ 1).contMDiff
  exact Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hcoord)

def SmoothRiemannianMetric.exponentialWarpedEnd (g : SmoothRiemannianMetric I M)
    (κ : ℝ) : SmoothRiemannianMetric (I.prod (𝓡∂ 1)) (M × EuclideanHalfSpace 1) :=
  Diffeomorph.pullbackMetricCross
    (halfLineMetric.warpedProduct g
      (fun r => Real.exp (-κ * r.val 0)) (contMDiff_exponentialDepth κ)
      (fun _ => Real.exp_pos _))
    (Diffeomorph.prodComm I (𝓡∂ 1) M (EuclideanHalfSpace 1) ∞)

@[simp] theorem SmoothRiemannianMetric.exponentialWarpedEnd_inner
    (g : SmoothRiemannianMetric I M) (κ : ℝ) (p : M × EuclideanHalfSpace 1)
    (v w : TangentSpace (I.prod (𝓡∂ 1)) p) :
    (g.exponentialWarpedEnd κ).inner p v w =
      v.2 0 * w.2 0 + Real.exp (-2 * κ * p.2.val 0) * g.inner p.1 v.1 w.1 := by
  have hd : mfderiv (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I)
      (Prod.swap : M × EuclideanHalfSpace 1 → EuclideanHalfSpace 1 × M) p =
        (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 1))).prod
          (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 1))) := by
    exact (mfderiv_prodMk mdifferentiableAt_snd mdifferentiableAt_fst).trans
      (by rw [mfderiv_snd, mfderiv_fst]; rfl)
  have he : Real.exp (-κ * p.2.val 0) ^ 2 = Real.exp (-2 * κ * p.2.val 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [SmoothRiemannianMetric.exponentialWarpedEnd,
    Diffeomorph.pullbackMetricCross_inner, Diffeomorph.coe_prodComm]
  erw [hd, SmoothRiemannianMetric.warpedProduct_inner]
  change halfLineMetric.inner p.2 v.2 w.2 +
    Real.exp (-κ * p.2.val 0) ^ 2 * g.inner p.1 v.1 w.1 = _
  rw [halfLineMetric_inner, he]


theorem SmoothRiemannianMetric.exponentialWarpedEnd_sliceFst
    (g : SmoothRiemannianMetric I M) (κ : ℝ) (r : EuclideanHalfSpace 1) :
    (g.exponentialWarpedEnd κ).sliceFst r =
      scaleMetric (Real.exp (-2 * κ * r.val 0)) (Real.exp_pos _) g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.sliceFst_inner]
  erw [SmoothRiemannianMetric.exponentialWarpedEnd_inner]
  simp [scaleMetric]

end DifferentialGeometry
