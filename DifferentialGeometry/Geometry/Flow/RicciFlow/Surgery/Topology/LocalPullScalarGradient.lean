import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (I3)

universe u v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N]

theorem abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le
    (g : SmoothRiemannianMetric I3 M) (f : N → M) (hf : IsLocalDiffeomorph I3 I3 ∞ f)
    {q C : ℝ} (hq : 0 < q) (z : N)
    (h : ∀ w : TangentSpace I3 (f z),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (f z) w)| ≤
        C * metricScalarAt g (f z) * Real.sqrt (metricScalarAt g (f z)) *
          Real.sqrt (g.inner (f z) w w)) :
    ∀ v : TangentSpace I3 z,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
          (metricScalarAt (localPullMetric (scaleMetric q hq g) f hf)) z v)| ≤
        C * metricScalarAt (localPullMetric (scaleMetric q hq g) f hf) z *
          Real.sqrt (metricScalarAt (localPullMetric (scaleMetric q hq g) f hf) z) *
          Real.sqrt ((localPullMetric (scaleMetric q hq g) f hf).inner z v v) := by
  intro v
  have hR (y : N) : metricScalarAt (localPullMetric (scaleMetric q hq g) f hf) y =
      q⁻¹ * metricScalarAt g (f y) := by
    rw [metricScalarAt_localPull, metricScalarAt_scaleMetric]
  have hfun : metricScalarAt (localPullMetric (scaleMetric q hq g) f hf) =
      (fun r : ℝ => q⁻¹ * r) ∘ fun y => metricScalarAt g (f y) := by
    funext y
    rw [hR y, Function.comp_apply]
  have hg : MDifferentiableAt I3 𝓘(ℝ, ℝ) (metricScalarAt g) (f z) :=
    (metricScalar_smooth g).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt I3 I3 f z := hf.mdifferentiable (by decide) z
  have hcomp : MDifferentiableAt I3 𝓘(ℝ, ℝ) (fun y => metricScalarAt g (f y)) z :=
    hg.comp z hfd
  have hlin (a w : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => q⁻¹ * r) a w : ℝ) = q⁻¹ * w := by
    have hL := congrArg (fun L : ℝ →L[ℝ] ℝ => L w)
      ((mfderiv_eq_fderiv (f := fun r : ℝ => q⁻¹ * r) (x := a)).trans
        ((hasFDerivAt_id a).const_mul q⁻¹).fderiv)
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at hL
    exact hL
  have hlinD (a : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => q⁻¹ * r) a :=
    ((differentiableAt_id).const_mul q⁻¹).mdifferentiableAt
  have hd : (show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
        (metricScalarAt (localPullMetric (scaleMetric q hq g) f hf)) z v) =
      q⁻¹ * (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (f z) (mfderiv I3 I3 f z v)) := by
    have e1 : (mfderiv I3 𝓘(ℝ, ℝ)
          (metricScalarAt (localPullMetric (scaleMetric q hq g) f hf)) z v : ℝ) =
        (mfderiv I3 𝓘(ℝ, ℝ) ((fun r : ℝ => q⁻¹ * r) ∘ fun y => metricScalarAt g (f y)) z v :
          ℝ) :=
      congrArg (fun F : N → ℝ => (mfderiv I3 𝓘(ℝ, ℝ) F z v : ℝ)) hfun
    have e2 : (mfderiv I3 𝓘(ℝ, ℝ) ((fun r : ℝ => q⁻¹ * r) ∘ fun y => metricScalarAt g (f y)) z v :
          ℝ) = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => q⁻¹ * r) (metricScalarAt g (f z))
            (mfderiv I3 𝓘(ℝ, ℝ) (fun y => metricScalarAt g (f y)) z v) : ℝ) :=
      mfderiv_comp_apply z (hlinD _) hcomp v
    have e3 : (mfderiv I3 𝓘(ℝ, ℝ) (fun y => metricScalarAt g (f y)) z v : ℝ) =
        (mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (f z) (mfderiv I3 I3 f z v) : ℝ) :=
      mfderiv_comp_apply (g := metricScalarAt g) z hg hfd v
    exact e1.trans (e2.trans ((hlin _ _).trans (congrArg (fun r : ℝ => q⁻¹ * r) e3)))
  have hinner : (localPullMetric (scaleMetric q hq g) f hf).inner z v v =
      q * g.inner (f z) (mfderiv I3 I3 f z v) (mfderiv I3 I3 f z v) := by
    rw [localPullMetric_inner, scaleMetric_inner]
  have hw := h (mfderiv I3 I3 f z v)
  have hq' : 0 < q⁻¹ := inv_pos.mpr hq
  have hsq : Real.sqrt q⁻¹ * Real.sqrt q = 1 := by
    rw [← Real.sqrt_mul hq'.le, inv_mul_cancel₀ hq.ne', Real.sqrt_one]
  rw [hd, hR z, hinner, abs_mul, abs_of_pos hq', Real.sqrt_mul hq'.le,
    Real.sqrt_mul hq.le]
  calc q⁻¹ * |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (f z) (mfderiv I3 I3 f z v))|
      ≤ q⁻¹ * (C * metricScalarAt g (f z) * Real.sqrt (metricScalarAt g (f z)) *
          Real.sqrt (g.inner (f z) (mfderiv I3 I3 f z v) (mfderiv I3 I3 f z v))) :=
        mul_le_mul_of_nonneg_left hw hq'.le
    _ = C * (q⁻¹ * metricScalarAt g (f z)) *
          (Real.sqrt q⁻¹ * Real.sqrt (metricScalarAt g (f z))) *
          (Real.sqrt q *
            Real.sqrt (g.inner (f z) (mfderiv I3 I3 f z v) (mfderiv I3 I3 f z v))) := by
        linear_combination (-(C * metricScalarAt g (f z) * Real.sqrt (metricScalarAt g (f z)) *
          Real.sqrt (g.inner (f z) (mfderiv I3 I3 f z v) (mfderiv I3 I3 f z v))) * q⁻¹) * hsq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
