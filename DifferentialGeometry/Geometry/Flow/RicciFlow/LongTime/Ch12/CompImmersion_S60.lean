import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Metric.Convergence.IntegrableVelocity

set_option autoImplicit false

/-!
# CH12-S60 / G3 (aux): order-0 smallness of `ckErr_S45` forces `0 < c` and an injective differential

If `ckErr_S45 H g' c f 0 q < 1` then `c > 0` and `mfderiv f q` is injective
(Cauchy-Schwarz `abs_tensor02_apply_le_norm_mul` on the error tensor `c f^*g' - h`).
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- no direction `v ≠ 0` has `c * g'(df v, df v) ≤ 0` when the order-0 error is `< 1`. -/
theorem ckErr0_no_degenerate_S60 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (q : H.Carrier)
    (hq : ckErr_S45 H g' c f 0 q < 1) (v : TangentSpace (𝓡 3) q) (hv : v ≠ 0)
    (hle : c * g'.inner (f q) (mfderiv (𝓡 3) (𝓡 3) f q v) (mfderiv (𝓡 3) (𝓡 3) f q v) ≤ 0) :
    False := by
  have hpos : 0 < H.metric.inner q v v := H.metric.pos q v hv
  unfold ckErr_S45 at hq
  have hCS := abs_tensor02_apply_le_norm_mul (E := EuclideanSpace ℝ (Fin 3))
    (I := 𝓡 3) (M := H.Carrier) H.metric
    (iteratedMetricCovariantDerivative H.metric 2
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f q - H.metric.inner q)).uncurryLeft) 0 q) v
  have hval : (iteratedMetricCovariantDerivative H.metric 2
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f q - H.metric.inner q)).uncurryLeft) 0 q) ![v, v] =
      c * g'.inner (f q) (mfderiv (𝓡 3) (𝓡 3) f q v) (mfderiv (𝓡 3) (𝓡 3) f q v) -
        H.metric.inner q v v := by
    have h0 : ∀ (L : TangentSpace (𝓡 3) q →L[ℝ] TangentSpace (𝓡 3) q →L[ℝ] ℝ),
        (((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          L).uncurryLeft : Tensor0SSpace 2 (𝓡 3) q) ![v, v] = L v v := fun L => by
      rfl
    refine (h0 (c • localPullInner g' f q - H.metric.inner q)).trans ?_
    simp [localPullInner_apply]
  rw [hval] at hCS
  unfold tensor0SFiberNorm at hq
  have habs : H.metric.inner q v v ≤
      |c * g'.inner (f q) (mfderiv (𝓡 3) (𝓡 3) f q v) (mfderiv (𝓡 3) (𝓡 3) f q v) -
        H.metric.inner q v v| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  nlinarith [mul_lt_mul_of_pos_right hq hpos]

theorem ckErr0_immersion_S60 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (q : H.Carrier)
    (hq : ckErr_S45 H g' c f 0 q < 1) :
    0 < c ∧ Function.Injective (mfderiv (𝓡 3) (𝓡 3) f q) := by
  refine ⟨?_, ?_⟩
  · by_contra hc
    obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 3))
    refine ckErr0_no_degenerate_S60 H g' c f q hq v hv ?_
    have : 0 ≤ g'.inner (f q) (mfderiv (𝓡 3) (𝓡 3) f q v) (mfderiv (𝓡 3) (𝓡 3) f q v) := by
      by_cases hz : mfderiv (𝓡 3) (𝓡 3) f q v = 0
      · simp [hz]
      · exact (g'.pos _ _ hz).le
    nlinarith [not_lt.mp hc]
  · intro v w hvw
    by_contra hne
    refine ckErr0_no_degenerate_S60 H g' c f q hq (v - w) (sub_ne_zero.mpr hne) ?_
    rw [map_sub, hvw, sub_self]
    simp

end GC.LongTime.Ch12
