import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingPatch_CX5

set_option autoImplicit false

/-! # CH12-S49 G2: `hmetric` (physical bound) from the order-zero C^k pullback error

* `pullback_inner_le_of_ckErr_S49`: `ckErr_S45 H g' c f 0 p < δ` gives
  `c · f^*g' ≤ (1 + δ) · h` on tangent vectors at `p` (order-zero binding of the metric error,
  same proof as `CuspEmbedding.abs_pullback_inner_sub_le`);
* `physical_metric_of_heq_S49`: transport of the bound along the actual-flow identification of the
  survivor representative `ψ` with the discrete map `f` (stage equality + `HEq` of the metric and
  of the points), the exact shape of the `hmetric` binder of `persistentModelPatch_of_dyadic_lifts_CX5`. -/

noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

/-- The pointwise `(0,2)`-tensor whose iterated derivatives are measured by `ckErr_S45`. -/
def scaledMetricError_S49 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier) :
    Tensor0SSpace 2 (𝓡 3) p :=
  ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
    (c • localPullInner g' f p - H.metric.inner p)).uncurryLeft

theorem scaledMetricError_apply_vec2_S49 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier)
    (v w : TangentSpace (𝓡 3) p) :
    scaledMetricError_S49 H g' c f p (vec2 v w) =
      c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w) -
        H.metric.inner p v w := by
  rw [← localPullInner_apply (I := 𝓡 3) (J := 𝓡 3) g' f p v w]
  rfl

theorem pullback_inner_le_of_ckErr_S49 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier) {δ : ℝ}
    (h0 : ckErr_S45 H g' c f 0 p < δ) (w : TangentSpace (𝓡 3) p) :
    c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ≤
      (1 + δ) * H.metric.inner p w w := by
  change tensor0SFiberNorm H.metric p 2 (scaledMetricError_S49 H g' c f p) < δ at h0
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := 𝓡 3) H.metric p
  have hb := abs_apply_le_sqrt_normSq0S (I := 𝓡 3) H.metric p 2 basis hON
    (scaledMetricError_S49 H g' c f p) (vec2 w w)
  rw [scaledMetricError_apply_vec2_S49, Fin.prod_univ_two] at hb
  simp only [vec2, Fin.isValue, ↓reduceIte, one_ne_zero] at hb
  rw [Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at hb
  have h1 := (abs_le.mp (hb.trans (mul_le_mul_of_nonneg_right h0.le
    (metric_inner_self_nonneg _ _ _)))).2
  linarith

/-- Transport of the physical pullback bound from the discrete map `f` (codomain `Q₂ = postStage`)
to the survivor representative `ψ` (codomain `Q₁ = stage (activeStage t)`). -/
theorem physical_metric_of_heq_S49 (H : FiniteVolumeHyperbolicModel.{u})
    {Q₁ Q₂ : OrientedThreeStage.{u}} (hQ : Q₁ = Q₂) (m₁ : Q₁.Metric) (m₂ : Q₂.Metric)
    (hm : HEq m₁ m₂) (ψ : H.Carrier → Q₁.Carrier) (f : H.Carrier → Q₂.Carrier)
    (A : Set H.Carrier) (hA : IsOpen A) (hψf : ∀ p ∈ A, HEq (ψ p) (f p)) {t : ℝ} (ht : 0 < t)
    (hf : ∀ p ∈ A, ∀ w : TangentSpace (𝓡 3) p,
      t⁻¹ * m₂.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ≤
        2 * H.metric.inner p w w) :
    ∀ p ∈ A, ∀ w : TangentSpace (𝓡 3) p,
      m₁.inner (ψ p) (mfderiv (𝓡 3) (𝓡 3) ψ p w) (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
        4 * t * H.metric.inner p w w := by
  subst hQ
  have hm' := eq_of_heq hm
  subst hm'
  intro p hp w
  have hψ : ψ =ᶠ[nhds p] f :=
    Filter.eventuallyEq_of_mem (hA.mem_nhds hp) fun q hq => eq_of_heq (hψf q hq)
  have hd : mfderiv (𝓡 3) (𝓡 3) ψ p = mfderiv (𝓡 3) (𝓡 3) f p := hψ.mfderiv_eq
  have hpt : ψ p = f p := eq_of_heq (hψf p hp)
  have h1 := mul_le_mul_of_nonneg_left (hf p hp w) ht.le
  rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at h1
  rw [hd, hpt]
  have h2 : 0 ≤ H.metric.inner p w w := metric_inner_self_nonneg _ _ _
  nlinarith

end GC.LongTime.Ch12
