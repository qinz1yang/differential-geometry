import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompGeometry_S71
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompBridge_S60

set_option autoImplicit false

/-!
# CH12-S71 / G3: the `ckErr_S45` bridge for `f ∘ Φ` on `↥U`, `Φ` a partial diffeomorphism

Local version of `ckErr_comp_bridge_S60`: `Φ : PartialDiffeomorph` with `U ⊆ Φ.source` in place of a
global `e : H.Carrier ≃ₘ H.Carrier`; naturality is `metricDerivNorm_localPullback_S71`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem ckErr_comp_bridge_S71 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c) (f : H.Carrier → N)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H.Carrier (∞ : WithTop ℕ∞))
    (U : Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ Φ.source)
    (hΦ : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → H.Carrier) y))
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f ((Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier)))
    (hinj : ∀ y ∈ (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    {δ ε : ℝ} {p : ℕ}
    (habs : ∀ A gHat gBase : SmoothRiemannianMetric (𝓡 3) U,
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q gHat gBase gBase x ≤ δ) →
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gHat gHat x ≤ δ) →
      ∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gBase gBase x ≤ ε)
    (hE : ∀ q : ℕ, q ≤ p → ∀ x ∈ (U : Set H.Carrier),
      ckErr_S45 H H.metric 1 (Φ : H.Carrier → H.Carrier) q x ≤ δ)
    (hF : ∀ q : ℕ, q ≤ p → ∀ y ∈ (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
      ckErr_S45 H g' c f q y ≤ δ) :
    ∀ q : ℕ, q ≤ p → ∀ x ∈ (U : Set H.Carrier),
      ckErr_S45 H g' c (f ∘ (Φ : H.Carrier → H.Carrier)) q x ≤ ε := by
  intro q hq x hx
  have he := contMDiffOn_partial_S71 H Φ U hU
  have hFe := contMDiffOn_comp_partial_S71 H Φ U hU f hf
  have hinjFe := mfderiv_inj_comp_partial_S71 H Φ U hU hΦ f hf hinj
  have h1 : ∀ y : U, ∀ r : ℕ, r ≤ p →
      metricDerivNorm (I := 𝓡 3) r
        (localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU)
          (subset_partialImage_S71 H Φ U hU) (H.metric.restrictOpen (partialImage_S71 Φ U hU)))
        (H.metric.restrictOpen U) (H.metric.restrictOpen U) y ≤ δ := by
    intro y r hr
    rw [← pullbackRestrict_self_eq_local_S71 H Φ U hU he hΦ,
      ← ckErr_S45_eq_metricDerivNorm_S57 H H.metric 1 one_pos (Φ : H.Carrier → H.Carrier) U he hΦ
        r y]
    exact hE r hr y y.2
  have h2 : ∀ y : U, ∀ r : ℕ, r ≤ p →
      metricDerivNorm (I := 𝓡 3) r
        (localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU)
          (subset_partialImage_S71 H Φ U hU)
          (pullbackRestrict_S57 H (scaleMetric (I := 𝓡 3) c hc g') f (partialImage_S71 Φ U hU)
            hf hinj))
        (localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU)
          (subset_partialImage_S71 H Φ U hU) (H.metric.restrictOpen (partialImage_S71 Φ U hU)))
        (localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU)
          (subset_partialImage_S71 H Φ U hU) (H.metric.restrictOpen (partialImage_S71 Φ U hU)))
        y ≤ δ := by
    intro y r hr
    rw [metricDerivNorm_localPullback_S71 Φ U hU (partialImage_S71 Φ U hU)
      (subset_partialImage_S71 H Φ U hU) _ _ _ r y,
      ← ckErr_S45_eq_metricDerivNorm_S57 H g' c hc f (partialImage_S71 Φ U hU) hf hinj r
        ⟨Φ y, y, y.2, rfl⟩]
    exact hF r hr (Φ y) ⟨y, y.2, rfl⟩
  have key := habs _ _ _ h1 h2 ⟨x, hx⟩ q hq
  rw [ckErr_S45_eq_metricDerivNorm_S57 H g' c hc (f ∘ (Φ : H.Carrier → H.Carrier)) U hFe hinjFe q
      ⟨x, hx⟩,
    pullbackRestrict_comp_eq_local_S71 H (scaleMetric (I := 𝓡 3) c hc g') f Φ U hU hΦ hf hinj]
  exact key

end GC.LongTime.Ch12
