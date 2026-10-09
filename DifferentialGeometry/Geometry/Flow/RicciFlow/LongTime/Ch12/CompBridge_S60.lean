import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompGeometry_S60

set_option autoImplicit false

/-!
# CH12-S60 / G2: the `ckErr_S45` bridge for `f ∘ e` on `↥U`

`ckErr_comp_bridge_S60`: under the abstract reference-change fact `habs` for the manifold `↥U`
(supplied by `ckComp_abstract_S60`), smallness of `ckErr_S45 H H.metric 1 e` on `U` and of
`ckErr_S45 H g' c f` on `e '' U` (orders `≤ p`) gives smallness of `ckErr_S45 H g' c (f ∘ e)` on `U`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem ckErr_comp_bridge_S60 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c) (f : H.Carrier → N)
    (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (e '' (U : Set H.Carrier)))
    (hinj : ∀ y ∈ e '' (U : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    {δ ε : ℝ} {p : ℕ}
    (habs : ∀ A gHat gBase : SmoothRiemannianMetric (𝓡 3) U,
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q gHat gBase gBase x ≤ δ) →
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gHat gHat x ≤ δ) →
      ∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gBase gBase x ≤ ε)
    (hE : ∀ q : ℕ, q ≤ p → ∀ x ∈ (U : Set H.Carrier), ckErr_S45 H H.metric 1 e q x ≤ δ)
    (hF : ∀ q : ℕ, q ≤ p → ∀ y ∈ e '' (U : Set H.Carrier), ckErr_S45 H g' c f q y ≤ δ) :
    ∀ q : ℕ, q ≤ p → ∀ x ∈ (U : Set H.Carrier), ckErr_S45 H g' c (f ∘ e) q x ≤ ε := by
  intro q hq x hx
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e : H.Carrier → H.Carrier) U :=
    e.contMDiff.contMDiffOn
  have hinje : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) y) :=
    fun y _ => mfderiv_inj_S60 H e y
  have hFe := contMDiffOn_comp_diff_S60 H e U f hf
  have hinjFe := mfderiv_inj_comp_diff_S60 H e U f hf hinj
  have h1 : ∀ y : U, ∀ r : ℕ, r ≤ p →
      metricDerivNorm (I := 𝓡 3) r
        (fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
          (H.metric.restrictOpen (diffImage_S60 H e U)))
        (H.metric.restrictOpen U) (H.metric.restrictOpen U) y ≤ δ := by
    intro y r hr
    rw [← pullbackRestrict_self_eq_fixed_S60 H e U he hinje,
      ← ckErr_S45_eq_metricDerivNorm_S57 H H.metric 1 one_pos e U he hinje r y]
    exact hE r hr y y.2
  have h2 : ∀ y : U, ∀ r : ℕ, r ≤ p →
      metricDerivNorm (I := 𝓡 3) r
        (fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
          (pullbackRestrict_S57 H (scaleMetric (I := 𝓡 3) c hc g') f (diffImage_S60 H e U) hf hinj))
        (fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
          (H.metric.restrictOpen (diffImage_S60 H e U)))
        (fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
          (H.metric.restrictOpen (diffImage_S60 H e U))) y ≤ δ := by
    intro y r hr
    rw [metricDerivNorm_fixedDomainPullback e U (diffImage_S60 H e U)
      (subset_diffImage_S60 H e U) _ _ _ r y,
      ← ckErr_S45_eq_metricDerivNorm_S57 H g' c hc f (diffImage_S60 H e U) hf hinj r
        ⟨e y, y, y.2, rfl⟩]
    exact hF r hr (e y) ⟨y, y.2, rfl⟩
  have key := habs _ _ _ h1 h2 ⟨x, hx⟩ q hq
  rw [ckErr_S45_eq_metricDerivNorm_S57 H g' c hc (f ∘ e) U hFe hinjFe q ⟨x, hx⟩,
    pullbackRestrict_comp_eq_fixed_S60 H (scaleMetric (I := 𝓡 3) c hc g') f e U hf hinj]
  exact key

end GC.LongTime.Ch12
