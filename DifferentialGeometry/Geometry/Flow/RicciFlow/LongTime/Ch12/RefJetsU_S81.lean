import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RefJetMain_S81
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57

set_option autoImplicit false

/-!
# CH12-S81 / G3: `hReferenceJets_S81` (the U-form producer of the frozen `hReferenceJets` binder of S75)

`refJets_window_S81` on `M := ↥U`, `h := H.metric.restrictOpen U`, `N := Nord + 1`, with the flow `S'` identified with
the pull-back family `pullbackRestrict_S57 H (g r) f U hF hinj` on `Icc t u`.  The constant `B` is chosen before
`N, g, f, t, u, S'`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.Ch12

theorem hReferenceJets_S81 (H : FiniteVolumeHyperbolicModel.{u}) (U : Opens H.Carrier) (Nord : ℕ)
    (K : ℕ → Set U) (hKc : IsCompact (K 0)) (V : Set U) (hV : IsOpen V) (hKV : K 0 ⊆ V)
    {Λ KShi : ℝ} (hΛ : 1 ≤ Λ) (hKShi : 0 ≤ KShi) (Cinit : ℕ → ℝ) (hC : ∀ q, 0 ≤ Cinit q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
      (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
      (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
      (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) (t u : ℝ), 0 < t → u ≤ 2 * t →
      (∀ r ∈ Icc t u, ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
        Λ⁻¹ * (r * (H.metric.restrictOpen U).inner x v v) ≤
            (pullbackRestrict_S57 H (g r) f U hF hinj).inner x v v ∧
          (pullbackRestrict_S57 H (g r) f U hF hinj).inner x v v ≤
            Λ * (r * (H.metric.restrictOpen U).inner x v v)) →
      (∀ s ≤ Nord + 1, ∀ r ∈ Icc t u, ∀ x ∈ V,
        normSq0S (pullbackRestrict_S57 H (g r) f U hF hinj) x (2 + s)
          (ricCovTower (pullbackRestrict_S57 H (g r) f U hF hinj)
            (pullbackRestrict_S57 H (g r) f U hF hinj) s x) * r ^ (2 + s) ≤ KShi ^ 2) →
      (∀ q, 1 ≤ q → q ≤ Nord + 1 → ∀ x ∈ V,
        Real.sqrt (normSq0S (H.metric.restrictOpen U) x (q + 2)
          (metricCovDeriv (pullbackRestrict_S57 H (g t) f U hF hinj) (H.metric.restrictOpen U) q x)) ≤
          Cinit q * t) →
      ∀ (D : RealTimeInterval) (S' : SolutionOn (I := 𝓡 3) (M := U) D),
      IsSolutionOn S' → Icc t u ⊆ D.regular →
      (∀ r ∈ Icc t u, S'.base.metric r = pullbackRestrict_S57 H (g r) f U hF hinj) →
      ∀ j ≤ Nord + 1, ∀ r ∈ Ioo t u, ∀ x ∈ K 0,
        Real.sqrt (normSq0S (H.metric.restrictOpen U) x (j + 2)
          (defectJet_S57 S' (H.metric.restrictOpen U) j r x)) ≤ B * r := by
  obtain ⟨B, hB0, hB⟩ := refJets_window_S81 (I := 𝓡 3) (H.metric.restrictOpen U) hKc hV hKV
    (Nord + 1) hΛ hKShi Cinit hC
  refine ⟨B, hB0, ?_⟩
  intro N _ _ _ g f hF hinj t u ht hu hequiv hShi hinit D S' hS' hreg hmet j hj r hr x hx
  have htu : t ≤ u := hr.1.le.trans hr.2.le
  have htmem : t ∈ Icc t u := ⟨le_rfl, htu⟩
  refine hB S' hS' ht hu hreg ?_ ?_ ?_ j hj r (Ioo_subset_Icc_self hr) x hx
  · intro r' hr' x' hx' v
    rw [hmet r' hr']
    exact hequiv r' hr' x' hx' v
  · intro s hs r' hr' x' hx'
    rw [hmet r' hr']
    exact hShi s hs r' hr' x' hx'
  · intro q hq1 hqN x' hx'
    rw [hmet t htmem]
    exact hinit q hq1 hqN x' hx'

end GC.LongTime.Ch12
