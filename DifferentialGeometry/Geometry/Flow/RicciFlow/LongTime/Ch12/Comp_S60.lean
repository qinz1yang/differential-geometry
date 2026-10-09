import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompBridge_S60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompImmersion_S60

set_option autoImplicit false

/-!
# CH12-S60 / G3: `hcomp_S60` (the composition lemma for `ckErr_S45`)

Adapter form of the frozen `hcomp` of `[FROZEN] CH12-S55` (see `[FROZEN] CH12-S60` in DELIVERIES):
`e` a global diffeomorphism of `H.Carrier`, `f` smooth on `e '' ball R`; `δ` depends only on
`(k, ε)`.  Proof: order-0 smallness gives `c > 0` and the immersion property of `f`
(`ckErr0_immersion_S60`); then `ckErr_comp_bridge_S60` + `ckComp_abstract_S60`.
-/

noncomputable section

open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem hcomp_S60 (H : FiniteVolumeHyperbolicModel.{u}) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ)
        (f : H.Carrier → N) (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (R : ℝ),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (e '' riemannianBallOf H.metric H.basepoint R) →
        (∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H H.metric 1 e i p ≤ δ) →
        (∀ i : ℕ, i ≤ k → ∀ q ∈ e '' riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H g' c f i q ≤ δ) →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint R, ckErr_S45 H g' c (f ∘ e) k p < ε := by
  obtain ⟨δa, hδa, habs⟩ := ckComp_abstract_S60 (E := EuclideanSpace ℝ (Fin 3)) (I := 𝓡 3) k
    (half_pos hε)
  refine ⟨min δa (1 / 2), lt_min hδa (by norm_num), ?_⟩
  intro N _ _ _ g' c f e R hf hE hF p hp
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint R, isOpen_riemannianBallOf H.metric H.basepoint R⟩
  have hlt : ∀ y ∈ e '' (U : Set H.Carrier), ckErr_S45 H g' c f 0 y < 1 := by
    intro y hy
    exact lt_of_le_of_lt ((hF 0 (Nat.zero_le k) y hy).trans (min_le_right _ _))
      (by norm_num)
  have hc : 0 < c := (ckErr0_immersion_S60 H g' c f (e p) (hlt (e p) ⟨p, hp, rfl⟩)).1
  have hinj : ∀ y ∈ e '' (U : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) :=
    fun y hy => (ckErr0_immersion_S60 H g' c f y (hlt y hy)).2
  have habs' : ∀ A gHat gBase : SmoothRiemannianMetric (𝓡 3) U,
      (∀ x : U, ∀ q : ℕ, q ≤ k →
        CheegerGromovCompactness.metricDerivNorm (I := 𝓡 3) q gHat gBase gBase x ≤
          min δa (1 / 2)) →
      (∀ x : U, ∀ q : ℕ, q ≤ k →
        CheegerGromovCompactness.metricDerivNorm (I := 𝓡 3) q A gHat gHat x ≤
          min δa (1 / 2)) →
      ∀ x : U, ∀ q : ℕ, q ≤ k →
        CheegerGromovCompactness.metricDerivNorm (I := 𝓡 3) q A gBase gBase x ≤ ε / 2 :=
    fun A gHat gBase h1 h2 x q hq =>
      habs (N := U) isOpen_univ A gHat gBase
        (fun y _ r hr => (h1 y r hr).trans (min_le_left _ _))
        (fun y _ r hr => (h2 y r hr).trans (min_le_left _ _)) x (mem_univ x) q hq
  have := ckErr_comp_bridge_S60 H g' c hc f e U hf hinj habs' hE hF k le_rfl p hp
  linarith

end GC.LongTime.Ch12
