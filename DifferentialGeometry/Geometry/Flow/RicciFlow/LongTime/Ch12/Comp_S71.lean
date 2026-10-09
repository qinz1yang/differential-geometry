import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompBridge_S71
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompLocalDiffeo_S71

set_option autoImplicit false

/-!
# CH12-S71 / G3: `hcomp_S71` (the composition lemma for `ckErr_S45`, S55 frozen shape)

`[FROZEN] CH12-S71` in DELIVERIES: the `hcomp` of `[FROZEN] CH12-S55` with `E` merely `ContMDiff`
(no global diffeomorphism), plus the inline binders `hinj : Set.InjOn E (ball R)` and
`hf : ContMDiffOn f (E '' ball R)` (S60 G2 ruling); `δ` depends only on `(k, ε)`.

Proof: order-0 smallness gives `c > 0`, the immersion property of `f` (`ckErr0_immersion_S60`) and a
partial diffeomorphism `Φ` with source `ball R` and underlying map `E` (`CompLocalDiffeo_S71`); then
`ckErr_comp_bridge_S71` (local naturality `metricDerivNorm_localPullback_S71`) +
`ckComp_abstract_S60`.
-/

noncomputable section

open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem hcomp_S71 (H : FiniteVolumeHyperbolicModel.{u}) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ)
        (f : H.Carrier → N) (E : H.Carrier → H.Carrier) (R : ℝ),
        ContMDiff (𝓡 3) (𝓡 3) ∞ E →
        Set.InjOn E (riemannianBallOf H.metric H.basepoint R) →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (E '' riemannianBallOf H.metric H.basepoint R) →
        (∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H H.metric 1 E i p ≤ δ) →
        (∀ i : ℕ, i ≤ k → ∀ q ∈ E '' riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H g' c f i q ≤ δ) →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint R, ckErr_S45 H g' c (f ∘ E) k p < ε := by
  obtain ⟨δa, hδa, habs⟩ := ckComp_abstract_S60 (E := EuclideanSpace ℝ (Fin 3)) (I := 𝓡 3) k
    (half_pos hε)
  refine ⟨min δa (1 / 2), lt_min hδa (by norm_num), ?_⟩
  intro N _ _ _ g' c f E R hEs hinjE hf hE hF p hp
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint R, isOpen_riemannianBallOf H.metric H.basepoint R⟩
  have h0 : ∀ y ∈ (U : Set H.Carrier), ckErr_S45 H H.metric 1 E 0 y < 1 := fun y hy =>
    lt_of_le_of_lt ((hE 0 (Nat.zero_le k) y hy).trans (min_le_right _ _)) (by norm_num)
  obtain ⟨Φ, hsrc, hΦE, hmf⟩ := exists_partialDiffeomorph_of_ckErr0_S71 H E hEs U hinjE h0
  subst hΦE
  have hU : (U : Set H.Carrier) ⊆ Φ.source := hsrc.symm.subset
  have hlt : ∀ y ∈ (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
      ckErr_S45 H g' c f 0 y < 1 := by
    intro y hy
    exact lt_of_le_of_lt ((hF 0 (Nat.zero_le k) y hy).trans (min_le_right _ _))
      (by norm_num)
  have hc : 0 < c := (ckErr0_immersion_S60 H g' c f (Φ p) (hlt (Φ p) ⟨p, hp, rfl⟩)).1
  have hinj : ∀ y ∈ (Φ : H.Carrier → H.Carrier) '' (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) :=
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
  have := ckErr_comp_bridge_S71 H g' c hc f Φ U hU hmf hf hinj habs' hE hF k le_rfl p hp
  linarith

end GC.LongTime.Ch12
