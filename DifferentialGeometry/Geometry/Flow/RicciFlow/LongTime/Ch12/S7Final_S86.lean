import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLiftMain_S86

/-!
# CH12-S86 G3: S7 v3 (`hpi02_inverse_comparison_S86`)
S7 v2 ([FROZEN] CH12-O19) with `[T2Space N]` ([FROZEN v2] CH12-S76).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Manifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem hpi02_inverse_comparison_S86 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (j₀ : ℕ),
    0 < R → 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∃ m : ℕ, ∀ (H' : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
      [TopologicalSpace N] [T2Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
      [IsManifold (𝓡 3) ∞ N]
      (gN : SmoothRiemannianMetric (𝓡 3) N) (U : TopologicalSpace.Opens H.Carrier)
      (U' : TopologicalSpace.Opens H'.Carrier) (f : H.Carrier → N) (φ : H'.Carrier → N),
      riemannianBallOf H.metric H.basepoint (2 * R + 2) ⊆ U →
      riemannianBallOf H'.metric H'.basepoint (8 * R + 8) ⊆ U' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) →
      f H.basepoint = φ H'.basepoint →
      (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R + 2),
        ckErr_O19 H gN 1 f j p < δ) →
      (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (8 * R + 8),
        ckErr_O19 H' gN 1 φ j p < δ) →
      (∀ p ∈ riemannianBallOf H.metric H.basepoint R, f p ∈ φ '' (U' : Set H'.Carrier)) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn φ U' (f p))
        (riemannianBallOf H.metric H.basepoint R) ∧
      ∀ j : ℕ, j ≤ j₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
        ckErr_O19 H H'.metric 1 (fun p => Function.invFunOn φ U' (f p)) j p < ε := by
  intro H R ε j₀ hR hε
  obtain ⟨δ, hδ, hδ8, m, key⟩ := s7_of_hlift_S86 H R ε j₀ hR hε
  refine ⟨δ, hδ, m, ?_⟩
  intro H' N _ _ _ _ gN U U' f φ hbU hbU' hfU hfemb hφU' hφemb hbase hck hck'
  exact key H' gN U U' f φ hbU hbU' hfU hfemb hφU' hφemb hck hck'
    (hlift_S86 H H' gN U U' f φ R hR hbU hbU' hfU hfemb hφU' hφemb hbase
      (fun p hp => lt_of_lt_of_le (hck 0 (Nat.zero_le _) p hp) hδ8)
      (fun q hq => lt_of_lt_of_le (hck' 0 (Nat.zero_le _) q hq) hδ8))

end GC.LongTime.Ch12
