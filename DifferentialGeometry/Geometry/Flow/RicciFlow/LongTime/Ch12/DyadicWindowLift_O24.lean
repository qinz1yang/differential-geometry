import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-! CH12-O24 G1b: the window half of hstep v5 (`[FROZEN v5] CH12-O24`): as
`dyadic_window_O20`, and additionally the S3/S45 survivor lift of every window map on `B(4R)`
(the `hlift0` input of S55); `C^k` errors written with `ckErr_S45`. -/

theorem dyadic_window_lift_O24 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (hLTF04 : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H'.Carrier)
        (f : H'.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H'.metric H'.basepoint (2 * R') ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ k' + 3 → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (2 * R'),
          ckErr_S45 H' (postMetric F.observation t) t⁻¹ f j p < δ') →
        ∃ fs : (s : ℝ) → s ∈ Icc t (2 * t) → H'.Carrier → (postStage F.observation s).Carrier,
          (∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'), fs t ⟨le_rfl, by linarith⟩ p = f p) ∧
          ∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            Set.InjOn (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            (∀ j : ℕ, j ≤ k' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
              ckErr_S45 H' (postMetric F.observation s) s⁻¹ (fs s hs) j p < ε') ∧
            ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
              (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : a ≤ s) (_ : s < b)
              (_ : b ≤ (F.tower.history n).horizon)
              (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
                first ≤ (F.tower.history n).toHistory.activeStage r ∧
                  (F.tower.history n).toHistory.activeStage r ≤ last)
              (φ : H'.Carrier →
                (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H'.metric H'.basepoint (R')) ∧
              ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
                (hrs : (r : ℝ) ∈ Icc t (2 * t)),
                ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
                  HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) (fs r hrs p)) (R ε : ℝ) (k : ℕ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ Tw : ℝ, 0 < δ ∧ ∀ (t t₂ : ℝ), 0 < t → Tw ≤ t → t₂ = 2 * t →
      ∀ b : ℝ, b ≤ δ → 4 * R ≤ b⁻¹ → (k : ℝ) + 3 ≤ b⁻¹ →
      ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
      (∃ U : TopologicalSpace.Opens H.Carrier,
        riemannianBallOf H.metric H.basepoint (2 * b⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
        ∀ k : ℕ, k ≤ ⌈b⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * b⁻¹),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < b) →
      ∃ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
        (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R), f t h0 p = g₁ p) ∧
        ∀ s (hs : s ∈ Icc t t₂),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
          Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
          (∀ k' : ℕ, k' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k' p < ε) ∧
  ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
    (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : a ≤ s) (_ : s < b)
    (_ : b ≤ (F.tower.history n).horizon)
    (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
      first ≤ (F.tower.history n).toHistory.activeStage r ∧
        (F.tower.history n).toHistory.activeStage r ≤ last)
    (φ : H.Carrier →
      (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
    ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
      (hrs : (r : ℝ) ∈ Icc t t₂),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
          (φ p)) (f r hrs p) := by
  obtain ⟨δ', T, hδ', -, hw⟩ := hLTF04 H (4 * R) ε k (by positivity) hε
  refine ⟨δ', T, hδ', ?_⟩
  intro t t₂ ht hTt ht₂ b hbδ hRb hkb g₁ ⟨U, hU, hsm, hemb, herr⟩
  subst ht₂
  have hball : riemannianBallOf H.metric H.basepoint (2 * (4 * R)) ⊆
      riemannianBallOf H.metric H.basepoint (2 * b⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith)
  have hord : ∀ j : ℕ, j ≤ k + 3 → j ≤ ⌈b⁻¹⌉₊ := fun j hj => by
    have h1 : ((k + 3 : ℕ) : ℝ) ≤ (⌈b⁻¹⌉₊ : ℝ) := by
      push_cast
      exact hkb.trans (Nat.le_ceil _)
    exact hj.trans (Nat.cast_le.1 h1)
  obtain ⟨fs, hfs0, hfs⟩ := hw t ht hTt U g₁ (hball.trans hU) hsm hemb
    (fun j hj p hp => (herr j (hord j hj) p (hball hp)).trans_le hbδ)
  exact ⟨fs, fun _ p hp => hfs0 p hp, fun s hs =>
    ⟨(hfs s hs).1, (hfs s hs).2.1, (hfs s hs).2.2.1, (hfs s hs).2.2.2⟩⟩

end GC.LongTime.Ch12
