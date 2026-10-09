import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HpiEndS_O32

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-! CH12-O32 G4 (R4 D-R4-8): window-lift form of hLTF04.  One lift datum per dyadic window
(`a < t`, `2 * t < b`, agreement for every `r ∈ [t, 2t]`); the per-time lift datum of the hLTF04
binder of `hpi03_discrete_of_end_v5_O24` is obtained by restriction (one way only). -/

/-- `[FROZEN] CH12-O32 G4`: window lift ⇒ per-time lift (restriction to each `s ∈ [t, 2t]`). -/
theorem hLTF04_of_window_O32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hW : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H'.Carrier)
        (f : H'.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H'.metric H'.basepoint (2 * R') ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ k' + 2 → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (2 * R'),
          ckErr_S45 H' (postMetric F.observation t) t⁻¹ f j p < δ') →
        ∃ fs : (s : ℝ) → s ∈ Icc t (2 * t) → H'.Carrier → (postStage F.observation s).Carrier,
          (∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'), fs t ⟨le_rfl, by linarith⟩ p = f p) ∧
          (∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            Set.InjOn (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            (∀ j : ℕ, j ≤ k' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
              ckErr_S45 H' (postMetric F.observation s) s⁻¹ (fs s hs) j p < ε')) ∧
          ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a < t) (_ : 2 * t < b)
            (_ : b ≤ (F.tower.history n).horizon)
            (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
              first ≤ (F.tower.history n).toHistory.activeStage r ∧
                (F.tower.history n).toHistory.activeStage r ≤ last)
            (φ : H'.Carrier →
              (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
              (hrs : (r : ℝ) ∈ Icc t (2 * t)),
              ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
                HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)) (fs r hrs p)) :
    ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H'.Carrier)
        (f : H'.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H'.metric H'.basepoint (2 * R') ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ k' + 2 → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (2 * R'),
          ckErr_S45 H' (postMetric F.observation t) t⁻¹ f j p < δ') →
        ∃ fs : (s : ℝ) → s ∈ Icc t (2 * t) → H'.Carrier → (postStage F.observation s).Carrier,
          (∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'), fs t ⟨le_rfl, by linarith⟩ p = f p) ∧
          ∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            Set.InjOn (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            (∀ j : ℕ, j ≤ k' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
              ckErr_S45 H' (postMetric F.observation s) s⁻¹ (fs s hs) j p < ε') ∧
            ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
              (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
              (_ : b ≤ (F.tower.history n).horizon)
              (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
                first ≤ (F.tower.history n).toHistory.activeStage r ∧
                  (F.tower.history n).toHistory.activeStage r ≤ last)
              (φ : H'.Carrier →
                (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H'.metric H'.basepoint (R')) ∧
              ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
                (hrs : (r : ℝ) ∈ Icc t (2 * t)),
                ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
                  HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) (fs r hrs p) := by
  intro H' R' ε' k' hR hε
  obtain ⟨δ', T, hδ, hT, h⟩ := hW H' R' ε' k' hR hε
  refine ⟨δ', T, hδ, hT, fun t ht0 htT U f h1 h2 h3 h4 => ?_⟩
  obtain ⟨fs, hfs0, hfs, n, first, last, ord, a, b, hat, hbt, hb, stages, φ, hφ, hlift⟩ :=
    h t ht0 htT U f h1 h2 h3 h4
  exact ⟨fs, hfs0, fun s hs => ⟨(hfs s hs).1, (hfs s hs).2.1, (hfs s hs).2.2, n, first, last,
    ord, a, b, by linarith [hs.1], by linarith [hs.2], hb, stages, φ, hφ, hlift⟩⟩

/-- `[FROZEN] CH12-O32 G4` (Ico form, hLTF04 v3 = S45 v2 with `a ≤ s`, `Ico a b`; lead 19:1x): window lift
(`a ≤ t`, `2 * t < b`) ⇒ per-time lift.  Independent of the O24 files. -/
theorem hLTF04Ico_of_window_O32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hW : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
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
          (∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            Set.InjOn (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            (∀ j : ℕ, j ≤ k' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
              ckErr_S45 H' (postMetric F.observation s) s⁻¹ (fs s hs) j p < ε')) ∧
          ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : 2 * t < b)
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
                  (φ p)) (fs r hrs p)) :
    ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
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
                    (φ p)) (fs r hrs p) := by
  intro H' R' ε' k' hR hε
  obtain ⟨δ', T, hδ, hT, h⟩ := hW H' R' ε' k' hR hε
  refine ⟨δ', T, hδ, hT, fun t ht0 htT U f h1 h2 h3 h4 => ?_⟩
  obtain ⟨fs, hfs0, hfs, n, first, last, ord, a, b, hat, hbt, hb, stages, φ, hφ, hlift⟩ :=
    h t ht0 htT U f h1 h2 h3 h4
  exact ⟨fs, hfs0, fun s hs => ⟨(hfs s hs).1, (hfs s hs).2.1, (hfs s hs).2.2, n, first, last,
    ord, a, b, hat, by linarith [hs.1], by linarith [hs.2], hb, stages, φ, hφ, hlift⟩⟩

end GC.LongTime.Ch12
