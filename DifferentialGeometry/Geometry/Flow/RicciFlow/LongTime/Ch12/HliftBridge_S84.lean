import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiring_S61

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

/-- CH12-S84 adapter: the `Ioo` datum `hlift0` of `persistentModelPatch_of_windows_S61` /
`singleModel_S72` / `hone_S4_S72` from the `Ico` datum `hlift0Ico` (the output shape of the O24 / O32 chain after
[FROZEN v3] CH12-S70 hLTF04, plus the left-coverage clause `∀ r ∈ window, r ≤ s → a ≤ r`, true for the producer
`hLTF04Ico_S70` whose lift starts at `a ≤ t = min window`) and the backward-crossing bridge `hbridge`
(= `hlift_Ioo_of_Ico_S84`, [FROZEN] CH12-S84 bridge, proof: lane S89), applied at `S := ball (4 ρ j)`,
`W := [2^j T, 2^(j+1) T]`, `w := f j`.  `hneg`: the post-side scalar of `f j t` on the ball is `≤ 0`
(hyperbolic model region; from `hacc` closeness, LTF03 defect `< 1`). -/
theorem hlift0_of_Ico_S84 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (ρ : ℕ → ℝ)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (hbridge : ∀ (S : Set H.Carrier) (W : Set ℝ)
      (w : ∀ r : ℝ, r ∈ W → H.Carrier → (postStage F.observation r).Carrier) (s : ℝ) (hs : s ∈ W),
      (∀ p ∈ S, metricScalarAt (postMetric F.observation s) (w s hs p) ≤ 0) →
      (∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ s) (_ : ∀ r ∈ W, r ≤ s → a ≤ r) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
        (hrW : (r : ℝ) ∈ W), ∀ p ∈ S,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (w r hrW p)) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
        (hrW : (r : ℝ) ∈ W), ∀ p ∈ S,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (w r hrW p))
    (hneg : ∀ j (t : ℝ) (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j), metricScalarAt (postMetric F.observation t) (f j t ht p) ≤ 0)
    (hlift0Ico : ∀ j (s : ℝ), s ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ s) (_ : ∀ r ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)), r ≤ s → a ≤ r) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
        (hrW : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (f j r hrW p)) :
    ∀ j (s : ℝ), s ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
        (hrW : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (f j r hrW p) :=
  fun j s hs => hbridge (riemannianBallOf H.metric H.basepoint (4 * ρ j)) (Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))) (fun r hr => f j r hr) s hs (hneg j s hs) (hlift0Ico j s hs)

end GC.LongTime.Ch12
