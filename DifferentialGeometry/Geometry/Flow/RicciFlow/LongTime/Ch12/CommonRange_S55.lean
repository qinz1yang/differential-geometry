import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WindowSurvivor_S49

set_option autoImplicit false

/-! # CH12-S55 G3b: two survivor lifts of one history over a common stage range.
Used for the junction `t₀ = t_{j+1}` of `persistentModelPatch_of_windows_S55` (windows `j`, `j+1`
lifted in one history by `lift_uniform_S55`, brought to the range `[max first, min last]` by
`survivorRestrict_S49`). -/

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

/-- The common range is nonempty as soon as one stage `c` lies in both ranges; the restricted
lifts are smooth on `S` and have the same survivor-map values at every stage of the common range. -/
theorem common_range_lift_S55 (K : ObservedHistory.{u}) {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (S : Set X)
    {f₁ l₁ f₂ l₂ : Fin (K.eventCount + 1)} (o₁ : f₁ ≤ l₁) (o₂ : f₂ ≤ l₂)
    (c : Fin (K.eventCount + 1)) (hc₁ : f₁ ≤ c ∧ c ≤ l₁) (hc₂ : f₂ ≤ c ∧ c ≤ l₂)
    (φ₁ : X → K.backwardSurvivorDomain f₁ l₁ o₁) (φ₂ : X → K.backwardSurvivorDomain f₂ l₂ o₂)
    (h₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ₁ S) (h₂ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ₂ S) :
    ∃ (o : max f₁ f₂ ≤ min l₁ l₂)
      (ψ₁ ψ₂ : X → K.backwardSurvivorDomain (max f₁ f₂) (min l₁ l₂) o),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ₁ S ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ₂ S ∧
      (∀ (j : Fin (K.eventCount + 1)) (hj1 : max f₁ f₂ ≤ j) (hj2 : j ≤ min l₁ l₂) (x : X),
        K.backwardSurvivorMap (max f₁ f₂) (min l₁ l₂) o j hj1 hj2 (ψ₁ x) =
          K.backwardSurvivorMap f₁ l₁ o₁ j ((le_max_left _ _).trans hj1)
            (hj2.trans (min_le_left _ _)) (φ₁ x)) ∧
      (∀ (j : Fin (K.eventCount + 1)) (hj1 : max f₁ f₂ ≤ j) (hj2 : j ≤ min l₁ l₂) (x : X),
        K.backwardSurvivorMap (max f₁ f₂) (min l₁ l₂) o j hj1 hj2 (ψ₂ x) =
          K.backwardSurvivorMap f₂ l₂ o₂ j ((le_max_right _ _).trans hj1)
            (hj2.trans (min_le_right _ _)) (φ₂ x)) := by
  have o : max f₁ f₂ ≤ min l₁ l₂ := le_trans (max_le hc₁.1 hc₂.1) (le_min hc₁.2 hc₂.2)
  refine ⟨o, fun x => survivorRestrict_S49 K o₁ o (le_max_left _ _) (min_le_left _ _) (φ₁ x),
    fun x => survivorRestrict_S49 K o₂ o (le_max_right _ _) (min_le_right _ _) (φ₂ x),
    (contMDiff_survivorRestrict_S49 K o₁ o (le_max_left _ _) (min_le_left _ _)).comp_contMDiffOn h₁,
    (contMDiff_survivorRestrict_S49 K o₂ o (le_max_right _ _) (min_le_right _ _)).comp_contMDiffOn h₂,
    fun j hj1 hj2 x => backwardSurvivorMap_survivorRestrict_S49 K o₁ o (le_max_left _ _)
      (min_le_left _ _) j hj1 hj2 (φ₁ x),
    fun j hj1 hj2 x => backwardSurvivorMap_survivorRestrict_S49 K o₂ o (le_max_right _ _)
      (min_le_right _ _) j hj1 hj2 (φ₂ x)⟩

end GC.LongTime.Ch12
