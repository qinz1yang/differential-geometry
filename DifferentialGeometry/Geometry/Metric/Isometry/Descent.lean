import Mathlib.Topology.MetricSpace.Isometry

namespace IsometryEquiv

variable {X Y M N : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [PseudoMetricSpace M] [PseudoMetricSpace N]

theorem isometry_of_image_ball (e : X ≃ᵢ Y)
    (p : X → M) (q : Y → N) (hp : Function.Surjective p)
    (hpball : ∀ (x : X) (r : ℝ), 0 < r → p '' Metric.ball x r = Metric.ball (p x) r)
    (hqball : ∀ (y : Y) (r : ℝ), 0 < r → q '' Metric.ball y r = Metric.ball (q y) r)
    (f : M → N) (hf : Function.Injective f)
    (hcomm : ∀ x : X, q (e x) = f (p x)) : Isometry f := by
  apply Isometry.of_dist_eq
  intro x y
  obtain ⟨a, ha⟩ := hp x
  have himage (r : ℝ) (hr : 0 < r) : f '' Metric.ball x r = Metric.ball (f x) r := by
    calc
      f '' Metric.ball x r = f '' (p '' Metric.ball a r) := by rw [hpball a r hr, ha]
      _ = (f ∘ p) '' Metric.ball a r := Set.image_image _ _ _
      _ = (q ∘ e) '' Metric.ball a r := by
        congr 1
        exact funext fun z => (hcomm z).symm
      _ = q '' (e '' Metric.ball a r) := by
        rw [Set.image_image]
        rfl
      _ = q '' Metric.ball (e a) r := by rw [e.image_ball]
      _ = Metric.ball (q (e a)) r := hqball _ _ hr
      _ = Metric.ball (f x) r := by rw [hcomm, ha]
  have hmem (r : ℝ) (hr : 0 < r) : f y ∈ Metric.ball (f x) r ↔ y ∈ Metric.ball x r := by
    rw [← himage r hr]
    constructor
    · rintro ⟨z, hz, heq⟩
      exact hf heq ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hlt (r : ℝ) (hr : 0 < r) : dist (f y) (f x) < r ↔ dist y x < r := hmem r hr
  have hd : dist (f y) (f x) = dist y x := by
    apply le_antisymm
    · by_contra h
      have hpos : 0 < dist (f y) (f x) := dist_nonneg.trans_lt (lt_of_not_ge h)
      exact (lt_irrefl _ ((hlt _ hpos).mpr (lt_of_not_ge h)))
    · by_contra h
      have hpos : 0 < dist y x := dist_nonneg.trans_lt (lt_of_not_ge h)
      exact (lt_irrefl _ ((hlt _ hpos).mp (lt_of_not_ge h)))
  simpa only [dist_comm] using hd

end IsometryEquiv
