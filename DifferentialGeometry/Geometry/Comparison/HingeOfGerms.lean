import DifferentialGeometry.Topology.MetricSpace.GermSegment
import DifferentialGeometry.Geometry.Comparison.HingeModel

set_option autoImplicit false

open Set Metric

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_hinge_of_germs {κ R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    {x p q : X} {γ β : ℝ → X} (hγend : γ R = p) (hβend : β S = q)
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist x (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist x (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|) :
    ∃ H : MinimizingHinge p q, H.center = x ∧ H.germAngle κ = germComparisonAngle κ γ β := by
  have ha : dist x p = R := by simpa only [hγend] using hγrad R ⟨hR, le_rfl⟩
  have hb : dist x q = S := by simpa only [hβend] using hβrad S ⟨hS, le_rfl⟩
  subst R
  subst S
  obtain ⟨η, hη, hη0, hηeq⟩ := exists_isometry_segment_of_germ hR.le hγrad hγmin
  obtain ⟨σ, hσ, hσ0, hσeq⟩ := exists_isometry_segment_of_germ hS.le hβrad hβmin
  have hηp : η ⟨dist x p, ⟨dist_nonneg, le_rfl⟩⟩ = p :=
    (hηeq (dist x p) ⟨hR, le_rfl⟩).trans hγend
  have hσq : σ ⟨dist x q, ⟨dist_nonneg, le_rfl⟩⟩ = q :=
    (hσeq (dist x q) ⟨hS, le_rfl⟩).trans hβend
  let H : MinimizingHinge p q := ⟨x, η, σ, hη, hσ, hη0, hσ0, hηp, hσq⟩
  refine ⟨H, rfl, ?_⟩
  apply germComparisonAngle_congr_on hR hS
  · intro s hs
    rw [IccExtend_of_mem _ η ⟨hs.1.le, hs.2⟩]
    exact hηeq s hs
  · intro t ht
    rw [IccExtend_of_mem _ σ ⟨ht.1.le, ht.2⟩]
    exact hσeq t ht

end Metric.MinimizingHinge
