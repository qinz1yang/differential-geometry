import DifferentialGeometry.Topology.JordanCurve
import DifferentialGeometry.External.Schoenflies.JordanSchoenflies

open Set

theorem Topology.IsEmbedding.jordan_schoenflies
    {e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2)} (he : Topology.IsEmbedding e) :
    ∃ F : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, F z = e z := by
  have hs : Schoenflies.IsJordanCurve
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    have hi : Topology.IsEmbedding
        (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
          EuclideanSpace ℝ (Fin 2)) := .subtypeVal
    simpa only [Subtype.range_coe] using hi.isJordanCurve_range
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    hs he.isJordanCurve_range he.toHomeomorph
  exact ⟨F, fun z => by simpa only [Topology.IsEmbedding.toHomeomorph_apply_coe] using hF z⟩
