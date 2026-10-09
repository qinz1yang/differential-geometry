import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X]

structure PairedComparisonPacket (δ : ℝ) (V : Set X) (a b : ι → X) : Prop where
  opposite : ∀ z ∈ V, ∀ i, Real.pi - δ <
    comparisonAngleNegCurvature 1 (dist z (a i)) (dist z (b i)) (dist (a i) (b i))
  cross : ∀ z ∈ V, ∀ i j, i ≠ j → ∀ u ∈ ({a i, b i} : Set X),
    ∀ v ∈ ({a j, b j} : Set X), Real.pi / 2 - δ <
      comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v)

theorem PairedComparisonPacket.mono {δ : ℝ} {V W : Set X} {a b : ι → X}
    (h : PairedComparisonPacket δ V a b) (hWV : W ⊆ V) : PairedComparisonPacket δ W a b :=
  ⟨fun z hz => h.opposite z (hWV hz), fun z hz => h.cross z (hWV hz)⟩

theorem PairedComparisonPacket.weaken {δ ε : ℝ} {V : Set X} {a b : ι → X}
    (h : PairedComparisonPacket δ V a b) (hδε : δ ≤ ε) : PairedComparisonPacket ε V a b := by
  constructor
  · intro z hz i
    exact lt_of_le_of_lt (by linarith) (h.opposite z hz i)
  · intro z hz i j hij u hu v hv
    exact lt_of_le_of_lt (by linarith) (h.cross z hz i j hij u hu v hv)

theorem PairedComparisonPacket.swap {δ : ℝ} {V : Set X} {a b : ι → X}
    (h : PairedComparisonPacket δ V a b) : PairedComparisonPacket δ V b a := by
  constructor
  · intro z hz i
    rw [comparisonAngleNegCurvature_comm, dist_comm (b i) (a i)]
    exact h.opposite z hz i
  · intro z hz i j hij u hu v hv
    exact h.cross z hz i j hij u (by simpa only [Set.pair_comm (b i) (a i)] using hu)
      v (by simpa only [Set.pair_comm (b j) (a j)] using hv)

end DifferentialGeometry.Geometry.Comparison.Toponogov
