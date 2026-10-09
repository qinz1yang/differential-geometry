import DifferentialGeometry.Geometry.Comparison.PairedPacket

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι κ : Type*} [MetricSpace X]

theorem PairedComparisonPacket.reindex {δ : ℝ} {V : Set X} {a b : ι → X}
    (h : PairedComparisonPacket δ V a b) (e : κ ≃ ι) :
    PairedComparisonPacket δ V (a ∘ e) (b ∘ e) := by
  constructor
  · intro z hz i
    exact h.opposite z hz (e i)
  · intro z hz i j hij u hu v hv
    exact h.cross z hz (e i) (e j) (fun hh => hij (e.injective hh)) u hu v hv

end DifferentialGeometry.Geometry.Comparison.Toponogov
