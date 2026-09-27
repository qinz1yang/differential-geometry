import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.EMetricSpace.Basic



open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Analysis



theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have h : eball x (⊤ : ℝ≥0∞) = univ :=
    (show IsClopen (eball x (⊤ : ℝ≥0∞)) from ⟨isClosed_eball_top, isOpen_eball⟩).eq_univ
      ⟨x, mem_eball_self (by simp)⟩
  have hy : y ∈ eball x (⊤ : ℝ≥0∞) := h ▸ mem_univ y
  exact ne_top_of_lt (by simpa only [mem_eball, edist_comm] using hy)

end DifferentialGeometry.Analysis
