import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Compact



open Set Filter Uniformity UniformSpace
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis



theorem exists_uniform_diagonal_radius {M : Type*} [PseudoEMetricSpace M] [CompactSpace M]
    {U : Set (M × M)} (hU : IsOpen U) (hdiag : ∀ x, (x, x) ∈ U) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ x y, edist x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U := by
  have hu : U ∈ 𝓤 M := by
    rw [compactSpace_uniformity]
    exact mem_iSup.mpr (fun x => hU.mem_nhds (hdiag x))
  obtain ⟨ρ, hρ, hρU⟩ := uniformity_basis_edist_nnreal_le.mem_iff.mp hu
  exact ⟨ρ, hρ, fun x y hxy => hρU hxy⟩

end DifferentialGeometry.Analysis
