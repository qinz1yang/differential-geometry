import DifferentialGeometry.Topology.Cobordism.Filling.AcyclicFilling
import DifferentialGeometry.Topology.Homology.Punctures.RoundedDouble
import DifferentialGeometry.Topology.Morse.RoundedSublevel.RoundedDouble
import DifferentialGeometry.Topology.Manifold.LinearRechart

namespace DifferentialGeometry.Topology.RoundedDouble

open Set _root_.Topology
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem nonempty_homeomorph_boundary_sphere (hn : 5 ≤ n) {g : M → ℝ}
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) (hne : (g ⁻¹' Iio 0).Nonempty)
    (hreg : ∀ x, g x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) g x)
    (hB : SimplyConnectedSpace (base g)) (hV : SimplyConnectedSpace (boundary g))
    (hacyclic : SingularPair.acyclic SingularPair.integerCoefficients.{u} (TopCat.of (base g))) :
    Nonempty (boundary g ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let G : M × ℝ → ℝ := fun p => g p.1 + p.2 ^ 2
  have hGprod := contMDiff_height (𝓡 n) hg
  have hregprod := regular_height_zero (𝓡 n) hg hreg
  let := productChartedSpace n M
  let : IsManifold (𝓡 (n + 1)) ∞ (M × ℝ) := product_isManifold
  have hG : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ G :=
    contMDiff_productChartedSpace_iff.mpr hGprod
  have hGregular : ∀ p, G p = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 (n + 1)) G p := by
    intro p hp
    rw [isCriticalPointAt_productChartedSpace_iff hGprod p]
    exact hregprod p hp
  have hGne : (G ⁻¹' Iio 0).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(x, 0), by simpa only [G, mem_preimage, mem_Iio, zero_pow (by decide : 2 ≠ 0),
      add_zero] using hx⟩
  let := hB
  exact nonempty_homeomorph_boundary_of_acyclic_filling (by omega : 6 ≤ n + 1)
    hG (isCompact_filling hg.continuous) hGne hGregular
    (simplyConnectedSpace_filling g) hV (acyclic_filling SingularPair.integerCoefficients g hacyclic)

end DifferentialGeometry.Topology.RoundedDouble
