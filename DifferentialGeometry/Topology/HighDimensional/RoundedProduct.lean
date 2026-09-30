import DifferentialGeometry.Topology.Cobordism.Filling.HomotopySpherePuncture
import DifferentialGeometry.Topology.Cobordism.Filling.RoundedFilling
import DifferentialGeometry.Topology.Morse.RoundedSublevel.RoundedCollar
import DifferentialGeometry.Topology.Double.Rounded.RoundedSimplyConnected
import DifferentialGeometry.Topology.Double.Rounded.RoundedDisk
import DifferentialGeometry.Topology.Schoenflies.BrownSchoenflies

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology
open scoped Manifold ContDiff ContinuousMap

theorem poincare_smooth_of_five_le {m : ℕ} (h5 : 5 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) := by
  obtain ⟨p⟩ := exists_smoothSpherePuncture (by omega : 3 ≤ m + 1) e
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    simplyConnectedSpace_sphere (by omega : 2 ≤ m)
  have hzero : IsPathConnected (p.g ⁻¹' {0}) :=
    isPathConnected_iff_pathConnectedSpace.mpr p.levelHomeomorph.symm.pathConnectedSpace
  obtain ⟨η₀, hη₀, Ψ₀, hΨ₀, -⟩ :=
    RoundedDouble.exists_equatorial_collar p.smooth p.regular_zero
  have hV := RoundedDouble.simplyConnectedSpace_boundary_of_collar p.smooth.continuous
    p.simplyConnected_base hzero hη₀ Ψ₀ hΨ₀
  obtain ⟨eV⟩ := RoundedDouble.nonempty_homeomorph_boundary_sphere h5 p.smooth
    p.negative_nonempty p.regular_zero p.simplyConnected_base hV p.acyclic_base
  have : CompactSpace (RoundedDouble.boundary p.g) :=
    isCompact_iff_compactSpace.mp (RoundedDouble.isCompact_boundary p.smooth.continuous)
  have : TopologicalSpace.MetrizableSpace (RoundedDouble.boundary p.g) := eV.isEmbedding.metrizableSpace
  let : MetricSpace (RoundedDouble.boundary p.g) :=
    TopologicalSpace.metrizableSpaceMetric (RoundedDouble.boundary p.g)
  obtain ⟨η, hη, Ψ, hΨ⟩ := RoundedDouble.exists_unit_equatorial_collar p.smooth p.regular_zero
  let t : RoundedDouble.boundary p.g → ℝ := fun x => x.1.2 / η
  let Φ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) ≃ₜ
      {x : RoundedDouble.boundary p.g // t x ∈ Icc (-1 : ℝ) 1} :=
    (Homeomorph.prodCongr p.levelHomeomorph.symm (Homeomorph.refl SuspensionInterval)).trans Ψ
  have hΦ (q : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
      t (Φ q).1 = q.2.1 := hΨ (p.levelHomeomorph.symm q.1, q.2)
  obtain ⟨d, hd, hdrange, hdboundary⟩ := (exists_side_disks_of_height_collar eV t
    (continuous_subtype_val.snd.div_const η) Φ hΦ).1
  have hdrange' : range d = {x : RoundedDouble.boundary p.g | x.1.2 ≤ 0} := by
    rw [hdrange]
    ext x
    change x.1.2 / η ≤ 0 ↔ x.1.2 ≤ 0
    rw [div_le_iff₀ hη, zero_mul]
  have hdboundary' : d '' diskSphere (m + 1) =
      {x : RoundedDouble.boundary p.g | x.1.2 = 0} := by
    rw [hdboundary]
    ext x
    change x.1.2 / η = 0 ↔ x.1.2 = 0
    simp only [div_eq_zero_iff, hη.ne', or_false]
  exact RoundedDouble.sphere_homeomorph_of_lower_disk p.chartDisk.isClosedEmbedding
    p.positive_eq_range.symm p.zero_eq_boundary.symm hd hdrange' hdboundary'

theorem smooth_poincare_five {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 5)) M] [IsManifold (𝓡 5) ∞ M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 6)) 1) := by
  exact poincare_smooth_of_five_le (m := 4) (by norm_num) e

end DifferentialGeometry.Topology
