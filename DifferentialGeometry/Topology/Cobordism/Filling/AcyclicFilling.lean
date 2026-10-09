import DifferentialGeometry.Topology.Cobordism.HCobordism
import DifferentialGeometry.Topology.Morse.RoundedSublevel.PuncturedSublevel
import DifferentialGeometry.Topology.Manifold.GeneralPosition.ChartDiskComplement
import DifferentialGeometry.Topology.Homology.Punctures.PuncturedFilling

namespace DifferentialGeometry.Topology

open Set _root_.Topology
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_disk_of_acyclic_filling (hn : 6 ≤ n) {G : M → ℝ}
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G)
    (hcompact : IsCompact (G ⁻¹' Iic 0)) (hne : (G ⁻¹' Iio 0).Nonempty)
    (hreg : ∀ x, G x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) G x)
    (hB : SimplyConnectedSpace (G ⁻¹' Iic 0))
    (hV : SimplyConnectedSpace (G ⁻¹' {0}))
    (hacyclic : SingularPair.acyclic SingularPair.integerCoefficients.{u} (TopCat.of (G ⁻¹' Iic 0))) :
    ∃ e : Disk n → M, IsClosedEmbedding e ∧ range e = G ⁻¹' Iic 0 ∧
      e '' diskSphere n = G ⁻¹' {0} := by
  obtain ⟨e, F, he, hF, hle, hlt, heq, hle0, heq0, hFreg, hD0⟩ :=
    exists_punctured_sublevel_strip (by omega) hG hne hreg
  have hD : range e ⊆ G ⁻¹' Iic 0 := by
    intro x hx
    exact (show G x < 0 from hD0 hx).le
  have hW := isSimplyConnected_sdiff_chartDisk (by omega : 3 ≤ n) he hD hB
  have hH := SingularPair.relHomologyVanishes_puncturedFilling he hD hacyclic
  have hS := he.simplyConnectedSpace_image_diskSphere (by omega : 3 ≤ n)
  have hstrip : (G ⁻¹' Iic 0) \ e '' diskInterior n = F ⁻¹' Icc (-5/8) 0 := by
    rw [← hle0, ← hlt]
    ext x
    simp only [mem_sdiff, mem_preimage, mem_Iic, mem_Iio, mem_Icc, not_lt]
    exact and_comm
  rw [hstrip] at hW hH
  rw [← heq] at hS hH
  have hV' : SimplyConnectedSpace (F ⁻¹' {0}) := by rwa [heq0]
  have hFc : IsCompact (F ⁻¹' Icc (-5/8) 0) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hF.continuous)
      (by intro x hx; rw [← hle0]; exact hx.2)
  have hF' := contMDiff_morseModelI_iff.mpr hF
  obtain ⟨Φ, hΦB, hΦV⟩ := hcobordism_strip (morseModelI n) hn F hF'
    (by norm_num : (-5/8 : ℝ) < 0) hFc (by
      intro x hx
      rw [isCriticalPointAt_morseModelI_iff hF]
      exact hFreg x hx) hW hS hV' hH
  refine ⟨Φ ∘ e, Φ.toHomeomorph.isClosedEmbedding.comp he.isClosedEmbedding, ?_, ?_⟩
  · rw [range_comp, ← hle, hΦB, hle0]
  · rw [image_comp, ← heq, hΦV, heq0]

theorem nonempty_homeomorph_boundary_of_acyclic_filling (hn : 6 ≤ n) {G : M → ℝ}
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G)
    (hcompact : IsCompact (G ⁻¹' Iic 0)) (hne : (G ⁻¹' Iio 0).Nonempty)
    (hreg : ∀ x, G x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) G x)
    (hB : SimplyConnectedSpace (G ⁻¹' Iic 0))
    (hV : SimplyConnectedSpace (G ⁻¹' {0}))
    (hacyclic : SingularPair.acyclic SingularPair.integerCoefficients.{u} (TopCat.of (G ⁻¹' Iic 0))) :
    Nonempty ((G ⁻¹' {0}) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  obtain ⟨e, he, -, heq⟩ := exists_disk_of_acyclic_filling hn hG hcompact hne hreg hB hV hacyclic
  exact ⟨(Homeomorph.setCongr heq.symm).trans
    ((he.isEmbedding.homeomorphImage (diskSphere n)).symm.trans (diskSphereHomeomorph n))⟩

end DifferentialGeometry.Topology
