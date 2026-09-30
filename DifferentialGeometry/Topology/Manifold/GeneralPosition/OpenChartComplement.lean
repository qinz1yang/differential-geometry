import DifferentialGeometry.Topology.Manifold.GeneralPosition.HigherPushOff
import DifferentialGeometry.Topology.Homology.Punctures.PuncturedFilling

namespace DifferentialGeometry.Topology

open Set Metric
open scoped ContinuousMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isChartDisk.nullhomotopic_map_compl_halfDisk_of_homotopyEquiv_sphere {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, ((e '' halfDisk n)ᶜ : Set M))) :
    f.Nullhomotopic := by
  have h := he.isHomotopyEquivInclusion_sdiff_halfDisk (B := univ) (subset_univ _)
  have hleft : (univ : Set M) \ e '' diskInterior n = (e '' diskInterior n)ᶜ := by ext x; simp
  have hright : (univ : Set M) \ e '' halfDisk n = (e '' halfDisk n)ᶜ := by ext x; simp
  rw [hleft, hright] at h
  obtain ⟨q, _⟩ := h
  have hnull := (he.nullhomotopic_map_compl_of_homotopyEquiv_sphere hkn eM
    (q.invFun.comp f)).comp_right q.toFun
  obtain ⟨c, hc⟩ := hnull
  exact ⟨c, ((q.right_inv.comp (.refl f)).symm).trans hc⟩

theorem isChartDisk.exists_disk_extension_compl_halfDisk_of_homotopyEquiv_sphere {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, ((e '' halfDisk n)ᶜ : Set M))) :
    ∃ F : C(Disk (k + 1), ((e '' halfDisk n)ᶜ : Set M)),
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) :=
  exists_disk_extension_of_nullhomotopic f
    (he.nullhomotopic_map_compl_halfDisk_of_homotopyEquiv_sphere hkn eM f)

end DifferentialGeometry.Topology
