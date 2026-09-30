import DifferentialGeometry.Topology.Manifold.GeneralPosition.OpenChartComplement

namespace DifferentialGeometry.Topology

open Set Metric
open scoped ContinuousMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isChartDisk.exists_disk_extension_sdiff_of_nullhomotopic {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    {B : Set M} (hD : range e ⊆ B)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      (B \ e '' diskInterior n : Set M)))
    (hf : (⟨fun x => ⟨(f x).1, (f x).2.1⟩,
      (continuous_subtype_val.comp f.continuous).subtype_mk _⟩ :
      C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, B)).Nullhomotopic) :
    ∃ F : C(Disk (k + 1), (B \ e '' diskInterior n : Set M)),
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) := by
  let fB : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, B) :=
    ⟨fun x => ⟨(f x).1, (f x).2.1⟩,
      (continuous_subtype_val.comp f.continuous).subtype_mk _⟩
  obtain ⟨G, hG⟩ := exists_disk_extension_of_nullhomotopic fB hf
  obtain ⟨H, hH, havoid, hfix, hin⟩ := he.exists_push_off_on_compact
    (by omega : k + 1 < n) (continuous_subtype_val.comp G.continuous)
  have hHB (x : Disk (k + 1)) : H x ∈ B := by
    by_cases hx : (G x).1 ∈ e '' diskInterior n
    · exact hD (hin x hx)
    · rw [hfix x hx]
      exact (G x).2
  refine ⟨⟨fun x => ⟨H x, hHB x, havoid x⟩, hH.subtype_mk _⟩, fun x => ?_⟩
  apply Subtype.ext
  change H x.1 = (f (diskSphereHomeomorph (k + 1) x)).1
  have hx : (Subtype.val ∘ G) x.1 ∉ e '' diskInterior n := by
    change (G x.1).1 ∉ _
    rw [hG x]
    exact (f _).2.2
  rw [hfix x.1 hx]
  exact congrArg Subtype.val (hG x)

theorem isChartDisk.nullhomotopic_sdiff_halfDisk {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    {B : Set M} (hD : range e ⊆ B)
    (hB : ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, B), f.Nullhomotopic)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      (B \ e '' halfDisk n : Set M))) : f.Nullhomotopic := by
  obtain ⟨q, _⟩ := he.isHomotopyEquivInclusion_sdiff_halfDisk hD
  obtain ⟨F, hF⟩ := he.exists_disk_extension_sdiff_of_nullhomotopic hkn hD
    (q.invFun.comp f) (hB _)
  have hnull := (nullhomotopic_of_disk_extension (q.invFun.comp f) F hF).comp_right q.toFun
  obtain ⟨c, hc⟩ := hnull
  exact ⟨c, ((q.right_inv.comp (.refl f)).symm).trans hc⟩

theorem isChartDisk.exists_disk_extension_sdiff_halfDisk {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    {B : Set M} (hD : range e ⊆ B)
    (hB : ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, B), f.Nullhomotopic)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      (B \ e '' halfDisk n : Set M))) :
    ∃ F : C(Disk (k + 1), (B \ e '' halfDisk n : Set M)),
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) :=
  exists_disk_extension_of_nullhomotopic f (he.nullhomotopic_sdiff_halfDisk hkn hD hB f)

theorem isChartDisk.nullhomotopic_sdiff_halfDisk_of_contractible {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    {B : Set M} [ContractibleSpace B] (hD : range e ⊆ B)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      (B \ e '' halfDisk n : Set M))) : f.Nullhomotopic :=
  he.nullhomotopic_sdiff_halfDisk hkn hD (fun g => (id_nullhomotopic B).comp_left g) f

end DifferentialGeometry.Topology
