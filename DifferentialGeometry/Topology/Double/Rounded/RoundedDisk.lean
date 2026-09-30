import DifferentialGeometry.Topology.Double.Rounded.RoundedDouble
import DifferentialGeometry.Topology.HighDimensional.TwistedSphere

namespace DifferentialGeometry.Topology.RoundedDouble

open Set Metric _root_.Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    {g : M → ℝ} {d : Disk n → boundary g}

def diskProjection (d : Disk n → boundary g) : Disk n → M := fun x => (d x).1.1

theorem disk_projection (hd : IsClosedEmbedding d)
    (hrange : range d = {p : boundary g | p.1.2 ≤ 0})
    (hboundary : d '' diskSphere n = {p : boundary g | p.1.2 = 0}) :
    IsClosedEmbedding (diskProjection d) ∧ range (diskProjection d) = base g ∧
      diskProjection d '' diskSphere n = g ⁻¹' {0} := by
  have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hdl (x : Disk n) : d x ∈ range (lower g) := by
    apply (mem_range_lower (d x)).mpr
    have hx : d x ∈ range d := mem_range_self x
    rwa [hrange] at hx
  have hproj_inj : Function.Injective (diskProjection d) := by
    intro x y hxy
    obtain ⟨a, ha⟩ := hdl x
    obtain ⟨b, hb⟩ := hdl y
    have hab : a = b := by
      apply Subtype.ext
      change (lower g a).1.1 = (lower g b).1.1
      rw [ha, hb]
      exact hxy
    apply hd.injective
    rw [← ha, ← hb, hab]
  refine ⟨(continuous_fst.comp (continuous_subtype_val.comp hd.continuous)).isClosedEmbedding
    hproj_inj, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact fst_mem_base (boundary_subset_filling g (d y).2)
    · intro hx
      have hp : lower g ⟨x, hx⟩ ∈ range d := by
        rw [hrange]
        exact (mem_range_lower _).mp (mem_range_self _)
      obtain ⟨y, hy⟩ := hp
      exact ⟨y, congrArg (fun p : boundary g => p.1.1) hy⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have ht : (d y).1.2 = 0 := by
        have hm : d y ∈ d '' diskSphere n := mem_image_of_mem d hy
        rwa [hboundary] at hm
      have he := (d y).2
      change g (diskProjection d y) = 0
      change g (d y).1.1 + (d y).1.2 ^ 2 = 0 at he
      simpa only [diskProjection, ht, zero_pow (by decide : 2 ≠ 0), add_zero] using he
    · intro hx
      have hx0 : g x = 0 := hx
      let p : boundary g := ⟨(x, 0), by simp [boundary, hx0]⟩
      have hp : p ∈ d '' diskSphere n := by
        rw [hboundary]
        rfl
      obtain ⟨y, hy, hyp⟩ := hp
      exact ⟨y, hy, congrArg (fun q : boundary g => q.1.1) hyp⟩

theorem sphere_homeomorph_of_lower_disk {m : ℕ}
    {e : Disk (m + 1) → M} (he : IsClosedEmbedding e)
    (herange : range e = g ⁻¹' Ici 0)
    (heboundary : e '' diskSphere (m + 1) = g ⁻¹' {0})
    {d : Disk (m + 1) → boundary g} (hd : IsClosedEmbedding d)
    (hdrange : range d = {p : boundary g | p.1.2 ≤ 0})
    (hdboundary : d '' diskSphere (m + 1) = {p : boundary g | p.1.2 = 0}) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) := by
  obtain ⟨hproj, hrange, hboundary⟩ := disk_projection hd hdrange hdboundary
  apply twisted_sphere_homeomorph he hproj
  · rw [herange, hrange]
    ext x
    simp only [mem_union, mem_preimage, mem_Ici, base, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total 0 (g x)
  · rw [herange, hrange, heboundary]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Ici, base, mem_ofPred_eq,
      mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  · exact heboundary.trans hboundary.symm

end DifferentialGeometry.Topology.RoundedDouble
