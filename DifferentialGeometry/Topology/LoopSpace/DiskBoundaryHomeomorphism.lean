import DifferentialGeometry.Analysis.Complex.RiemannMapping.BoundaryModulus
import DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism

section

noncomputable section
open Set
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

theorem exists_circle_homeomorph_of_disk_homeomorph_extension
    (H : closedDisk ≃ₜ closedDisk) (ψ : OpenPartialHomeomorph ℂ ℂ)
    (hψs : ψ.source = Metric.ball (0 : ℂ) 1) (hψt : ψ.target = Metric.ball (0 : ℂ) 1)
    (hH : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1),
      (H ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = ψ z) :
    ∃ δ : loopCircle ≃ₜ loopCircle, ∀ θ, H (diskBoundary θ) = diskBoundary (δ θ) := by
  have hHi (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (H.symm ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = ψ.symm z := by
    have hzt : z ∈ ψ.target := hψt.symm ▸ hz
    have hxs : ψ.symm z ∈ Metric.ball (0 : ℂ) 1 := hψs ▸ ψ.map_target hzt
    have heq : H ⟨ψ.symm z, Metric.ball_subset_closedBall hxs⟩ =
        ⟨z, Metric.ball_subset_closedBall hz⟩ := by
      apply Subtype.ext
      rw [hH _ hxs, ψ.right_inv hzt]
    have hh := congrArg H.symm heq
    rw [H.symm_apply_apply] at hh
    exact congrArg Subtype.val hh.symm
  let C : C(closedDisk, closedDisk) := ⟨H, H.continuous⟩
  let Ci : C(closedDisk, closedDisk) := ⟨H.symm, H.symm.continuous⟩
  have hb (z : Circle) : ‖(H ⟨z, z.property.le⟩ : ℂ)‖ = 1 :=
    Complex.norm_extension_eq_one_on_sphere ψ hψs hψt C hH z.property
  have hbi (z : Circle) : ‖(H.symm ⟨z, z.property.le⟩ : ℂ)‖ = 1 :=
    Complex.norm_extension_eq_one_on_sphere ψ.symm hψt hψs Ci hHi z.property
  let ι : Circle → closedDisk := fun z => ⟨z, z.property.le⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  let κ : Circle ≃ₜ Circle :=
    { toFun := fun z => ⟨H (ι z), mem_sphere_zero_iff_norm.mpr (hb z)⟩
      invFun := fun z => ⟨H.symm (ι z), mem_sphere_zero_iff_norm.mpr (hbi z)⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change (H.symm (ι ⟨H (ι z), mem_sphere_zero_iff_norm.mpr (hb z)⟩) : ℂ) = z
        have heq : ι ⟨H (ι z), mem_sphere_zero_iff_norm.mpr (hb z)⟩ = H (ι z) := rfl
        rw [heq, H.symm_apply_apply]
      right_inv := by
        intro z
        apply Subtype.ext
        change (H (ι ⟨H.symm (ι z), mem_sphere_zero_iff_norm.mpr (hbi z)⟩) : ℂ) = z
        have heq : ι ⟨H.symm (ι z), mem_sphere_zero_iff_norm.mpr (hbi z)⟩ = H.symm (ι z) := rfl
        rw [heq, H.apply_symm_apply]
      continuous_toFun := (continuous_subtype_val.comp (H.continuous.comp hι)).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp (H.symm.continuous.comp hι)).subtype_mk _ }
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let δ := (e.trans κ).trans e.symm
  refine ⟨δ, ?_⟩
  intro θ
  apply Subtype.ext
  change (H (diskBoundary θ) : ℂ) = (AddCircle.toCircle (δ θ) : ℂ)
  have heδ : AddCircle.toCircle (δ θ) = κ (AddCircle.toCircle θ) := by
    have hm (t : loopCircle) : e t = AddCircle.toCircle t :=
      AddCircle.homeomorphCircle_apply one_ne_zero t
    rw [← hm, ← hm]
    change e (e.symm (κ (e θ))) = κ (e θ)
    exact e.apply_symm_apply _
  rw [heδ]
  rfl

end DifferentialGeometry.Topology

end

end
