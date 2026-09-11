import DifferentialGeometry.Topology.LoopSpace.RadialExtension



noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Topology



def radialDiskHomeomorph (F : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hF' : LipschitzWith L F.symm) : closedDisk ≃ₜ closedDisk where
  toFun z := ⟨radialExtension F z, by
    simpa only [mem_closedBall, dist_zero_right, radialExtension_norm] using z.property⟩
  invFun z := ⟨radialExtension F.symm z, by
    simpa only [mem_closedBall, dist_zero_right, radialExtension_norm] using z.property⟩
  left_inv z := by
    apply Subtype.ext
    change radialExtension F.symm (radialExtension F z) = (z : ℂ)
    rw [← radialExtension_comp]
    have heq : (F.symm ∘ F : Circle → Circle) = id := funext F.symm_apply_apply
    rw [heq, radialExtension_id]
  right_inv z := by
    apply Subtype.ext
    change radialExtension F (radialExtension F.symm z) = (z : ℂ)
    rw [← radialExtension_comp]
    have heq : (F ∘ F.symm : Circle → Circle) = id := funext F.apply_symm_apply
    rw [heq, radialExtension_id]
  continuous_toFun := ((radialExtension_lipschitz hF).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((radialExtension_lipschitz hF').continuous.comp continuous_subtype_val).subtype_mk _

theorem radialDiskHomeomorph_lipschitz (F : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hF' : LipschitzWith L F.symm) :
    LipschitzWith (2 * K + 1) (radialDiskHomeomorph F hF hF') := by
  intro z w
  exact radialExtension_lipschitz hF z w

theorem radialDiskHomeomorph_symm_lipschitz (F : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hF' : LipschitzWith L F.symm) :
    LipschitzWith (2 * L + 1) (radialDiskHomeomorph F hF hF').symm := by
  intro z w
  exact radialExtension_lipschitz hF' z w



def geometricCircleHomeomorph (ψ : loopCircle ≃ₜ loopCircle) : Circle ≃ₜ Circle :=
  ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans ψ).trans
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)

theorem geometricCircleHomeomorph_boundary (ψ : loopCircle ≃ₜ loopCircle) (θ : loopCircle) :
    geometricCircleHomeomorph ψ (AddCircle.toCircle θ) = AddCircle.toCircle (ψ θ) := by
  have hleft : (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
      (AddCircle.toCircle θ) = θ := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply θ
  change (AddCircle.homeomorphCircle one_ne_zero)
    (ψ ((AddCircle.homeomorphCircle one_ne_zero).symm (AddCircle.toCircle θ))) = _
  rw [hleft, AddCircle.homeomorphCircle_apply]

theorem geometricCircleHomeomorph_symm (ψ : loopCircle ≃ₜ loopCircle) :
    (geometricCircleHomeomorph ψ).symm = geometricCircleHomeomorph ψ.symm := rfl



theorem geometricCircleHomeomorph_lipschitz (ψ : loopCircle ≃ₜ loopCircle) {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) : ∃ C : ℝ≥0, LipschitzWith C (geometricCircleHomeomorph ψ) := by
  have hb : LipschitzWith ⟨2 * Real.pi, by positivity⟩ (fun θ : loopCircle => AddCircle.toCircle θ) :=
    fun x y => circle_boundary_lipschitz x y
  have h := hb.comp (hψ.comp circle_parameter_lipschitz)
  refine ⟨⟨2 * Real.pi, by positivity⟩ * (K * 1), ?_⟩
  intro z w
  change edist ((AddCircle.homeomorphCircle one_ne_zero)
      (ψ ((AddCircle.homeomorphCircle one_ne_zero).symm z)))
    ((AddCircle.homeomorphCircle one_ne_zero)
      (ψ ((AddCircle.homeomorphCircle one_ne_zero).symm w))) ≤ _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
  exact h z w



theorem exists_radial_disk_reparametrization (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm) :
    ∃ φ : closedDisk ≃ₜ closedDisk,
      (∀ θ, φ (diskBoundary θ) = diskBoundary (ψ θ)) ∧
      ∃ K' L' : ℝ≥0, LipschitzWith K' φ ∧ LipschitzWith L' φ.symm := by
  obtain ⟨Cf, hf⟩ := geometricCircleHomeomorph_lipschitz ψ hψ
  obtain ⟨Ci, hi⟩ := geometricCircleHomeomorph_lipschitz ψ.symm hψ'
  rw [← geometricCircleHomeomorph_symm] at hi
  let φ := radialDiskHomeomorph (geometricCircleHomeomorph ψ) hf hi
  refine ⟨φ, ?_, _, _, radialDiskHomeomorph_lipschitz _ hf hi,
    radialDiskHomeomorph_symm_lipschitz _ hf hi⟩
  intro θ
  apply Subtype.ext
  change radialExtension (geometricCircleHomeomorph ψ) (AddCircle.toCircle θ : ℂ) =
    (AddCircle.toCircle (ψ θ) : ℂ)
  rw [radialExtension_circle, geometricCircleHomeomorph_boundary]

end DifferentialGeometry.Topology
