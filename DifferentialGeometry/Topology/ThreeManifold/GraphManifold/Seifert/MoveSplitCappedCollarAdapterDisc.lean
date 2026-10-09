import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCollarAdapterRadial
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSphere

/-!
The actual plane compression restricts through the regular smooth boundary atlas to the standard
radius-three filling disc. Its full collar identity uses the corrected radius 3 minus 3s/2.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

universe u

namespace GC.Seifert

private local instance : ChartedSpace (EuclideanHalfSpace 2)
    (discPlanarBase.{u} 1).surface.Carrier :=
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace 2) discSet.{u})

private theorem compressionDisc_mem (R : ℂ ≃ₘ[ℝ] ℂ)
    (hR : R '' closedBall 0 3 = closedBall 0 3) (z : ℂ) : ‖z‖ ≤ 3 ↔ ‖R z‖ ≤ 3 := by
  constructor
  · intro hz
    exact mem_closedBall_zero_iff.mp (hR.subset ⟨z, mem_closedBall_zero_iff.mpr hz, rfl⟩)
  · intro hz
    obtain ⟨w, hw, hwe⟩ := hR.symm.subset (mem_closedBall_zero_iff.mpr hz)
    rw [R.injective hwe] at hw
    exact mem_closedBall_zero_iff.mp hw

private def compressionDiscEquiv (R : ℂ ≃ₘ[ℝ] ℂ)
    (hR : R '' closedBall 0 3 = closedBall 0 3) : discSet.{u} ≃ discSet.{u} where
  toFun x := ⟨ULift.up (R x.val.down), (mem_discSet_iff _).mpr
    ((compressionDisc_mem R hR x.val.down).mp ((mem_discSet_iff _).mp x.property))⟩
  invFun x := ⟨ULift.up (R.symm x.val.down), (mem_discSet_iff _).mpr
    ((compressionDisc_mem R hR (R.symm x.val.down)).mpr (by
      rw [R.apply_symm_apply]
      exact (mem_discSet_iff _).mp x.property))⟩
  left_inv x := by apply Subtype.ext; apply ULift.ext; exact R.symm_apply_apply x.val.down
  right_inv x := by apply Subtype.ext; apply ULift.ext; exact R.apply_symm_apply x.val.down

private def compressionDisc (R : ℂ ≃ₘ[ℝ] ℂ)
    (hR : R '' closedBall 0 3 = closedBall 0 3) : discSet.{u} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ discSet.{u} where
  toEquiv := compressionDiscEquiv R hR
  contMDiff_toFun := (discAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_planeLift_up.comp (R.contMDiff.comp contMDiff_discSet_down))
  contMDiff_invFun := (discAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_planeLift_up.comp (R.symm.contMDiff.comp contMDiff_discSet_down))

theorem exists_discCollarCompression {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ R : (discPlanarBase.{u} 1).surface.Carrier ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯
      (discPlanarBase.{u} 1).surface.Carrier,
      (∀ z, ‖(discPlanarBase.{u} 1).embedding z‖ ≤ 1 → R z = z) ∧
      ∀ (θ : Circle) (s : ℝ) (hs : 0 ≤ s), s < 1 →
        R ((discPlanarBase.{u} 1).collar 0 (θ, halfPoint s hs)) =
          (discPlanarBase.{u} 1).collar 0 (θ, halfPoint (k * s) (mul_nonneg hk.le hs)) := by
  obtain ⟨D, hfix, hray, hdisc⟩ := exists_ambientCollarCompression hk hk1
  refine ⟨compressionDisc D hdisc, ?_, ?_⟩
  · intro z hz
    apply Subtype.ext
    apply ULift.ext
    exact hfix z.val.down hz
  · intro θ s hs hs1
    have hks : k * s < 1 := by
      exact (mul_lt_mul_of_pos_left hs1 hk).trans_le (by simpa using hk1)
    apply Subtype.ext
    apply ULift.ext
    change D ((discCollar.{u} 1 (θ, halfPoint s hs)).val.down) =
      (discCollar.{u} 1 (θ, halfPoint (k * s) (mul_nonneg hk.le hs))).val.down
    rw [discCollar_apply_val 1 hs1, discCollar_apply_val 1 hks,
      ElementaryPresentation.seamRadius_one, ElementaryPresentation.seamRadius_one]
    change D ((3 + 3 * -s / 2 : ℝ) • (θ : ℂ)) =
      (3 + 3 * -(k * s) / 2 : ℝ) • (θ : ℂ)
    have he : 3 + 3 * -s / 2 = 3 - 3 * s / 2 := by ring
    rw [he, hray θ (3 - 3 * s / 2) (by linarith) (by linarith)]
    congr 1
    ring

end GC.Seifert
