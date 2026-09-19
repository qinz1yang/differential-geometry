import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Support

noncomputable section

open Set

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def affineInverseHomeomorph (b : E) {r : ℝ} (hr : r ≠ 0) : E ≃ₜ E where
  toFun x := r⁻¹ • (x - b)
  invFun x := b + r • x
  left_inv x := by
    simp [smul_smul, hr, sub_eq_add_neg]
  right_inv x := by
    simp [smul_smul, hr, sub_eq_add_neg, add_assoc]
  continuous_toFun := continuous_const.smul (continuous_id.sub continuous_const)
  continuous_invFun := continuous_const.add (continuous_const.smul continuous_id)

private def spatialAffineInverseHomeomorph (b : E) {r : ℝ} (hr : r ≠ 0) :
    (ℝ × E) ≃ₜ (ℝ × E) where
  toFun p := (p.1, r⁻¹ • (p.2 - b))
  invFun p := (p.1, b + r • p.2)
  left_inv p := by
    rcases p with ⟨t, x⟩
    simp [smul_smul, hr, sub_eq_add_neg]
  right_inv p := by
    rcases p with ⟨t, x⟩
    simp [smul_smul, hr, sub_eq_add_neg, add_assoc]
  continuous_toFun :=
    continuous_fst.prodMk (continuous_const.smul (continuous_snd.sub continuous_const))
  continuous_invFun :=
    continuous_fst.prodMk (continuous_const.add (continuous_const.smul continuous_snd))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_comp_affine_inverse (b : E) (r : ℝ)
    {k : WithTop ℕ∞} {φ : E → F} (hφ : ContDiff ℝ k φ) :
    ContDiff ℝ k (fun z => φ (r⁻¹ • (z - b))) := by
  exact hφ.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))

theorem contDiff_comp_spatial_affine_inverse (b : E) (r : ℝ)
    {k : WithTop ℕ∞} {φ : ℝ × E → F} (hφ : ContDiff ℝ k φ) :
    ContDiff ℝ k (fun p : ℝ × E => φ (p.1, r⁻¹ • (p.2 - b))) := by
  exact hφ.comp
    (contDiff_fst.prodMk (contDiff_const.smul (contDiff_snd.sub contDiff_const)))

theorem fderiv_comp_affine_inverse_apply (b : E) (r : ℝ) {φ : E → F} {z : E}
    (hφ : DifferentiableAt ℝ φ (r⁻¹ • (z - b))) (v : E) :
    fderiv ℝ (fun x => φ (r⁻¹ • (x - b))) z v =
      r⁻¹ • fderiv ℝ φ (r⁻¹ • (z - b)) v := by
  have hmap : HasFDerivAt (fun x : E => r⁻¹ • (x - b))
      (r⁻¹ • ContinuousLinearMap.id ℝ E) z :=
    ((hasFDerivAt_id z).sub_const b).const_smul r⁻¹
  have hd := (hφ.hasFDerivAt.comp z hmap).fderiv
  calc
    fderiv ℝ (fun x => φ (r⁻¹ • (x - b))) z v =
        fderiv ℝ φ (r⁻¹ • (z - b)) (r⁻¹ • v) :=
      congrArg (fun L : E →L[ℝ] F => L v) hd
    _ = r⁻¹ • fderiv ℝ φ (r⁻¹ • (z - b)) v := map_smul _ _ _

theorem fderiv_comp_spatial_affine_inverse_apply (b : E) (r : ℝ)
    {φ : ℝ × E → F} {p : ℝ × E}
    (hφ : DifferentiableAt ℝ φ (p.1, r⁻¹ • (p.2 - b))) (v : ℝ × E) :
    fderiv ℝ (fun q : ℝ × E => φ (q.1, r⁻¹ • (q.2 - b))) p v =
      fderiv ℝ φ (p.1, r⁻¹ • (p.2 - b)) (v.1, r⁻¹ • v.2) := by
  have hmap : HasFDerivAt (fun q : ℝ × E => (q.1, r⁻¹ • (q.2 - b)))
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        (r⁻¹ • ContinuousLinearMap.snd ℝ ℝ E)) p :=
    hasFDerivAt_fst.prodMk ((hasFDerivAt_snd.sub_const b).const_smul r⁻¹)
  exact congrArg (fun L : (ℝ × E) →L[ℝ] F => L v)
    (hφ.hasFDerivAt.comp p hmap).fderiv

theorem fderiv_comp_spatial_affine_inverse_time (b : E) (r : ℝ)
    {φ : ℝ × E → F} {p : ℝ × E}
    (hφ : DifferentiableAt ℝ φ (p.1, r⁻¹ • (p.2 - b))) :
    fderiv ℝ (fun q : ℝ × E => φ (q.1, r⁻¹ • (q.2 - b))) p (1, 0) =
      fderiv ℝ φ (p.1, r⁻¹ • (p.2 - b)) (1, 0) := by
  simpa only [smul_zero] using
    fderiv_comp_spatial_affine_inverse_apply b r hφ (1, 0)

theorem fderiv_comp_spatial_affine_inverse_spatial (b : E) (r : ℝ)
    {φ : ℝ × E → F} {p : ℝ × E}
    (hφ : DifferentiableAt ℝ φ (p.1, r⁻¹ • (p.2 - b))) (v : E) :
    fderiv ℝ (fun q : ℝ × E => φ (q.1, r⁻¹ • (q.2 - b))) p (0, v) =
      r⁻¹ • fderiv ℝ φ (p.1, r⁻¹ • (p.2 - b)) (0, v) := by
  rw [fderiv_comp_spatial_affine_inverse_apply b r hφ]
  simpa using
    map_smul (fderiv ℝ φ (p.1, r⁻¹ • (p.2 - b))) r⁻¹ ((0 : ℝ), v)

theorem fderiv_comp_affine_inverse_at_image (b : E) {r : ℝ} (hr : r ≠ 0)
    {φ : E → F} {y : E} (hφ : DifferentiableAt ℝ φ y) (v : E) :
    fderiv ℝ (fun x => φ (r⁻¹ • (x - b))) (b + r • y) v =
      r⁻¹ • fderiv ℝ φ y v := by
  have hcancel : r⁻¹ • (b + r • y - b) = y := by
    simp [smul_smul, hr, sub_eq_add_neg, add_assoc]
  have hφ' : DifferentiableAt ℝ φ (r⁻¹ • (b + r • y - b)) := by
    simpa only [hcancel] using hφ
  simpa only [hcancel] using fderiv_comp_affine_inverse_apply b r hφ' v

theorem fderiv_comp_spatial_affine_inverse_time_at_image (b : E)
    {r : ℝ} (hr : r ≠ 0) {φ : ℝ × E → F} {t : ℝ} {y : E}
    (hφ : DifferentiableAt ℝ φ (t, y)) :
    fderiv ℝ (fun q : ℝ × E => φ (q.1, r⁻¹ • (q.2 - b))) (t, b + r • y) (1, 0) =
      fderiv ℝ φ (t, y) (1, 0) := by
  have hcancel : r⁻¹ • (b + r • y - b) = y := by
    simp [smul_smul, hr, sub_eq_add_neg, add_assoc]
  have hφ' : DifferentiableAt ℝ φ (t, r⁻¹ • (b + r • y - b)) := by
    simpa only [hcancel] using hφ
  simpa only [hcancel] using
    fderiv_comp_spatial_affine_inverse_time b r (p := (t, b + r • y)) hφ'

theorem fderiv_comp_spatial_affine_inverse_spatial_at_image (b : E)
    {r : ℝ} (hr : r ≠ 0) {φ : ℝ × E → F} {t : ℝ} {y : E}
    (hφ : DifferentiableAt ℝ φ (t, y)) (v : E) :
    fderiv ℝ (fun q : ℝ × E => φ (q.1, r⁻¹ • (q.2 - b))) (t, b + r • y) (0, v) =
      r⁻¹ • fderiv ℝ φ (t, y) (0, v) := by
  have hcancel : r⁻¹ • (b + r • y - b) = y := by
    simp [smul_smul, hr, sub_eq_add_neg, add_assoc]
  have hφ' : DifferentiableAt ℝ φ (t, r⁻¹ • (b + r • y - b)) := by
    simpa only [hcancel] using hφ
  simpa only [hcancel] using
    fderiv_comp_spatial_affine_inverse_spatial b r (p := (t, b + r • y)) hφ' v

variable {G : Type*} [Zero G]

theorem hasCompactSupport_comp_affine_inverse (b : E) {r : ℝ} (hr : r ≠ 0)
    {φ : E → G} (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z => φ (r⁻¹ • (z - b))) := by
  exact hφ.comp_homeomorph (affineInverseHomeomorph b hr)

theorem hasCompactSupport_comp_spatial_affine_inverse (b : E) {r : ℝ} (hr : r ≠ 0)
    {φ : ℝ × E → G} (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun p : ℝ × E => φ (p.1, r⁻¹ • (p.2 - b))) := by
  exact hφ.comp_homeomorph (spatialAffineInverseHomeomorph b hr)

theorem tsupport_comp_affine_inverse_subset (b : E) {r : ℝ} (hr : r ≠ 0)
    {φ : E → G} {Ω : Set E} (hφ : tsupport φ ⊆ Ω) :
    tsupport (fun z => φ (r⁻¹ • (z - b))) ⊆ (fun y => b + r • y) '' Ω := by
  intro z hz
  have hz' : r⁻¹ • (z - b) ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ
      (continuous_const.smul (continuous_id.sub continuous_const)) hz
  refine ⟨r⁻¹ • (z - b), hφ hz', ?_⟩
  simp [smul_smul, hr, sub_eq_add_neg]

theorem tsupport_comp_spatial_affine_inverse_subset (b : E) {r : ℝ} (hr : r ≠ 0)
    {φ : ℝ × E → G} {T : Set ℝ} {Ω : Set E}
    (hφ : tsupport φ ⊆ T ×ˢ Ω) :
    tsupport (fun p : ℝ × E => φ (p.1, r⁻¹ • (p.2 - b))) ⊆
      T ×ˢ ((fun y => b + r • y) '' Ω) := by
  intro p hp
  have hp' : (p.1, r⁻¹ • (p.2 - b)) ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ
      (continuous_fst.prodMk (continuous_const.smul
        (continuous_snd.sub continuous_const))) hp
  refine ⟨(hφ hp').1, ⟨r⁻¹ • (p.2 - b), (hφ hp').2, ?_⟩⟩
  simp [smul_smul, hr, sub_eq_add_neg]

theorem tsupport_comp_affine_inverse_subset_of_preimage (b : E) {r : ℝ} (hr : r ≠ 0)
    {φ : E → G} {Ω : Set E} (hφ : tsupport φ ⊆ (fun y => b + r • y) ⁻¹' Ω) :
    tsupport (fun z => φ (r⁻¹ • (z - b))) ⊆ Ω := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := tsupport_comp_affine_inverse_subset b hr hφ hz
  exact hy

theorem tsupport_comp_spatial_affine_inverse_subset_of_preimage
    (b : E) {r : ℝ} (hr : r ≠ 0) {φ : ℝ × E → G} {T : Set ℝ} {Ω : Set E}
    (hφ : tsupport φ ⊆ T ×ˢ ((fun y => b + r • y) ⁻¹' Ω)) :
    tsupport (fun p : ℝ × E => φ (p.1, r⁻¹ • (p.2 - b))) ⊆ T ×ˢ Ω := by
  intro p hp
  obtain ⟨ht, y, hy, heq⟩ := tsupport_comp_spatial_affine_inverse_subset b hr hφ hp
  exact ⟨ht, heq ▸ hy⟩

end DifferentialGeometry.Analysis.Calculus

end
