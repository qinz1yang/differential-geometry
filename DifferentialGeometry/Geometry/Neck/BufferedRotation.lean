import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Metric.CylinderRotation

noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Neck
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem rotation_image_le (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) :
    roundCylinderImage (n := 2) e 0 (bufferedCylinder δ) ≤ bufferedCylinder δ := by
  rintro q ⟨p, hp, rfl⟩
  rw [roundCylinderDiffeomorph_apply]
  change -δ⁻¹ - 1 < 0 + p.2 ∧ 0 + p.2 < δ⁻¹ + 1
  change -δ⁻¹ - 1 < p.2 ∧ p.2 < δ⁻¹ + 1 at hp
  simpa only [zero_add] using hp

private def rotationMap (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) :
    bufferedCylinder δ → bufferedCylinder δ :=
  Opens.inclusion (rotation_image_le δ e) ∘ roundCylinderRestrict (n := 2) e 0 (bufferedCylinder δ)

private theorem rotationMap_val (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) (q : bufferedCylinder δ) :
    (rotationMap δ e q).val = (sphereDiffeo (n := 2) e q.val.1, q.val.2) := by
  exact (roundCylinderRestrict_apply e 0 (bufferedCylinder δ) q).trans (by rw [zero_add])

private theorem rotationMap_smooth (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) :
    ContMDiff IC IC ∞ (rotationMap δ e) :=
  (contMDiff_inclusion (rotation_image_le δ e)).comp
    (roundCylinderRestrict (n := 2) e 0 (bufferedCylinder δ)).contMDiff

def bufferedCylinderRotation (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) :
    bufferedCylinder δ ≃ₘ⟮IC, IC⟯ bufferedCylinder δ where
  toFun := rotationMap δ e
  invFun := rotationMap δ e.symm
  left_inv q := by
    apply Subtype.ext
    rw [rotationMap_val, rotationMap_val]
    apply Prod.ext
    · apply Subtype.ext
      exact e.symm_apply_apply q.val.1.val
    · rfl
  right_inv q := by
    apply Subtype.ext
    rw [rotationMap_val, rotationMap_val]
    apply Prod.ext
    · apply Subtype.ext
      exact e.apply_symm_apply q.val.1.val
    · rfl
  contMDiff_toFun := rotationMap_smooth δ e
  contMDiff_invFun := rotationMap_smooth δ e.symm

@[simp] theorem bufferedCylinderRotation_apply (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3)
    (q : bufferedCylinder δ) :
    (bufferedCylinderRotation δ e q).val = (sphereDiffeo (n := 2) e q.val.1, q.val.2) :=
  rotationMap_val δ e q

theorem bufferedCylinderRotation_mfderiv (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3)
    (q : bufferedCylinder δ) (v : TangentSpace IC q) :
    mfderiv IC IC (bufferedCylinderRotation δ e) q v =
      (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) q.val.1 v.1, v.2) := by
  have hinc := (contMDiff_inclusion (I := IC) (n := ∞) (rotation_image_le δ e)).mdifferentiable (by simp)
  have hrot := (roundCylinderRestrict (n := 2) e 0 (bufferedCylinder δ)).contMDiff.mdifferentiable (by simp)
  change mfderiv IC IC (rotationMap δ e) q v = _
  rw [rotationMap, mfderiv_comp q (hinc _) (hrot _), mfderiv_opens_incl]
  exact roundCylinderRestrict_mfderiv e 0 (bufferedCylinder δ) q v

theorem image_bufferedCylinderRotation_controlledCylinder (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) :
    bufferedCylinderRotation δ e '' controlledCylinder δ = controlledCylinder δ := by
  apply Subset.antisymm
  · rintro q ⟨p, hp, rfl⟩
    change (bufferedCylinderRotation δ e p).val.2 ∈ Icc (-δ⁻¹) δ⁻¹
    rw [bufferedCylinderRotation_apply]
    exact hp
  · intro q hq
    refine ⟨(bufferedCylinderRotation δ e).symm q, ?_, (bufferedCylinderRotation δ e).apply_symm_apply q⟩
    change (rotationMap δ e.symm q).val.2 ∈ Icc (-δ⁻¹) δ⁻¹
    rw [rotationMap_val]
    exact hq

theorem pullback_referenceMetric_bufferedCylinderRotation (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) :
    Diffeomorph.pullbackMetric (referenceMetric δ) (bufferedCylinderRotation δ e) =
      referenceMetric δ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change (roundCylinderMetric (E := E3) (n := 2)).inner (bufferedCylinderRotation δ e x).val
    (mfderiv IC IC (bufferedCylinderRotation δ e) x v)
    (mfderiv IC IC (bufferedCylinderRotation δ e) x w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner x.val v w
  rw [bufferedCylinderRotation_mfderiv, bufferedCylinderRotation_mfderiv, bufferedCylinderRotation_apply]
  have h := congrArg (fun g => g.inner x.val v w)
    (pullback_roundCylinderMetric_roundCylinderDiffeomorph (n := 2) e 0)
  have hinner := Diffeomorph.pullbackMetric_inner
    (roundCylinderMetric (E := E3) (n := 2)) (roundCylinderDiffeomorph (n := 2) e 0) x.val v w
  have h' := hinner.symm.trans h
  have hv := roundCylinderDiffeomorph_mfderiv (n := 2) e 0 x.val v
  have hw := roundCylinderDiffeomorph_mfderiv (n := 2) e 0 x.val w
  have hx := roundCylinderDiffeomorph_apply (n := 2) e 0 x.val
  simp only [zero_add] at hx
  exact (congrArg₂ (fun v w => (roundCylinderMetric (E := E3) (n := 2)).inner
    ((roundCylinderDiffeomorph (n := 2) e 0) x.val) v w) hv hw).symm.trans h' |>
    fun he => hx ▸ he

theorem metricDerivENormSupOn_bufferedCylinderRotation (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3)
    (H HInf : SmoothRiemannianMetric IC (bufferedCylinder δ)) (p : ℕ) :
    metricDerivENormSupOn (controlledCylinder δ) p
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e))
      (Diffeomorph.pullbackMetric HInf (bufferedCylinderRotation δ e)) (referenceMetric δ) =
    metricDerivENormSupOn (controlledCylinder δ) p H HInf (referenceMetric δ) := by
  have hn : ∀ j q, metricDerivNorm j
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e))
      (Diffeomorph.pullbackMetric HInf (bufferedCylinderRotation δ e)) (referenceMetric δ) q =
      metricDerivNorm j H HInf (referenceMetric δ) (bufferedCylinderRotation δ e q) := by
    intro j q
    simpa only [pullback_referenceMetric_bufferedCylinderRotation] using
      metricDerivNorm_pullback H HInf (referenceMetric δ) (bufferedCylinderRotation δ e) j q
  have he : metricDerivENormSupOn (controlledCylinder δ) p
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e))
      (Diffeomorph.pullbackMetric HInf (bufferedCylinderRotation δ e)) (referenceMetric δ) =
      metricDerivENormSupOn (bufferedCylinderRotation δ e '' controlledCylinder δ) p H HInf (referenceMetric δ) := by
    simp only [metricDerivENormSupOn, hn, iSup_image]
  rw [image_bufferedCylinderRotation_controlledCylinder] at he
  exact he

@[simp] theorem bufferedCylinderRotation_symm_apply (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3)
    (q : bufferedCylinder δ) :
    ((bufferedCylinderRotation δ e).symm q).val = (sphereDiffeo (n := 2) e.symm q.val.1, q.val.2) :=
  rotationMap_val δ e.symm q

theorem image_bufferedCylinderRotation_height (δ : ℝ) (e : E3 ≃ₗᵢ[ℝ] E3) (S : Set ℝ) :
    bufferedCylinderRotation δ e '' {q : bufferedCylinder δ | q.val.2 ∈ S} =
      {q : bufferedCylinder δ | q.val.2 ∈ S} := by
  apply Subset.antisymm
  · rintro q ⟨p, hp, rfl⟩
    change (bufferedCylinderRotation δ e p).val.2 ∈ S
    rw [bufferedCylinderRotation_apply]
    exact hp
  · intro q hq
    refine ⟨(bufferedCylinderRotation δ e).symm q, ?_, (bufferedCylinderRotation δ e).apply_symm_apply q⟩
    change ((bufferedCylinderRotation δ e).symm q).val.2 ∈ S
    rw [bufferedCylinderRotation_symm_apply]
    exact hq

end DifferentialGeometry.Geometry.Neck
