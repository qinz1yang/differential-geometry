import DifferentialGeometry.Topology.Manifold.ClosedBallInducedBoundaryOrientation
import DifferentialGeometry.Topology.Manifold.Attachment.RadialWitness
import DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)
private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev ER := E2 × E1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev Collar (B : ℝ) := S2 × Ico (0 : ℝ) B
private def b2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)
private def scaledSphere (L : ℝ) (y : S2) : E3 := L • y.val
private def sphereNormal (y : S2) : E3 := y.val
private theorem scaledSphere_smooth (L : ℝ) : ContMDiff (𝓡 2) (𝓡 3) ∞ (scaledSphere L) := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S2 → E3) := contMDiff_coe_sphere (n := 2)
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun _ : S2 => L) := contMDiff_const
  exact hc.smul hs
private def scaledSphereDifferential (L : ℝ) (y : S2) : E2 →L[ℝ] E3 :=
  mfderiv (𝓡 2) (𝓡 3) (scaledSphere L) y
private theorem scaledSphere_derivative (L : ℝ) (y : S2) :
    scaledSphereDifferential L y = L • dIncl (n := 2) y := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S2 → E3) := contMDiff_coe_sphere (n := 2)
  have h := mvfderiv_fun_smul (I := 𝓡 2)
    (mdifferentiableAt_const (c := L) (x := y)) (hs.mdifferentiableAt (by simp) (x := y))
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at h
  change mvfderiv (𝓡 2) (fun z : S2 => L • z.val) y = L • mvfderiv (𝓡 2) (Subtype.val : S2 → E3) y
  exact h

def retainedFaceAmbientMap (L B : ℝ) (q : retainedFace B) : E3 :=
  radialCollarOrientationMap L B q.val

def retainedFaceOutwardNormal (B : ℝ) (q : retainedFace B) : E3 := -q.val.1.val

private theorem face_ambient_formula (L B : ℝ) (q : retainedFace B) :
    retainedFaceAmbientMap L B q = L • q.val.1.val := by
  change (L + q.val.2.val) • q.val.1.val = _
  rw [q.property, add_zero]

theorem retainedFaceOutwardNormal_outward {L B : ℝ} (hL : 0 < L) (q : retainedFace B) :
    ‖retainedFaceOutwardNormal B q‖ = 1 ∧
      ∀ s : ℝ, 0 < s → s < L →
        ‖retainedFaceAmbientMap L B q + s • retainedFaceOutwardNormal B q‖ < L ∧
        retainedFaceAmbientMap L B q + s • retainedFaceOutwardNormal B q ∉ range (radialCollarOrientationMap L B) := by
  have hy : ‖q.val.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp q.val.1.property
  refine ⟨?_, ?_⟩
  · change ‖-q.val.1.val‖ = 1
    rw [norm_neg, hy]
  · intro s hs hsL
    have hn : ‖retainedFaceAmbientMap L B q + s • retainedFaceOutwardNormal B q‖ = L - s := by
      rw [face_ambient_formula]
      change ‖L • q.val.1.val + s • (-q.val.1.val)‖ = L - s
      rw [smul_neg, ← sub_eq_add_neg, ← sub_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr hsL), hy, mul_one]
    refine ⟨by rw [hn]; linarith, ?_⟩
    rintro ⟨p, hp⟩
    have hpN : ‖radialCollarOrientationMap L B p‖ = L + p.2.val := retainedRadialMap_norm hL p
    rw [hp, hn] at hpN
    linarith [p.2.property.1]

private theorem face_ambient_smooth {L B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    ContMDiff (𝓡 2) (𝓡 3) ∞ (retainedFaceAmbientMap L B) := by
  let := retainedFaceChartedSpace hB
  have he : retainedFaceAmbientMap L B = scaledSphere L ∘ (retainedFaceDiffeomorph hB).symm := by
    funext q
    exact face_ambient_formula L B q
  rw [he]
  exact (scaledSphere_smooth L).comp (retainedFaceDiffeomorph hB).symm.contMDiff
private theorem face_normal_continuous (B : ℝ) : Continuous (retainedFaceOutwardNormal B) := by
  change Continuous (fun q : retainedFace B => -q.val.1.val)
  have hy : Continuous (fun q : retainedFace B => q.val.1) := continuous_fst.comp continuous_subtype_val
  exact ((show Continuous (Subtype.val : S2 → E3) from continuous_subtype_val).comp hy).neg
private def faceDerivative {L B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    retainedFace B → E2 →L[ℝ] E3 := by
  let := retainedFaceChartedSpace hB
  exact fun q => mfderiv (𝓡 2) (𝓡 3) (retainedFaceAmbientMap L B) q
private def faceNormalizationDerivative {B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    retainedFace B → E2 ≃L[ℝ] E2 := by
  let := retainedFaceChartedSpace hB
  exact fun q => (retainedFaceDiffeomorph hB).symm.mfderivToContinuousLinearEquiv (by simp) q
private theorem face_derivative_chain {L B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    ∀ q : retainedFace B, faceDerivative (L := L) hB q =
      (scaledSphereDifferential L ((retainedFaceDiffeomorph hB).symm q)).comp
        (faceNormalizationDerivative hB q : E2 →L[ℝ] E2) := by
  let := retainedFaceChartedSpace hB
  intro q
  have he : scaledSphere L ∘ (retainedFaceDiffeomorph hB).symm = retainedFaceAmbientMap L B := by
    funext q
    exact (face_ambient_formula L B q).symm
  have h := mfderiv_comp q ((scaledSphere_smooth L).mdifferentiableAt (by simp))
    ((retainedFaceDiffeomorph hB).symm.contMDiff.mdifferentiableAt (by simp))
  rw [he] at h
  exact h
private def reflectedRadialFrame {L : ℝ} (hL : 0 < L) (y : S2) : (ℝ × E2) ≃L[ℝ] E3 :=
  (normalFirstReflection (F := E2)).toContinuousLinearEquiv.trans (radialSphereNormalFrame hL y)
private theorem face_frame_eq {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    ∀ q : retainedFace B,
      hypersurfaceNormalFrame (retainedFaceAmbientMap L B) (retainedFaceOutwardNormal B) q =
        ((((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (faceNormalizationDerivative hB q)).trans
          (reflectedRadialFrame hL ((retainedFaceDiffeomorph hB).symm q))) : (ℝ × E2) →L[ℝ] E3) := by
  let := retainedFaceChartedSpace hB
  intro q
  apply ContinuousLinearMap.ext
  intro v
  change v.1 • (-q.val.1.val) + faceDerivative (L := L) hB q v.2 = _
  rw [face_derivative_chain hB q, scaledSphere_derivative]
  have h := radialSphereNormalFrame_apply hL ((retainedFaceDiffeomorph hB).symm q) (-v.1)
    (faceNormalizationDerivative hB q v.2)
  change v.1 • (-q.val.1.val) + L • dIncl (n := 2) ((retainedFaceDiffeomorph hB).symm q)
    (faceNormalizationDerivative hB q v.2) =
      radialSphereNormalFrame hL ((retainedFaceDiffeomorph hB).symm q) (-v.1, faceNormalizationDerivative hB q v.2)
  have hy : ((retainedFaceDiffeomorph hB).symm q).val = q.val.1.val := rfl
  rw [hy] at h
  simpa only [neg_smul, smul_neg] using h.symm

theorem retainedFaceNormalFrame_bijective {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    ∀ q : retainedFace B,
      Bijective (hypersurfaceNormalFrame (retainedFaceAmbientMap L B) (retainedFaceOutwardNormal B) q) := by
  let := retainedFaceChartedSpace hB
  intro q
  rw [face_frame_eq hL hB q]
  exact (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (faceNormalizationDerivative hB q)).trans
    (reflectedRadialFrame hL ((retainedFaceDiffeomorph hB).symm q))).bijective

def retainedFaceSmoothOrientation {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    SmoothOrientation (𝓡 2) (retainedFace B) := by
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact hypersurfaceSmoothOrientation (retainedFaceAmbientMap L B) (retainedFaceOutwardNormal B)
    (face_ambient_smooth hB) (face_normal_continuous B) (retainedFaceNormalFrame_bijective hL hB) o

theorem retainedFaceSmoothOrientation_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace B, (retainedFaceSmoothOrientation hL hB o).val q = Orientation.reindex ℝ E2 i2
      (normalFirstOrientation (hypersurfaceNormalFrameEquiv (retainedFaceAmbientMap L B)
        (retainedFaceOutwardNormal B) (retainedFaceNormalFrame_bijective hL hB) q).toLinearEquiv b2 o) := by
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro q
  rfl

private theorem map_reindex (A : E2 ≃ₗ[ℝ] E2) (q : Orientation ℝ E2 (Fin 2)) :
    Orientation.map (Fin (Module.finrank ℝ E2)) A (Orientation.reindex ℝ E2 i2 q) =
      Orientation.reindex ℝ E2 i2 (Orientation.map (Fin 2) A q) := by
  induction q using Module.Ray.ind
  rfl

theorem retainedFaceSmoothOrientation_normalization_neg {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace B,
      tangentOrientationEquiv ((retainedFaceDiffeomorph hB).symm.mfderivToContinuousLinearEquiv (by simp) q).toLinearEquiv
        ((retainedFaceSmoothOrientation hL hB o).val q) =
          -(radialSphereSmoothOrientation hL o).val ((retainedFaceDiffeomorph hB).symm q) := by
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro q
  have he : (hypersurfaceNormalFrameEquiv (retainedFaceAmbientMap L B)
      (retainedFaceOutwardNormal B) (retainedFaceNormalFrame_bijective hL hB) q).toLinearEquiv =
      ((LinearEquiv.refl ℝ ℝ).prodCongr (faceNormalizationDerivative hB q).toLinearEquiv).trans
        (reflectedRadialFrame hL ((retainedFaceDiffeomorph hB).symm q)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun A : (ℝ × E2) →L[ℝ] E3 => A v) (face_frame_eq hL hB q)
  change tangentOrientationEquiv (faceNormalizationDerivative hB q).toLinearEquiv
    ((retainedFaceSmoothOrientation hL hB o).val q) = _
  rw [retainedFaceSmoothOrientation_apply, radialSphereSmoothOrientation_apply, tangentOrientationEquiv_self,
    map_reindex, he, normalFirstOrientation_change_boundary
      (reflectedRadialFrame hL ((retainedFaceDiffeomorph hB).symm q)).toLinearEquiv
      (faceNormalizationDerivative hB q).toLinearEquiv b2 b2 o]
  rw [← Orientation.map_symm, Equiv.apply_symm_apply]
  change Orientation.reindex ℝ E2 i2
    (normalFirstOrientation ((normalFirstReflection (F := E2)).trans
      (radialSphereNormalFrame hL ((retainedFaceDiffeomorph hB).symm q)).toLinearEquiv) b2 o) = _
  rw [normalFirstOrientation_reflect_normal, Orientation.reindex_neg]
  rfl

theorem radialCapGluingDiffeomorph_reverses_orientation {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      tangentOrientationEquiv ((radialCapGluingDiffeomorph hL hB).mfderivToContinuousLinearEquiv (by simp) b).toLinearEquiv
        ((closedBallBoundarySmoothOrientation hL o).val b) =
          -(retainedFaceSmoothOrientation hL hB o).val (radialCapGluingDiffeomorph hL hB b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro b
  let φ := radialCapGluingDiffeomorph hL hB
  let ψ := (retainedFaceDiffeomorph hB).symm
  let d := closedBallBoundaryDiffeomorph hL
  let eφ : E2 ≃L[ℝ] E2 := φ.mfderivToContinuousLinearEquiv (by simp) b
  let eψ : E2 ≃L[ℝ] E2 := ψ.mfderivToContinuousLinearEquiv (by simp) (φ b)
  let ed : E2 ≃L[ℝ] E2 := d.mfderivToContinuousLinearEquiv (by simp) b
  have hmap : ψ ∘ φ = d := by
    funext x
    exact (retainedFaceDiffeomorph hB).symm_apply_apply (d x)
  have he : eφ.toLinearEquiv.trans eψ.toLinearEquiv = ed.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    have h := mfderiv_comp b (ψ.contMDiff.mdifferentiableAt (by simp)) (φ.contMDiff.mdifferentiableAt (by simp))
    rw [hmap] at h
    exact (congrArg (fun D : E2 →L[ℝ] E2 => D v) h).symm
  let os : S2 → Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) := (radialSphereSmoothOrientation hL o).val
  have hc := closedBallBoundarySmoothOrientation_normalization hL o b
  change tangentOrientationEquiv ed.toLinearEquiv ((closedBallBoundarySmoothOrientation hL o).val b) =
    os (d b) at hc
  have hf := retainedFaceSmoothOrientation_normalization_neg hL hB o (φ b)
  change tangentOrientationEquiv eψ.toLinearEquiv ((retainedFaceSmoothOrientation hL hB o).val (φ b)) =
    -os (ψ (φ b)) at hf
  change tangentOrientationEquiv eφ.toLinearEquiv ((closedBallBoundarySmoothOrientation hL o).val b) = _
  apply (tangentOrientationEquiv eψ.toLinearEquiv).injective
  rw [← tangentOrientationEquiv_trans, he, hc, tangentOrientationEquiv_neg, hf]
  have hn : - -os (ψ (φ b)) = os (ψ (φ b)) := neg_neg (os (ψ (φ b)))
  exact (congrArg os (congrFun hmap b).symm).trans hn.symm
end DifferentialGeometry.Topology.Manifold.Attachment
