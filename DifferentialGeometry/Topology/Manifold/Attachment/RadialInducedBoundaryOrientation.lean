import DifferentialGeometry.Topology.Manifold.Attachment.RadialBoundaryOrientation

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold
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
private def i3 : Fin 3 ≃ Fin (Module.finrank ℝ E3) := finCongr (by simp)
private def iR : Fin 3 ≃ Fin (Module.finrank ℝ ER) := finCongr (by simp [ER, E2, E1])
private def collarDerivative {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    Collar B → ER ≃L[ℝ] E3 := by
  let := halfClosedIntervalChartedSpace hB
  exact differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L B)
    (radialCollarOrientationMap_mfderiv_bijective hL hB)

def radialCollarTangentOrientationThree {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := halfClosedIntervalChartedSpace hB
    Collar B → Orientation ℝ ER (Fin 3) := by
  let := halfClosedIntervalChartedSpace hB
  exact fun q => Orientation.map (Fin 3) (collarDerivative hL hB q).symm.toLinearEquiv o

theorem radialCollarTangentOrientationThree_eq {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    ∀ q : Collar B, Orientation.reindex ℝ ER iR (radialCollarTangentOrientationThree hL hB o q) =
      (radialCollarSmoothOrientation hL hB (Orientation.reindex ℝ E3 i3 o)).val q := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  intro q
  change Orientation.reindex ℝ ER iR (Orientation.map (Fin 3) (collarDerivative hL hB q).symm.toLinearEquiv o) =
    tangentOrientationEquiv (collarDerivative hL hB q).symm.toLinearEquiv (Orientation.reindex ℝ E3 i3 o)
  induction o using Module.Ray.ind
  rfl

theorem retainedFaceInclusion_contMDiff {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    ContMDiff (𝓡 2) IR ∞ (Subtype.val : retainedFace B → Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let z : Ico (0 : ℝ) B := ⟨0, le_rfl, hB⟩
  have he : (Subtype.val : retainedFace B → Collar B) =
      (fun q => ((retainedFaceDiffeomorph hB).symm q, z)) := by
    funext q
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact q.property
  rw [he]
  exact (retainedFaceDiffeomorph hB).symm.contMDiff.prodMk
    (show ContMDiff (𝓡 2) (𝓡∂ 1) ∞ (fun _ : retainedFace B => z) from contMDiff_const)

def retainedFaceIntrinsicFrame {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    retainedFace B → (ℝ × E2) ≃ₗ[ℝ] ER := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact fun q => (hypersurfaceNormalFrameEquiv (retainedFaceAmbientMap L B)
    (retainedFaceOutwardNormal B) (retainedFaceNormalFrame_bijective hL hB) q).toLinearEquiv.trans
      (collarDerivative hL hB q.val).symm.toLinearEquiv
private def faceInclusionDerivative {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    retainedFace B → E2 →L[ℝ] ER := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  exact fun q => mfderiv (𝓡 2) IR (Subtype.val : retainedFace B → Collar B) q
private def faceAmbientDerivative {L B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    retainedFace B → E2 →L[ℝ] E3 := by
  let := retainedFaceChartedSpace hB
  exact fun q => mfderiv (𝓡 2) (𝓡 3) (retainedFaceAmbientMap L B) q
private theorem face_inclusion_chain {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    ∀ q : retainedFace B, faceAmbientDerivative (L := L) hB q =
      (collarDerivative hL hB q.val : ER →L[ℝ] E3).comp (faceInclusionDerivative hB q) := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  intro q
  exact mfderiv_comp q ((radialCollarOrientationMap_isSmoothEmbedding hL hB).contMDiff.mdifferentiableAt (by simp))
    ((retainedFaceInclusion_contMDiff hB).mdifferentiableAt (by simp))

theorem retainedFaceIntrinsicFrame_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace B, ∀ t : ℝ, ∀ v : E2,
      let D : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (Subtype.val : retainedFace B → Collar B) q
      retainedFaceIntrinsicFrame hL hB q (t,v) =
        t • (differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L B)
          (radialCollarOrientationMap_mfderiv_bijective hL hB) q.val).symm (retainedFaceOutwardNormal B q) + D v := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro q t v
  change (collarDerivative hL hB q.val).symm
    (t • retainedFaceOutwardNormal B q + faceAmbientDerivative (L := L) hB q v) =
      t • (collarDerivative hL hB q.val).symm (retainedFaceOutwardNormal B q) + faceInclusionDerivative hB q v
  rw [map_add, map_smul, face_inclusion_chain hL hB q]
  change t • (collarDerivative hL hB q.val).symm (retainedFaceOutwardNormal B q) +
    (collarDerivative hL hB q.val).symm ((collarDerivative hL hB q.val) (faceInclusionDerivative hB q v)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem retainedFaceSmoothOrientation_induced {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := halfClosedIntervalChartedSpace hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace B, (retainedFaceSmoothOrientation hL hB o).val q = Orientation.reindex ℝ E2 i2
      (normalFirstOrientation (retainedFaceIntrinsicFrame hL hB q) b2
        (radialCollarTangentOrientationThree hL hB o q.val)) := by
  let := halfClosedIntervalChartedSpace hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  intro q
  rw [retainedFaceSmoothOrientation_apply]
  have h := normalFirstOrientation_map
    (hypersurfaceNormalFrameEquiv (retainedFaceAmbientMap L B) (retainedFaceOutwardNormal B)
      (retainedFaceNormalFrame_bijective hL hB) q).toLinearEquiv
    (collarDerivative hL hB q.val).symm.toLinearEquiv b2 o
  exact congrArg (Orientation.reindex ℝ E2 i2) h.symm
end DifferentialGeometry.Topology.Manifold.Attachment
