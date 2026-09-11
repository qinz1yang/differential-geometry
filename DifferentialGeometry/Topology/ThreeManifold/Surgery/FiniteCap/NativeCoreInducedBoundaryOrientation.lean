import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCoreBoundaryOrientation
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold TopologicalSpace
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Collar (B : ℝ) := S2 × Ico (0 : ℝ) B
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel
private local instance : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    ChartedSpace E2 (BoundaryManifold IR X) := BoundaryManifold.chartedSpace (I := IR)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold IR X) := BoundaryManifold.isManifold (I := IR)
private def b2 : Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)
private def i3 : Fin 3 ≃ Fin (Module.finrank ℝ E3) := finCongr (by simp)
private def iR : Fin 3 ≃ Fin (Module.finrank ℝ ER) := finCongr (by simp [ER, E2])
private theorem map_reindex (A : E2 ≃ₗ[ℝ] E2) (o : Orientation ℝ E2 (Fin 2)) :
    Orientation.reindex ℝ E2 i2 (Orientation.map (Fin 2) A o) =
      tangentOrientationEquiv A (Orientation.reindex ℝ E2 i2 o) := by
  induction o using Module.Ray.ind
  rfl
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

def nativeCoreFaceDiffeomorph (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    retainedFace (cuttingCollarWidth (precision b.1)) ≃ₘ⟮𝓡 2, 𝓡 2⟯ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact (retainedFaceDiffeomorph hB).symm.trans (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)

theorem nativeCoreFaceDiffeomorph_apply (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace (cuttingCollarWidth (precision b.1)),
      (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val.val =
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q.val := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  dsimp only
  intro q
  have hq : q.val = ((retainedFaceDiffeomorph hB).symm q, ⟨0, le_rfl, hB⟩) := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext q.property
  exact (nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b ((retainedFaceDiffeomorph hB).symm q)).trans
    ((cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b ((retainedFaceDiffeomorph hB).symm q)).symm.trans
      (congrArg (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) hq.symm))

variable {L : ℝ} (hL : 0 < L) (oE : (ι × Bool) → Orientation ℝ E3 (Fin 3))

theorem nativeCoreFaceDiffeomorph_preserves_orientation (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace (cuttingCollarWidth (precision b.1)),
      tangentOrientationEquiv ((nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b).mfderivToContinuousLinearEquiv (by simp) q).toLinearEquiv
        ((retainedFaceSmoothOrientation hL hB (oE b)).val q) =
          (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  dsimp only
  intro q
  let ψ := (retainedFaceDiffeomorph hB).symm
  let β := nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b
  let γ := nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b
  let A : E2 ≃L[ℝ] E2 := ψ.mfderivToContinuousLinearEquiv (by simp) q
  let B : E2 ≃L[ℝ] E2 := β.mfderivToContinuousLinearEquiv (by simp) (ψ q)
  let C : E2 ≃L[ℝ] E2 := γ.mfderivToContinuousLinearEquiv (by simp) q
  have he : C = A.trans B := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun D : E2 →L[ℝ] E2 => D v)
      (mfderiv_comp q (β.contMDiff.mdifferentiableAt (by simp)) (ψ.contMDiff.mdifferentiableAt (by simp)))
  let O := (retainedFaceSmoothOrientation hL hB (oE b)).val q
  have hA : tangentOrientationEquiv A.toLinearEquiv O =
      -(radialSphereSmoothOrientation hL (oE b)).val (ψ q) :=
    retainedFaceSmoothOrientation_normalization_neg hL hB (oE b) q
  change tangentOrientationEquiv C.toLinearEquiv O = _
  calc
    tangentOrientationEquiv C.toLinearEquiv O =
        tangentOrientationEquiv B.toLinearEquiv (tangentOrientationEquiv A.toLinearEquiv O) := by
      rw [he]
      exact tangentOrientationEquiv_trans A.toLinearEquiv B.toLinearEquiv O
    _ = tangentOrientationEquiv B.toLinearEquiv (-(radialSphereSmoothOrientation hL (oE b)).val (ψ q)) :=
      congrArg (tangentOrientationEquiv B.toLinearEquiv) hA
    _ = (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (γ q).val :=
      (nativeCoreBoundarySmoothOrientation_apply I hdim hδ f hf hdisj hs hL oE b (ψ q)).symm

def nativeCoreTangentOrientationThree (o : SmoothOrientation I M) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    cutCore f → Orientation ℝ ER (Fin 3) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact fun p => Orientation.reindex ℝ ER iR.symm ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p)

theorem nativeCoreTangentOrientationThree_eq (o : SmoothOrientation I M) (p : cutCore f) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Orientation.reindex ℝ ER iR (nativeCoreTangentOrientationThree I hdim hδ f hf hdisj hs o p) =
      (cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (Orientation.reindex ℝ ER iR).apply_symm_apply _

private def collarDifferential (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    Collar (cuttingCollarWidth (precision b.1)) → ER ≃L[ℝ] ER := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact differentialEquivOfBijective IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b)
private def faceDifferential (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    retainedFace (cuttingCollarWidth (precision b.1)) → E2 ≃L[ℝ] E2 := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact fun q => (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b).mfderivToContinuousLinearEquiv (by simp) q

def nativeCoreBoundaryIntrinsicFrame (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    retainedFace (cuttingCollarWidth (precision b.1)) → (ℝ × E2) ≃ₗ[ℝ] ER := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  exact fun q => ((LinearEquiv.refl ℝ ℝ).prodCongr (faceDifferential I hdim hδ f hf hdisj hs b q).symm.toLinearEquiv).trans
    ((retainedFaceIntrinsicFrame hL hB q).trans (collarDifferential I hdim hδ f hf hdisj hs b q.val).toLinearEquiv)

private theorem native_face_inclusion_chain (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace (cuttingCollarWidth (precision b.1)),
      (mfderiv (𝓡 2) IR (boundaryInclusion IR (cutCore f)) (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val : E2 →L[ℝ] ER).comp
        (faceDifferential I hdim hδ f hf hdisj hs b q : E2 →L[ℝ] E2) =
          (collarDifferential I hdim hδ f hf hdisj hs b q.val : ER →L[ℝ] ER).comp
            (mfderiv (𝓡 2) IR (Subtype.val : retainedFace (cuttingCollarWidth (precision b.1)) → Collar (cuttingCollarWidth (precision b.1))) q) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  dsimp only
  intro q
  let U := nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b
  let γ := nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b
  let g : retainedFace (cuttingCollarWidth (precision b.1)) → BoundaryManifold IR (cutCore f) := Subtype.val ∘ γ
  let j := boundaryInclusion IR (cutCore f)
  let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
  let inc : retainedFace (cuttingCollarWidth (precision b.1)) → Collar (cuttingCollarWidth (precision b.1)) := Subtype.val
  have hg : ContMDiff (𝓡 2) (𝓡 2) ∞ g :=
    (contMDiff_subtype_val (I := 𝓡 2) (U := U)).comp γ.contMDiff
  have he : j ∘ g = κ ∘ inc := by
    funext z
    exact nativeCoreFaceDiffeomorph_apply I hdim hδ f hf hdisj hs b z
  let T : (retainedFace (cuttingCollarWidth (precision b.1)) → cutCore f) → (E2 →L[ℝ] ER) :=
    fun u => mfderiv (𝓡 2) IR u q
  let DJ : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR j (g q)
  let DG : E2 →L[ℝ] E2 := mfderiv (𝓡 2) (𝓡 2) g q
  let DF : E2 →L[ℝ] E2 := faceDifferential I hdim hδ f hf hdisj hs b q
  have h₁ : T (j ∘ g) = DJ.comp DG := mfderiv_comp q
    ((boundaryInclusion_contMDiff (I := IR) (M := cutCore f)).mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  have h₂ : T (κ ∘ inc) = (collarDifferential I hdim hδ f hf hdisj hs b q.val : ER →L[ℝ] ER).comp
      (mfderiv (𝓡 2) IR inc q) := mfderiv_comp q
    ((cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff.mdifferentiableAt (by simp))
    ((retainedFaceInclusion_contMDiff hB).mdifferentiableAt (by simp))
  have hD : DG = DF := mfderiv_comp_open_val (𝓡 2) (𝓡 2) U γ γ.contMDiff q
  exact (congrArg (fun D : E2 →L[ℝ] E2 => DJ.comp D) hD.symm).trans
    (h₁.symm.trans ((congrArg T he).trans h₂))

theorem nativeCoreBoundaryIntrinsicFrame_apply (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace (cuttingCollarWidth (precision b.1)), ∀ t : ℝ, ∀ v : E2,
      let D : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR (cutCore f)) (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val
      let K := differentialEquivOfBijective IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
        (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) q.val
      let R := differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L (cuttingCollarWidth (precision b.1)))
        (radialCollarOrientationMap_mfderiv_bijective hL hB) q.val
      nativeCoreBoundaryIntrinsicFrame I hdim hδ f hf hdisj hs hL b q (t, v) =
        t • K (R.symm (retainedFaceOutwardNormal (cuttingCollarWidth (precision b.1)) q)) + D v := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  dsimp only
  intro q t v
  let A := collarDifferential I hdim hδ f hf hdisj hs b q.val
  let F := faceDifferential I hdim hδ f hf hdisj hs b q
  let D : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR (cutCore f)) (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val
  change A (retainedFaceIntrinsicFrame hL hB q (t, F.symm v)) = _
  rw [retainedFaceIntrinsicFrame_apply, map_add, map_smul]
  congr 1
  have hv := congrArg (fun T : E2 →L[ℝ] ER => T (F.symm v)) (native_face_inclusion_chain I hdim hδ f hf hdisj hs b q)
  change D (F (F.symm v)) = A (mfderiv (𝓡 2) IR (Subtype.val : retainedFace (cuttingCollarWidth (precision b.1)) → Collar (cuttingCollarWidth (precision b.1))) q (F.symm v)) at hv
  rw [F.apply_symm_apply] at hv
  exact hv.symm

private theorem collar_three_push (b : ι × Bool) (o : SmoothOrientation I M)
    (hmatch :
      let hB := cuttingCollarWidth_pos (hδ b.1)
      letI := halfClosedIntervalChartedSpace hB
      letI := halfClosedInterval_isManifold hB
      ∀ q : Collar (cuttingCollarWidth (precision b.1)),
        (radialCollarSmoothOrientation hL hB (Orientation.reindex ℝ E3 i3 (oE b))).val q =
          (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : Collar (cuttingCollarWidth (precision b.1)),
      Orientation.map (Fin 3) (collarDifferential I hdim hδ f hf hdisj hs b q).toLinearEquiv
        (radialCollarTangentOrientationThree hL hB (oE b) q) =
          nativeCoreTangentOrientationThree I hdim hδ f hf hdisj hs o (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  dsimp only
  intro q
  let A := collarDifferential I hdim hδ f hf hdisj hs b q
  let oc := radialCollarTangentOrientationThree hL hB (oE b) q
  have he : Orientation.reindex ℝ ER iR (Orientation.map (Fin 3) A.toLinearEquiv oc) =
      tangentOrientationEquiv A.toLinearEquiv (Orientation.reindex ℝ ER iR oc) := by
    induction oc using Module.Ray.ind
    rfl
  apply (Orientation.reindex ℝ ER iR).injective
  rw [he, nativeCoreTangentOrientationThree_eq]
  have hc : Orientation.reindex ℝ ER iR oc = (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q :=
    (radialCollarTangentOrientationThree_eq hL hB (oE b) q).trans (hmatch q)
  rw [hc]
  exact pullbackSmoothOrientation_pushforward IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
    (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) (cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o) q

theorem nativeCoreBoundarySmoothOrientation_induced (b : ι × Bool) (o : SmoothOrientation I M)
    (hmatch :
      let hB := cuttingCollarWidth_pos (hδ b.1)
      letI := halfClosedIntervalChartedSpace hB
      letI := halfClosedInterval_isManifold hB
      ∀ q : Collar (cuttingCollarWidth (precision b.1)),
        (radialCollarSmoothOrientation hL hB (Orientation.reindex ℝ E3 i3 (oE b))).val q =
          (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let hB := cuttingCollarWidth_pos (hδ b.1)
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    letI := retainedFaceChartedSpace hB
    letI := retainedFace_isManifold hB
    ∀ q : retainedFace (cuttingCollarWidth (precision b.1)),
      (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val =
        Orientation.reindex ℝ E2 i2 (normalFirstOrientation (nativeCoreBoundaryIntrinsicFrame I hdim hδ f hf hdisj hs hL b q) b2
          (nativeCoreTangentOrientationThree I hdim hδ f hf hdisj hs o (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val.val)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let hB := cuttingCollarWidth_pos (hδ b.1)
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let := retainedFaceChartedSpace hB
  let := retainedFace_isManifold hB
  dsimp only
  intro q
  let A := collarDifferential I hdim hδ f hf hdisj hs b q.val
  let F := faceDifferential I hdim hδ f hf hdisj hs b q
  let e := retainedFaceIntrinsicFrame hL hB q
  let oc := radialCollarTangentOrientationThree hL hB (oE b) q.val
  have hc : nativeCoreTangentOrientationThree I hdim hδ f hf hdisj hs o (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val.val =
      Orientation.map (Fin 3) A.toLinearEquiv oc := by
    rw [nativeCoreFaceDiffeomorph_apply]
    exact (collar_three_push I hdim hδ f hf hdisj hs hL oE b o hmatch q.val).symm
  have hN := normalFirstOrientation_change_boundary (e.trans A.toLinearEquiv) F.symm.toLinearEquiv b2 b2
    (Orientation.map (Fin 3) A.toLinearEquiv oc)
  have hA := normalFirstOrientation_map e A.toLinearEquiv b2 oc
  have hface : (retainedFaceSmoothOrientation hL hB (oE b)).val q =
      Orientation.reindex ℝ E2 i2 (normalFirstOrientation e b2 oc) :=
    retainedFaceSmoothOrientation_induced hL hB (oE b) q
  have hpush := nativeCoreFaceDiffeomorph_preserves_orientation I hdim hδ f hf hdisj hs hL oE b q
  calc
    (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val =
        tangentOrientationEquiv F.toLinearEquiv ((retainedFaceSmoothOrientation hL hB (oE b)).val q) := hpush.symm
    _ = Orientation.reindex ℝ E2 i2 (Orientation.map (Fin 2) F.toLinearEquiv (normalFirstOrientation e b2 oc)) := by
      rw [hface]
      exact (map_reindex F.toLinearEquiv _).symm
    _ = Orientation.reindex ℝ E2 i2 (normalFirstOrientation (nativeCoreBoundaryIntrinsicFrame I hdim hδ f hf hdisj hs hL b q) b2
          (nativeCoreTangentOrientationThree I hdim hδ f hf hdisj hs o (nativeCoreFaceDiffeomorph I hdim hδ f hf hdisj hs b q).val.val)) := by
      rw [hc]
      exact congrArg (Orientation.reindex ℝ E2 i2) ((hN.trans (congrArg (Orientation.map (Fin 2) F.toLinearEquiv) hA)).symm)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
