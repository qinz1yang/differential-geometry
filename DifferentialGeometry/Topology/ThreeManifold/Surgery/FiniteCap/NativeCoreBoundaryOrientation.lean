import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCuttingSpheres
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient
import DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison

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
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.isManifold (I := 𝓡∂ 3)

private def pushThroughDiffeo {X Y : Type*} [TopologicalSpace X] [ChartedSpace E2 X] [IsManifold (𝓡 2) ∞ X]
    [TopologicalSpace Y] [ChartedSpace E2 Y] [IsManifold (𝓡 2) ∞ Y]
    (D : X ≃ₘ⟮𝓡 2, 𝓡 2⟯ Y) (o : SmoothOrientation (𝓡 2) X) : SmoothOrientation (𝓡 2) Y :=
  pullbackSmoothOrientation (𝓡 2) (𝓡 2) D.symm D.symm.contMDiff
    (fun p => (D.symm.mfderivToContinuousLinearEquiv (by simp) p).bijective) o
private theorem pushThroughDiffeo_apply {X Y : Type*} [TopologicalSpace X] [ChartedSpace E2 X] [IsManifold (𝓡 2) ∞ X]
    [TopologicalSpace Y] [ChartedSpace E2 Y] [IsManifold (𝓡 2) ∞ Y]
    (D : X ≃ₘ⟮𝓡 2, 𝓡 2⟯ Y) (o : SmoothOrientation (𝓡 2) X) (y : X) :
    (pushThroughDiffeo D o).val (D y) =
      tangentOrientationEquiv (D.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv (o.val y) := by
  let A : E2 ≃L[ℝ] E2 := D.mfderivToContinuousLinearEquiv (by simp) y
  let hb := fun p => (D.symm.mfderivToContinuousLinearEquiv (by simp) p).bijective
  let B : E2 ≃L[ℝ] E2 := differentialEquivOfBijective (𝓡 2) (𝓡 2) D.symm hb (D y)
  have he : B = A.symm := by
    have hd := mfderiv_comp y (D.symm.contMDiff.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))
    have hid : D.symm ∘ D = id := funext D.symm_apply_apply
    rw [hid, mfderiv_id] at hd
    apply ContinuousLinearEquiv.ext
    funext v
    have hv := congrArg (fun T : E2 →L[ℝ] E2 => T (A.symm v)) hd
    change A.symm v = B (A (A.symm v)) at hv
    rw [A.apply_symm_apply] at hv
    exact hv.symm
  change tangentOrientationEquiv B.symm.toLinearEquiv (o.val (D.symm (D y))) =
    tangentOrientationEquiv A.toLinearEquiv (o.val y)
  rw [D.symm_apply_apply, he]
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

def nativeCuttingSphereOpens (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    Opens (BoundaryManifold IR (cutCore f)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (nativeCuttingSphereMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).image

def nativeCuttingSphereDiffeomorph (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact diffeomorphOntoImage (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)
    (nativeCuttingSphereMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b) (nativeCuttingSphereMap_injective I hdim hδ f hf hdisj hs b)

theorem nativeCuttingSphereDiffeomorph_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b y).val.val =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact nativeCuttingSphereMap_apply I hdim hδ f hf hdisj hs b y

private theorem sphereOpens_cover :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ p : BoundaryManifold IR (cutCore f), ∃ b, p ∈ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro p
  obtain ⟨b, y, h⟩ := nativeCuttingSphereMap_cover I hdim hδ f hf hdisj hs p
  exact ⟨b, y, h⟩

variable {L : ℝ} (hL : 0 < L) (oE : (ι × Bool) → Orientation ℝ E3 (Fin 3))
private def sphereComponentOrientation (b : ι × Bool) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    SmoothOrientation (𝓡 2) (nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact pushThroughDiffeo (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)
    (negSmoothOrientation (𝓡 2) (radialSphereSmoothOrientation hL (oE b)))
private theorem sphereComponentOrientation_compatible :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ (b c : ι × Bool) (p : BoundaryManifold IR (cutCore f))
      (hb : p ∈ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b) (hc : p ∈ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs c),
      (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE b).val ⟨p, hb⟩ =
        (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE c).val ⟨p, hc⟩ := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro b c p hb hc
  by_cases h : b = c
  · subst c
    rfl
  · exact ((Set.disjoint_left.mp (nativeCuttingSphereMap_ranges_disjoint I hdim hδ f hf hdisj hs h)) hb hc).elim

def nativeCoreBoundarySmoothOrientation :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    SmoothOrientation (𝓡 2) (BoundaryManifold IR (cutCore f)) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact glueSmoothOrientations (𝓡 2) (nativeCuttingSphereOpens I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE) (sphereOpens_cover I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation_compatible I hdim hδ f hf hdisj hs hL oE)

theorem nativeCoreBoundarySmoothOrientation_apply (b : ι × Bool) (y : S2) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val
      (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b y).val =
        tangentOrientationEquiv ((nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b).mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
          (-(radialSphereSmoothOrientation hL (oE b)).val y) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (glueSmoothOrientations_apply (𝓡 2) (nativeCuttingSphereOpens I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation I hdim hδ f hf hdisj hs hL oE) (sphereOpens_cover I hdim hδ f hf hdisj hs)
    (sphereComponentOrientation_compatible I hdim hδ f hf hdisj hs hL oE) b (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b y)).trans
      (pushThroughDiffeo_apply (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)
        (negSmoothOrientation (𝓡 2) (radialSphereSmoothOrientation hL (oE b))) y)

def nativeCoreBoundaryAttachingDiffeomorph (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    BoundaryManifold (𝓡∂ 3) (Ball L) ≃ₘ⟮𝓡 2, 𝓡 2⟯ nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (closedBallBoundaryDiffeomorph hL).trans (nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b)

theorem nativeCoreBoundaryAttachingDiffeomorph_apply (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ x : BoundaryManifold (𝓡∂ 3) (Ball L),
      (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val.val =
        cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj
          ⟨b, closedBallBoundaryDiffeomorph hL x⟩ := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro x
  exact nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b (closedBallBoundaryDiffeomorph hL x)

theorem nativeCoreBoundaryAttachingDiffeomorph_coherence (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ x : BoundaryManifold (𝓡∂ 3) (Ball L),
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x.val⟩ =
        finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val.val := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro x
  have hx : radialCapBoundary hL (closedBallBoundaryDiffeomorph hL x) = x.val := by
    apply Subtype.ext
    change L • (L⁻¹ • x.val.val) = x.val.val
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  rw [nativeCoreBoundaryAttachingDiffeomorph_apply]
  have h := finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj
    ⟨b, closedBallBoundaryDiffeomorph hL x⟩
  change finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
    ⟨b, radialCapBoundary hL (closedBallBoundaryDiffeomorph hL x)⟩ = _ at h
  rw [hx] at h
  exact h

theorem nativeCoreBoundaryAttachingDiffeomorph_reverses_orientation (b : ι × Bool) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    ∀ x : BoundaryManifold (𝓡∂ 3) (Ball L),
      tangentOrientationEquiv ((nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b).mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        ((closedBallBoundarySmoothOrientation hL (oE b)).val x) =
          -(nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val
            (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  dsimp only
  intro x
  let d := closedBallBoundaryDiffeomorph hL
  let β := nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b
  let φ := nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b
  let A : E2 ≃L[ℝ] E2 := d.mfderivToContinuousLinearEquiv (by simp) x
  let B : E2 ≃L[ℝ] E2 := β.mfderivToContinuousLinearEquiv (by simp) (d x)
  let C : E2 ≃L[ℝ] E2 := φ.mfderivToContinuousLinearEquiv (by simp) x
  have he : C = A.trans B := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun D : E2 →L[ℝ] E2 => D v)
      (mfderiv_comp x (β.contMDiff.mdifferentiableAt (by simp)) (d.contMDiff.mdifferentiableAt (by simp)))
  let oB := (closedBallBoundarySmoothOrientation hL (oE b)).val x
  let oS := (radialSphereSmoothOrientation hL (oE b)).val (d x)
  have hA : tangentOrientationEquiv A.toLinearEquiv oB = oS :=
    closedBallBoundarySmoothOrientation_normalization hL (oE b) x
  have hN : (nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (φ x).val =
      tangentOrientationEquiv B.toLinearEquiv (-oS) :=
    nativeCoreBoundarySmoothOrientation_apply I hdim hδ f hf hdisj hs hL oE b (d x)
  change tangentOrientationEquiv C.toLinearEquiv oB = _
  calc
    tangentOrientationEquiv C.toLinearEquiv oB =
        tangentOrientationEquiv B.toLinearEquiv (tangentOrientationEquiv A.toLinearEquiv oB) := by
      rw [he]
      exact tangentOrientationEquiv_trans A.toLinearEquiv B.toLinearEquiv oB
    _ = tangentOrientationEquiv B.toLinearEquiv oS := congrArg (tangentOrientationEquiv B.toLinearEquiv) hA
    _ = -(nativeCoreBoundarySmoothOrientation I hdim hδ f hf hdisj hs hL oE).val (φ x).val := by
      have hn := congrArg (fun q : Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) => -q) hN
      have hm := congrArg (fun q : Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) => -q)
        (tangentOrientationEquiv_neg B.toLinearEquiv oS)
      exact (hn.trans (hm.trans (neg_neg (tangentOrientationEquiv B.toLinearEquiv oS)))).symm
end DifferentialGeometry.Topology.ThreeManifold.Surgery
