import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingCollarOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RadialAnnulusOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothOverlap

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

include hdim hs in
theorem cuttingCollarAmbient_mfderiv_bijective (b : ι × Bool)
    (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    Bijective (mfderiv IR I
      (Subtype.val ∘ cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) q) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact bijective_mfderiv_comp IR IR I
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) (Subtype.val : cutCore f → M)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
    (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).contMDiff
    (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b)
    (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) q

theorem cuttingCollarSmoothOrientation_ambient_apply (b : ι × Bool) (o : SmoothOrientation I M)
    (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q =
      (pullbackSmoothOrientation IR I
        (Subtype.val ∘ cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
        (cuttingCollarAmbient_contMDiff I hδ f (fun i => (hf i).injective) hdisj (fun i => (hs i).contMDiff) b)
        (cuttingCollarAmbient_mfderiv_bijective I hdim hδ f hf hdisj hs b) o).val q := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact (pullbackSmoothOrientation_comp_apply IR IR I
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) (Subtype.val : cutCore f → M)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
    (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).contMDiff
    (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b)
    (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs)
    (cuttingCollarAmbient_mfderiv_bijective I hdim hδ f hf hdisj hs b) o q).symm

include hs in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [Finite ι] in
theorem cuttingAnnulusAmbient_mfderiv_bijective {L : ℝ} (hL : 0 < L) (b : ι × Bool)
    (x : cuttingAnnulus L (precision b.1)) :
    Bijective (mfderiv (𝓡 3) I
      (f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2) x) :=
  ((finiteCapAnnulusAmbient_isLocalDiffeomorph (I := I) hL hδ f hs b x).mfderivToContinuousLinearEquiv (by simp)).bijective

theorem exists_radialOrientation_matching_collar_and_annulus {L : ℝ} (hL : 0 < L)
    (b : ι × Bool) (o : SmoothOrientation I M) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    ∃ oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      (oE = (Module.finBasis ℝ E3).orientation ∨ oE = -(Module.finBasis ℝ E3).orientation) ∧
      (∀ q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
        (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q =
          (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) ∧
      ∀ x : cuttingAnnulus L (precision b.1),
        tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) I
          (f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2)
          (cuttingAnnulusAmbient_mfderiv_bijective I hδ f hs hL b) x).toLinearEquiv oE =
            o.val (f b.1 (cuttingAnnulusCylinderMap hL (hδ b.1) b.2 x)) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  obtain ⟨oE, hsign, hmatch⟩ := exists_radialOrientation_matching_cuttingCollar I hdim hδ f hf hdisj hs hL b o
  refine ⟨oE, hsign, hmatch, ?_⟩
  intro x
  let a := cuttingAnnulusCollar (δ := precision b.1) hL
  let A := (Subtype.val : cutCore f → M) ∘ cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
  let F := f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2
  have ha := cuttingAnnulusCollar_contMDiff hL (hδ b.1)
  have hba := cuttingAnnulusCollar_mfderiv_bijective hL (hδ b.1)
  have hA := cuttingCollarAmbient_contMDiff I hδ f (fun i => (hf i).injective) hdisj (fun i => (hs i).contMDiff) b
  have hbA := cuttingCollarAmbient_mfderiv_bijective I hdim hδ f hf hdisj hs b
  have hF := (finiteCapAnnulusAmbient_isLocalDiffeomorph (I := I) hL hδ f hs b).contMDiff
  have hbF := cuttingAnnulusAmbient_mfderiv_bijective I hδ f hs hL b
  let OCollar := cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o
  let ORadial := radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE
  have hcomp : (pullbackSmoothOrientation (𝓡 3) I F hF hbF o).val x =
      (pullbackSmoothOrientation (𝓡 3) IR a ha hba (pullbackSmoothOrientation IR I A hA hbA o)).val x :=
    pullbackSmoothOrientation_comp_apply (𝓡 3) IR I a A ha hA hba hbA hbF o x
  have hc : (pullbackSmoothOrientation (𝓡 3) IR a ha hba (pullbackSmoothOrientation IR I A hA hbA o)).val x =
      (pullbackSmoothOrientation (𝓡 3) IR a ha hba OCollar).val x :=
    congrArg (tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) IR a hba x).symm.toLinearEquiv)
      (cuttingCollarSmoothOrientation_ambient_apply I hdim hδ f hf hdisj hs b o (a x)).symm
  have hr : (pullbackSmoothOrientation (𝓡 3) IR a ha hba ORadial).val x =
      (pullbackSmoothOrientation (𝓡 3) IR a ha hba OCollar).val x :=
    congrArg (tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) IR a hba x).symm.toLinearEquiv) (hmatch (a x))
  have he : (pullbackSmoothOrientation (𝓡 3) I F hF hbF o).val x = oE :=
    hcomp.trans (hc.trans (hr.symm.trans
      (cuttingAnnulusCollar_pullback_radialOrientation hL (hδ b.1) oE x)))
  rw [← he]
  exact pullbackSmoothOrientation_pushforward (𝓡 3) I F hF hbF o x
end DifferentialGeometry.Topology.ThreeManifold.Surgery
