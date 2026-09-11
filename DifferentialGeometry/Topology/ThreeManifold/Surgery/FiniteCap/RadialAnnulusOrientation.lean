import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingAnnulusCoordinates
import DifferentialGeometry.Topology.Manifold.HalfClosedIntervalSmoothMaps
import DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem cuttingAnnulusCollar_contMDiff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    ContMDiff (𝓡 3) IR ∞ (cuttingAnnulusCollar (δ := δ) hL) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : cuttingAnnulus L δ => ‖x.val‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := cuttingAnnulus L δ)).mpr
    exact (contDiffAt_norm ℝ (norm_pos_iff.mp (hL.trans x.property.1))).contMDiffAt
  have hang : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1) := by
    have hv : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1.val) := by
      simp_rw [cuttingAnnulusCollar_direction]
      exact (hn.inv₀ (fun x => (hL.trans x.property.1).ne')).smul (contMDiff_subtype_val (U := cuttingAnnulus L δ))
    exact ContMDiff.codRestrict_sphere hv (fun x => (cuttingAnnulusCollar hL x).1.property)
  have ht : ContMDiff (𝓡 3) (𝓡∂ 1) ∞
      (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).2) :=
    contMDiff_halfClosedInterval_of_val (𝓡 3) (cuttingCollarWidth_pos hδ) _
      (by simpa only [cuttingAnnulusCollar_radius] using hn.sub contMDiff_const)
  exact hang.prodMk ht

theorem cuttingAnnulusCollar_mfderiv_bijective {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (x : cuttingAnnulus L δ) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    Bijective (mfderiv (𝓡 3) IR (cuttingAnnulusCollar hL) x) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let a := cuttingAnnulusCollar (δ := δ) hL
  let ρ := radialCollarOrientationMap L (cuttingCollarWidth δ)
  have hρ := (radialCollarOrientationMap_isSmoothEmbedding hL (cuttingCollarWidth_pos hδ)).contMDiff
  have ha := cuttingAnnulusCollar_contMDiff hL hδ
  have he : ρ ∘ a = (Subtype.val : cuttingAnnulus L δ → E3) :=
    funext (cuttingAnnulusCollar_radial hL)
  have hc := mfderiv_comp (f := a) (g := ρ) x (hρ.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  rw [he, DifferentialGeometry.mfderiv_subtype_val] at hc
  have hb : Bijective ((mfderiv IR (𝓡 3) ρ (a x)) ∘ (mfderiv (𝓡 3) IR a x)) := by
    change Bijective ((mfderiv IR (𝓡 3) ρ (a x)).comp (mfderiv (𝓡 3) IR a x))
    rw [← hc]
    exact Function.bijective_id
  exact hb.of_comp_left (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos hδ) (a x)).injective

theorem cuttingAnnulusCollar_pullback_radialOrientation {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (x : cuttingAnnulus L δ) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
    (pullbackSmoothOrientation (𝓡 3) IR (cuttingAnnulusCollar hL)
      (cuttingAnnulusCollar_contMDiff hL hδ) (cuttingAnnulusCollar_mfderiv_bijective hL hδ)
      (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos hδ) o)).val x = o := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
  let a := cuttingAnnulusCollar (δ := δ) hL
  let ρ := radialCollarOrientationMap L (cuttingCollarWidth δ)
  have hρ := (radialCollarOrientationMap_isSmoothEmbedding hL (cuttingCollarWidth_pos hδ)).contMDiff
  have ha := cuttingAnnulusCollar_contMDiff hL hδ
  have hba := cuttingAnnulusCollar_mfderiv_bijective hL hδ
  have hbρ := radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos hδ)
  have hb := bijective_mfderiv_comp (𝓡 3) IR (𝓡 3) a ρ ha hρ hba hbρ
  have hcomp := pullbackSmoothOrientation_comp_apply (𝓡 3) IR (𝓡 3)
    a ρ ha hρ hba hbρ hb (euclideanSmoothOrientation E3 o) x
  have he : ρ ∘ a = (Subtype.val : cuttingAnnulus L δ → E3) :=
    funext (cuttingAnnulusCollar_radial hL)
  have hd : differentialEquivOfBijective (𝓡 3) (𝓡 3) (ρ ∘ a) hb x =
      ContinuousLinearEquiv.refl ℝ E3 := by
    apply ContinuousLinearEquiv.ext
    funext v
    change mfderiv (𝓡 3) (𝓡 3) (ρ ∘ a) x v = v
    rw [he, DifferentialGeometry.mfderiv_subtype_val]
    rfl
  refine hcomp.symm.trans ?_
  change tangentOrientationEquiv
    (differentialEquivOfBijective (𝓡 3) (𝓡 3) (ρ ∘ a) hb x).symm.toLinearEquiv o = o
  rw [hd]
  exact tangentOrientationEquiv_refl o
end DifferentialGeometry.Topology.ThreeManifold.Surgery
