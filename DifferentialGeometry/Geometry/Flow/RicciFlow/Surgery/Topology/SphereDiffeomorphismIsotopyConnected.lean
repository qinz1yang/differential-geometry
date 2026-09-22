import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BoundaryAttachmentIsotopy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Reconstruction

set_option autoImplicit false

noncomputable section

open Set Metric Manifold Module
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem sphereDiffeomorphIsotopicToIdentity_of_degree_one
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (h : sphereDiffeomorphDegree f = 1) :
    DifferentialGeometry.Topology.SphereDiffeomorphIsotopicToIdentity f :=
  (sphereDiffeomorphDegree_eq_one_iff_isotopy f).mp h

theorem sphereDiffeomorphDegree_eq_one_of_isotopicToIdentity
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (h : DifferentialGeometry.Topology.SphereDiffeomorphIsotopicToIdentity f) :
    sphereDiffeomorphDegree f = 1 := by
  obtain ⟨J, hJ, -, hJ0, hJ1⟩ := h
  let v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let D : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ :=
    fun p => J (1 - p)
  have hD : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => D q.1 q.2) :=
    hJ.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd)
  have hD0 : D 0 = Diffeomorph.refl (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ := by
    simpa [D] using hJ1
  have hp := det_fderiv_sphereRadialExtension_pos_of_isotopy D hD hD0 1
    (ne_zero_of_mem_unit_sphere v)
  rw [sphereDiffeomorphDegree_eq_one_iff f v]
  simpa only [D, sub_self, hJ0] using hp

theorem smaleMunkresSphereIsotopy_of_degree_one
    (h : ∀ f : Diffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by norm_num))
        (DifferentialGeometry.sphereOrientation 2 (by norm_num)) →
      sphereDiffeomorphDegree f = 1) :
    DifferentialGeometry.Topology.SmaleMunkresSphereIsotopy :=
  fun f hf => sphereDiffeomorphIsotopicToIdentity_of_degree_one f (h f hf)

theorem sphereDiffeomorphDegree_eq_one_of_smaleMunkres
    (h : DifferentialGeometry.Topology.SmaleMunkresSphereIsotopy)
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hf : f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by norm_num))
      (DifferentialGeometry.sphereOrientation 2 (by norm_num))) :
    sphereDiffeomorphDegree f = 1 :=
  sphereDiffeomorphDegree_eq_one_of_isotopicToIdentity f (h f hf)

theorem smaleMunkresSphereIsotopy_iff_degree_one :
    DifferentialGeometry.Topology.SmaleMunkresSphereIsotopy ↔
      ∀ f : Diffeomorph (𝓡 2) (𝓡 2)
          (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
        f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by norm_num))
          (DifferentialGeometry.sphereOrientation 2 (by norm_num)) →
        sphereDiffeomorphDegree f = 1 :=
  ⟨sphereDiffeomorphDegree_eq_one_of_smaleMunkres, smaleMunkresSphereIsotopy_of_degree_one⟩

theorem smaleMunkresSphereIsotopy_holds :
    DifferentialGeometry.Topology.SmaleMunkresSphereIsotopy :=
  smaleMunkresSphereIsotopy_of_degree_one sphereDiffeomorphDegree_eq_one_of_preservesOrientation

theorem sphereAntipodalDiffeomorph_degree_eq_neg_one :
    sphereDiffeomorphDegree
      (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) = -1 := by
  have hfun : sphereRadialExtension
      (⇑(sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) =
      fun z : E3 => -z := by
    funext z
    by_cases hz : z = 0
    · simp [sphereRadialExtension, hz]
    · rw [sphereRadialExtension_of_ne_zero _ hz]
      rw [show (⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩ : S2) =
          ConnectedSumQuotient.unitVecFun z from
        Subtype.ext (by rw [ConnectedSumQuotient.coe_unitVecFun_eq hz])]
      rw [show ((sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
          (ConnectedSumQuotient.unitVecFun z) : S2) : E3) =
          -((ConnectedSumQuotient.unitVecFun z : S2) : E3) from rfl]
      rw [show ((ConnectedSumQuotient.unitVecFun z : S2) : E3) = (‖z‖)⁻¹ • z from
        ConnectedSumQuotient.coe_unitVecFun_eq hz]
      rw [smul_neg, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hdet (w : E3) : (fderiv ℝ (fun z : E3 => -z) w).toLinearMap.det = -1 := by
    rw [show fderiv ℝ (fun z : E3 => -z) w = -ContinuousLinearMap.id ℝ E3 from
      (hasFDerivAt_id w).neg.fderiv]
    rw [show (-(ContinuousLinearMap.id ℝ E3)).toLinearMap =
      (-1 : ℝ) • (LinearMap.id : E3 →ₗ[ℝ] E3) from by
        ext w
        simp]
    rw [LinearMap.det_smul, LinearMap.det_id]
    rw [show Module.finrank ℝ E3 = 3 from by simp]
    norm_num
  let v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  rw [sphereDiffeomorphDegree_eq_sign
    (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) v]
  rw [show (fderiv ℝ (sphereRadialExtension
      (⇑(sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det = -1 from by
    rw [hfun]
    exact hdet _]
  norm_num

theorem sphereAntipodalDiffeomorph_not_isotopicToIdentity :
    ¬ DifferentialGeometry.Topology.SphereDiffeomorphIsotopicToIdentity
      (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) := by
  intro h
  have hdeg := sphereDiffeomorphDegree_eq_one_of_isotopicToIdentity _ h
  rw [sphereAntipodalDiffeomorph_degree_eq_neg_one] at hdeg
  norm_num at hdeg

theorem exists_sphereDiffeomorph_not_isotopicToIdentity :
    ∃ f : Diffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ¬ DifferentialGeometry.Topology.SphereDiffeomorphIsotopicToIdentity f :=
  ⟨sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2),
    sphereAntipodalDiffeomorph_not_isotopicToIdentity⟩

theorem sphereAntipodalDiffeomorph_not_preservesOrientation :
    ¬ (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).preservesOrientation
      (DifferentialGeometry.sphereOrientation 2 (by norm_num))
      (DifferentialGeometry.sphereOrientation 2 (by norm_num)) := by
  intro h
  have h2 := sphereAntipodalDiffeomorph_preservesOrientation_opposite
  let p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hp := h p
  have hp2 := h2 p
  rw [hp, DifferentialGeometry.ManifoldOrientation.opposite_orientation] at hp2
  exact Module.Ray.ne_neg_self
    ((DifferentialGeometry.sphereOrientation 2 (by norm_num)).orientation
      (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2) p)) hp2

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology

theorem boundaryAttachmentIsotopic_holds (a a' : BoundaryAttachment) :
    BoundaryAttachmentIsotopic a a' :=
  boundaryAttachmentIsotopic_of_smaleMunkres
    DifferentialGeometry.Topology.Manifold.smaleMunkresSphereIsotopy_holds a a'

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem sphereDiffeomorphismIsotopyConnected_of_smaleMunkres
    (h : DifferentialGeometry.Topology.SmaleMunkresSphereIsotopy) :
    sphereDiffeomorphismIsotopyConnected := by
  intro f hf
  obtain ⟨J, hJ, -, hJ0, hJ1⟩ := h f hf
  have hcont : Continuous fun p : Set.Icc (0 : ℝ) 1 × Sphere 2 => J (p.1 : ℝ) p.2 :=
    hJ.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  refine ⟨⟨fun p => J (p.1 : ℝ) p.2, hcont⟩, ?_, ?_, ?_⟩
  · intro y
    change J (0 : ℝ) y = f y
    rw [hJ0]
  · intro y
    change J (1 : ℝ) y = y
    rw [hJ1]
    rfl
  · intro t
    exact ⟨J (t.1 : ℝ), fun y => rfl⟩

theorem sphereDiffeomorphismIsotopyConnected_of_degree_one
    (h : ∀ f : Diffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by norm_num))
        (DifferentialGeometry.sphereOrientation 2 (by norm_num)) →
      DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree f = 1) :
    sphereDiffeomorphismIsotopyConnected :=
  sphereDiffeomorphismIsotopyConnected_of_smaleMunkres
    (DifferentialGeometry.Topology.Manifold.smaleMunkresSphereIsotopy_of_degree_one h)

theorem sphereDiffeomorphismIsotopyConnected_holds :
    sphereDiffeomorphismIsotopyConnected :=
  sphereDiffeomorphismIsotopyConnected_of_smaleMunkres
    DifferentialGeometry.Topology.Manifold.smaleMunkresSphereIsotopy_holds

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
