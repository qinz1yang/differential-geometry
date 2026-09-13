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

private noncomputable def e3Basis : Basis (Fin 3) ℝ E3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private theorem e3Basis_det_apply (v : Fin 3 → E3) :
    e3Basis.det v = Matrix.det (fun i j : Fin 3 => (v j) i) :=
  Module.Basis.det_apply (e := e3Basis) v

private theorem hasFDerivAt_norm_e3 {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun v : E3 => ‖v‖) (innerSL ℝ ((‖x‖)⁻¹ • x)) x := by
  have hsq : HasFDerivAt (fun v : E3 => ‖v‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖x‖ ^ 2))) (‖x‖ ^ 2) :=
    Real.hasDerivAt_sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hcomp := hsqrt.hasFDerivAt.comp x hsq
  have hfun : (Real.sqrt ∘ fun v : E3 => ‖v‖ ^ 2) = fun v : E3 => ‖v‖ := by
    funext v
    exact Real.sqrt_sq (norm_nonneg v)
  rw [hfun] at hcomp
  have hf' : ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖x‖ ^ 2))) ∘SL
      (2 • innerSL ℝ x) = innerSL ℝ ((‖x‖)⁻¹ • x) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      innerSL_apply_apply, real_inner_smul_left, smul_apply]
    rw [Real.sqrt_sq (norm_nonneg x), nsmul_eq_mul, smul_eq_mul]
    field_simp
    ring
  rw [hf'] at hcomp
  exact hcomp

private theorem hasFDerivAt_unitVecPush
    (f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun z : E3 => (f (ConnectedSumQuotient.unitVecFun z) : E3))
      (fderiv ℝ (fun z : E3 => (f (ConnectedSumQuotient.unitVecFun z) : E3)) x) x :=
  ConnectedSumQuotient.hasFDerivAt_pushCoe f hx

private theorem fderiv_unitVecPush_self
    (f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) {x : E3} (hx : x ≠ 0) :
    fderiv ℝ (fun z : E3 => (f (ConnectedSumQuotient.unitVecFun z) : E3)) x
      ((‖x‖)⁻¹ • x) = 0 :=
  ConnectedSumQuotient.fderiv_pushCoe_self f hx

private theorem fderiv_unitVecPush_dIncl
    (f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) {x : E3} (hx : x ≠ 0)
    (b : TangentSpace (𝓡 2) (ConnectedSumQuotient.unitVecFun x)) :
    fderiv ℝ (fun z : E3 => (f (ConnectedSumQuotient.unitVecFun z) : E3)) x
        (Geometry.dIncl (ConnectedSumQuotient.unitVecFun x) b) =
      (‖x‖)⁻¹ • Geometry.dIncl (f (ConnectedSumQuotient.unitVecFun x))
        (mfderiv (𝓡 2) (𝓡 2) f (ConnectedSumQuotient.unitVecFun x) b) :=
  ConnectedSumQuotient.fderiv_pushCoe_dIncl f hx b

private theorem hasFDerivAt_sphereRadialExtension
    (f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (sphereRadialExtension ⇑f)
      (‖x‖ • fderiv ℝ (fun z : E3 => (f (ConnectedSumQuotient.unitVecFun z) : E3)) x
        + (innerSL ℝ ((‖x‖)⁻¹ • x)).smulRight
            (f (ConnectedSumQuotient.unitVecFun x) : E3)) x := by
  have h1 : HasFDerivAt (fun v : E3 => ‖v‖) (innerSL ℝ ((‖x‖)⁻¹ • x)) x :=
    hasFDerivAt_norm_e3 hx
  have h2 := hasFDerivAt_unitVecPush f hx
  have h := h1.smul h2
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
  rw [sphereRadialExtension_of_ne_zero _ hz]
  have hsub : (⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩ : S2) =
      ConnectedSumQuotient.unitVecFun z :=
    Subtype.ext (by rw [ConnectedSumQuotient.coe_unitVecFun_eq hz])
  rw [hsub]
  rfl

private theorem det_fderiv_sphereRadialExtension_pos_of_preservesOrientation
    (f : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞)
    (hf : f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by norm_num))
      (DifferentialGeometry.sphereOrientation 2 (by norm_num)))
    {x : E3} (hx : x ≠ 0) :
    0 < (fderiv ℝ (sphereRadialExtension ⇑f) x).toLinearMap.det := by
  let L : E3 →L[ℝ] E3 :=
    ‖x‖ • fderiv ℝ (fun z : E3 => (f (ConnectedSumQuotient.unitVecFun z) : E3)) x
      + (innerSL ℝ ((‖x‖)⁻¹ • x)).smulRight
          (f (ConnectedSumQuotient.unitVecFun x) : E3)
  have hL : HasFDerivAt (sphereRadialExtension ⇑f) L x := hasFDerivAt_sphereRadialExtension f hx
  rw [hL.fderiv]
  let o : ManifoldOrientation (𝓡 2) S2 2 := DifferentialGeometry.sphereOrientation 2 (by norm_num)
  have hcard : Fintype.card (Fin 2) =
      Module.finrank ℝ (TangentSpace (𝓡 2) (ConnectedSumQuotient.unitVecFun x)) := by
    change Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
    simp
  let b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (ConnectedSumQuotient.unitVecFun x)) :=
    Orientation.someBasis (o.orientation (ConnectedSumQuotient.unitVecFun x)) hcard
  have hb : b.orientation = o.orientation (ConnectedSumQuotient.unitVecFun x) :=
    Orientation.someBasis_orientation _ _
  have hposX : 0 < DifferentialGeometry.sphereOutwardDeterminant 2
      (ConnectedSumQuotient.unitVecFun x) b :=
    (DifferentialGeometry.sphereOrientation_characterization 2 (by norm_num)
      (ConnectedSumQuotient.unitVecFun x) b).mp hb
  let A : TangentSpace (𝓡 2) (ConnectedSumQuotient.unitVecFun x) ≃ₗ[ℝ]
      TangentSpace (𝓡 2) (f (ConnectedSumQuotient.unitVecFun x)) :=
    (f.mfderivToContinuousLinearEquiv (by simp) (ConnectedSumQuotient.unitVecFun x)).toLinearEquiv
  let c : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (f (ConnectedSumQuotient.unitVecFun x))) :=
    b.map A
  have hc : ∀ k : Fin 2, c k = mfderiv (𝓡 2) (𝓡 2) f
      (ConnectedSumQuotient.unitVecFun x) (b k) := by
    intro k
    rw [show c k = A (b k) from Basis.map_apply b A k]
    exact congrArg (fun (M : TangentSpace (𝓡 2) (ConnectedSumQuotient.unitVecFun x) →L[ℝ]
      TangentSpace (𝓡 2) (f (ConnectedSumQuotient.unitVecFun x))) => M (b k))
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe f (by simp))
  have hmapc : Orientation.map (Fin 2) A (o.orientation (ConnectedSumQuotient.unitVecFun x)) =
      c.orientation := by
    rw [← hb]
    exact (Basis.orientation_map b A).symm
  have hposR : 0 < DifferentialGeometry.sphereOutwardDeterminant 2
      (f (ConnectedSumQuotient.unitVecFun x)) c :=
    (DifferentialGeometry.sphereOrientation_characterization 2 (by norm_num)
      (f (ConnectedSumQuotient.unitVecFun x)) c).mp
      (hmapc.symm.trans (hf (ConnectedSumQuotient.unitVecFun x)))
  let xframe : Fin 3 → E3 := fun j => Fin.cases (ConnectedSumQuotient.unitVecFun x : E3)
    (fun k => Geometry.dIncl (ConnectedSumQuotient.unitVecFun x) (b k)) j
  let rframe : Fin 3 → E3 := fun j =>
    Fin.cases (f (ConnectedSumQuotient.unitVecFun x) : E3)
      (fun k => Geometry.dIncl (f (ConnectedSumQuotient.unitVecFun x)) (c k)) j
  have hframe : ∀ j : Fin 3, L (xframe j) = rframe j := by
    intro j
    refine Fin.cases ?_ ?_ j
    · dsimp only [xframe, rframe, L, Fin.cases_zero]
      rw [show ((ConnectedSumQuotient.unitVecFun x : S2) : E3) = (‖x‖)⁻¹ • x from
        ConnectedSumQuotient.coe_unitVecFun_eq hx]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply]
      rw [fderiv_unitVecPush_self f hx, smul_zero, zero_add]
      have hinner : ⟪(‖x‖)⁻¹ • x, (‖x‖)⁻¹ • x⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_mul_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), mul_one]
      rw [hinner, one_smul]
    · intro k
      dsimp only [xframe, rframe, L, Fin.cases_succ]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply]
      rw [fderiv_unitVecPush_dIncl f hx (b k), ← hc k]
      have hinner : ⟪(‖x‖)⁻¹ • x,
          Geometry.dIncl (ConnectedSumQuotient.unitVecFun x) (b k)⟫_ℝ = 0 := by
        rw [← ConnectedSumQuotient.coe_unitVecFun_eq hx]
        exact Geometry.dIncl_orth (ConnectedSumQuotient.unitVecFun x) (b k)
      rw [hinner, zero_smul, add_zero]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hxdet : e3Basis.det xframe = DifferentialGeometry.sphereOutwardDeterminant 2
      (ConnectedSumQuotient.unitVecFun x) b := by
    rw [e3Basis_det_apply]
    rfl
  have hrdet : e3Basis.det rframe = DifferentialGeometry.sphereOutwardDeterminant 2
      (f (ConnectedSumQuotient.unitVecFun x)) c := by
    rw [e3Basis_det_apply]
    rfl
  have hframeFun : (L.toLinearMap ∘ xframe) = rframe := funext fun j => hframe j
  have hkey : L.toLinearMap.det * e3Basis.det xframe = e3Basis.det rframe := by
    rw [← Module.Basis.det_comp e3Basis L.toLinearMap xframe, hframeFun]
  have hX : 0 < e3Basis.det xframe := by rw [hxdet]; exact hposX
  have hR : 0 < e3Basis.det rframe := by rw [hrdet]; exact hposR
  exact (mul_pos_iff_of_pos_right hX).mp (by rw [hkey]; exact hR)

theorem sphereDiffeomorphDegree_eq_one_of_preservesOrientation
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hf : f.preservesOrientation (DifferentialGeometry.sphereOrientation 2 (by norm_num))
      (DifferentialGeometry.sphereOrientation 2 (by norm_num))) :
    sphereDiffeomorphDegree f = 1 := by
  let v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  rw [sphereDiffeomorphDegree_eq_one_iff f v]
  exact det_fderiv_sphereRadialExtension_pos_of_preservesOrientation f hf
    (ne_zero_of_mem_unit_sphere v)

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
