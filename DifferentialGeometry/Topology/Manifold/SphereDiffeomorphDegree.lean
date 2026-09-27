import DifferentialGeometry.Topology.Manifold.SphereOrientationIsotopy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientation

noncomputable section
open Set Metric Manifold Module
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Topology.Manifold

variable (f : Diffeomorph (𝓡 2) (𝓡 2)
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)

private abbrev uniqueSphereFiber (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Unique {x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 // f x = y} where
  default := ⟨f.symm y, f.apply_symm_apply y⟩
  uniq := by
    intro x
    apply Subtype.ext
    exact f.injective (x.2.trans (f.apply_symm_apply y).symm)

def sphereDiffeomorphPreimageCount (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : ℤ := by
  classical
  let := uniqueSphereFiber f y
  exact ∑ x : {x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 // f x = y},
    if 0 < (fderiv ℝ (sphereRadialExtension f) (x.1 : EuclideanSpace ℝ (Fin 3))).toLinearMap.det
    then 1 else
    if (fderiv ℝ (sphereRadialExtension f) (x.1 : EuclideanSpace ℝ (Fin 3))).toLinearMap.det < 0
    then -1 else 0

theorem sphereDiffeomorphPreimageCount_eq
    (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphPreimageCount f y =
      if 0 < (fderiv ℝ (sphereRadialExtension f)
        (f.symm y : EuclideanSpace ℝ (Fin 3))).toLinearMap.det then 1 else -1 := by
  classical
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let := uniqueSphereFiber f y
  have hnz := det_fderiv_sphereRadialExtension_ne_zero f (ne_zero_of_mem_unit_sphere (f.symm y))
  simp only [sphereDiffeomorphPreimageCount, Fintype.sum_unique]
  change (if 0 < (fderiv ℝ (sphereRadialExtension f)
    (f.symm y : EuclideanSpace ℝ (Fin 3))).toLinearMap.det then (1 : ℤ) else
    if (fderiv ℝ (sphereRadialExtension f)
    (f.symm y : EuclideanSpace ℝ (Fin 3))).toLinearMap.det < 0 then -1 else 0) = _
  split_ifs with hp hn
  · rfl
  · rfl
  · exact False.elim (hnz (le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)))

theorem sphereDiffeomorphPreimageCount_independent
    (y z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphPreimageCount f y = sphereDiffeomorphPreimageCount f z := by
  classical
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hsign := det_fderiv_sphereRadialExtension_pos_iff hrank f
    (ne_zero_of_mem_unit_sphere (f.symm y)) (ne_zero_of_mem_unit_sphere (f.symm z))
  simp only [sphereDiffeomorphPreimageCount_eq, hsign]

def sphereDiffeomorphDegree : ℤ :=
  sphereDiffeomorphPreimageCount f ⟨EuclideanSpace.single 0 1, by simp⟩

theorem sphereDiffeomorphDegree_eq_sign
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphDegree f =
      if 0 < (fderiv ℝ (sphereRadialExtension f)
        (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det then 1 else -1 := by
  classical
  unfold sphereDiffeomorphDegree
  rw [sphereDiffeomorphPreimageCount_independent f _ (f v), sphereDiffeomorphPreimageCount_eq,
    f.symm_apply_apply]

theorem sphereDiffeomorphDegree_eq_one_iff
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphDegree f = 1 ↔
      0 < (fderiv ℝ (sphereRadialExtension f) (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det := by
  classical
  rw [sphereDiffeomorphDegree_eq_sign f v]
  split_ifs <;> simp_all

theorem sphereDiffeomorphDegree_eq_one_iff_isotopy :
    sphereDiffeomorphDegree f = 1 ↔
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞ := by
  let v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact (sphereDiffeomorphDegree_eq_one_iff f v).trans
    (sphere_isotopy_iff_positive_radial_derivative f v).symm

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

end DifferentialGeometry.Topology.Manifold
