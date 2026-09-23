import DifferentialGeometry.Topology.Manifold.RoundCylinderOrientation
import DifferentialGeometry.Topology.Manifold.ClosedBallBoundaryOrientation
import DifferentialGeometry.Topology.Manifold.SphereOutwardFrameDictionary
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private def b3 : Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem normalFirstOrientation_radialSphereNormalFrame_one
    (z : S2) (b : Basis (Fin 2) ℝ E2) :
    normalFirstOrientation (radialSphereNormalFrame zero_lt_one z).toLinearEquiv b
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
        (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z := by
  let o := (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace (𝓡 2) z) := by
    change Fintype.card (Fin 2) = Module.finrank ℝ E2
    simp
  let c : Basis (Fin 2) ℝ E2 := o.someBasis hcard
  have hc : c.orientation = o := o.someBasis_orientation hcard
  have hpos : 0 < DifferentialGeometry.sphereOutwardDeterminant 2 z c :=
    (DifferentialGeometry.sphereOrientation_characterization 2 (by decide) z c).mp hc
  let F := normalFirstContraction (radialSphereNormalFrame zero_lt_one z).toLinearEquiv b3.det
  have hF : F c = DifferentialGeometry.sphereOutwardDeterminant 2 z c := by
    rw [DifferentialGeometry.sphereOutwardDeterminant_eq_basisDet_frame]
    dsimp only [F]
    rw [normalFirstContraction_apply]
    congr 1
    funext i
    cases i using Fin.cases with
    | zero =>
      change radialSphereNormalFrame zero_lt_one z (1, 0) = z.val
      rw [radialSphereNormalFrame_apply, one_smul, one_smul]
      have hz : dIncl (n := 2) z (0 : E2) = 0 :=
        (dIncl (n := 2) z).map_zero
      rw [hz, add_zero]
    | succ i =>
      change radialSphereNormalFrame zero_lt_one z (0, c i) =
        mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) z (c i)
      simp only [radialSphereNormalFrame_apply, zero_smul, one_smul, zero_add]
      rfl
  change normalFirstOrientation _ b (rayOfNeZero ℝ b3.det b3.det_ne_zero) = o
  rw [normalFirstOrientation_apply, ← hc]
  change rayOfNeZero ℝ F _ = rayOfNeZero ℝ c.det c.det_ne_zero
  apply (ray_eq_iff _ _).mpr
  rw [F.eq_smul_basis_det c]
  exact SameRay.sameRay_pos_smul_left c.det (hF ▸ hpos)

theorem exponentialPolarMap_mfderiv_apply (q : S2 × ℝ) (v : E2) (s : ℝ) :
    mfderiv IC (𝓡 3) exponentialPolarMap q (v, s) =
      Real.exp q.2 • (s • q.1.val + dIncl (n := 2) q.1 v) := by
  have hP := (euclideanPolarMap_smooth (E := E3) (n := 2)).mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0) (x := positiveCylinderReparametrization q)
  have hR := positiveCylinderReparametrization_contMDiff.mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0) (x := q)
  have hexp : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ Real.exp := Real.contDiff_exp.contMDiff
  change mfderiv IC (𝓡 3) (euclideanPolarMap ∘ positiveCylinderReparametrization) q (v, s) = _
  rw [mfderiv_comp q hP hR]
  change mfderiv IC (𝓡 3) euclideanPolarMap (positiveCylinderReparametrization q)
    (mfderiv IC IC positiveCylinderReparametrization q (v, s)) = _
  have hD : mfderiv IC IC positiveCylinderReparametrization q (v, s) =
      (v, s * Real.exp q.2) := by
    change mfderiv IC IC (Prod.map (id : S2 → S2) Real.exp) q (v, s) = _
    rw [mfderiv_prodMap mdifferentiableAt_id (hexp.mdifferentiableAt (by simp)), mfderiv_id,
      mfderiv_eq_fderiv, (Real.hasDerivAt_exp q.2).hasFDerivAt.fderiv]
    rfl
  rw [hD]
  have hp := euclideanPolarMap_mfderiv (n := 2) (positiveCylinderReparametrization q)
    (v, s * Real.exp q.2)
  change mfderiv IC (𝓡 3) euclideanPolarMap (positiveCylinderReparametrization q)
      (v, s * Real.exp q.2) = _ at hp
  rw [hp]
  dsimp only [positiveCylinderReparametrization, Prod.map]
  rw [smul_add, smul_smul, mul_comm s]
  rfl

theorem normalFirstOrientation_eq_of_pos_smul
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e e' : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (r : ℝ) (hr : 0 < r) (he : ∀ v, e' v = r • e v)
    (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation e' b o = normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h form hform =>
    rw [normalFirstOrientation_apply, normalFirstOrientation_apply]
    apply (ray_eq_iff _ _).mpr
    have hscale : normalFirstContraction e' form = (r ^ 3) • normalFirstContraction e form := by
      ext v
      rw [AlternatingMap.smul_apply, normalFirstContraction_apply, normalFirstContraction_apply]
      change form (Matrix.vecCons (e' (1, 0)) (fun i => e' (0, v i))) =
        r ^ 3 • form (Matrix.vecCons (e (1, 0)) (fun i => e (0, v i)))
      simp_rw [he]
      have hv : Matrix.vecCons (r • e (1, 0)) (fun i => r • e (0, v i)) =
          fun i => r • Matrix.vecCons (e (1, 0)) (fun j => e (0, v j)) i := by
        funext i
        cases i using Fin.cases <;> rfl
      rw [hv, AlternatingMap.map_smul_univ]
      simp
    rw [hscale]
    exact SameRay.sameRay_pos_smul_left _ (pow_pos hr 3)

theorem normalFirstOrientation_roundCylinderSmoothOrientation
    (z : S2) (t : ℝ) (b : Basis (Fin 2) ℝ E2) :
    normalFirstOrientation (LinearEquiv.prodComm ℝ ℝ E2) b
      (Orientation.reindex ℝ (E2 × ℝ)
        (finCongr (by simp [Module.finrank_prod] : Module.finrank ℝ (E2 × ℝ) = 3))
        ((roundCylinderSmoothOrientation (Orientation.reindex ℝ E3
          (finCongr (by simp : 3 = Module.finrank ℝ E3))
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)).val (z, t))) =
      (DifferentialGeometry.sphereOrientation 2 (by decide)).orientation z := by
  let L := (differentialEquivOfBijective IC (𝓡 3) exponentialPolarMap
    exponentialPolarMap_mfderiv_bijective (z, t)).toLinearEquiv
  let oC := Orientation.reindex ℝ (E2 × ℝ)
    (finCongr (by simp [Module.finrank_prod] : Module.finrank ℝ (E2 × ℝ) = 3))
    ((roundCylinderSmoothOrientation (Orientation.reindex ℝ E3
      (finCongr (by simp : 3 = Module.finrank ℝ E3)) b3.orientation)).val (z, t))
  have hpush : Orientation.map (Fin 3) L oC = b3.orientation := by
    exact tangentOrientationEquiv_symm_reindex_map L
      (by simp [Module.finrank_prod]) (by simp) b3.orientation
  have hmap := normalFirstOrientation_map (LinearEquiv.prodComm ℝ ℝ E2) L b oC
  rw [hpush] at hmap
  change normalFirstOrientation (LinearEquiv.prodComm ℝ ℝ E2) b oC = _
  rw [← hmap]
  have hscale : ∀ v : ℝ × E2,
      ((LinearEquiv.prodComm ℝ ℝ E2).trans L) v =
        Real.exp t • (radialSphereNormalFrame zero_lt_one z) v := by
    intro v
    change mfderiv IC (𝓡 3) exponentialPolarMap (z, t) (v.2, v.1) = _
    rw [exponentialPolarMap_mfderiv_apply, radialSphereNormalFrame_apply, one_smul]
  rw [normalFirstOrientation_eq_of_pos_smul
    (radialSphereNormalFrame zero_lt_one z).toLinearEquiv
    ((LinearEquiv.prodComm ℝ ℝ E2).trans L) b (Real.exp t) (Real.exp_pos t) hscale]
  exact normalFirstOrientation_radialSphereNormalFrame_one z b

end DifferentialGeometry.Topology.Manifold
