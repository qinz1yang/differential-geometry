import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianMetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Horospherical

open Hyperbolic

local notation "P" => (TopologicalSpace.Opens.mk (Set.Ioi (0 : ℝ)) isOpen_Ioi)

private def positiveLogDiffeomorph (r : ℕ∞ω) : P ≃ₘ^r⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun x := Real.log x.val
  invFun t := ⟨Real.exp t, Real.exp_pos t⟩
  left_inv x := Subtype.ext (Real.exp_log x.property)
  right_inv := Real.log_exp
  contMDiff_toFun := fun x =>
    (Real.contDiffAt_log.mpr x.property.ne').contMDiffAt.comp x
      contMDiff_subtype_val.contMDiffAt
  contMDiff_invFun := by
    apply (Manifold.contMDiff_subtypeVal_comp_iff (n := r) P _).mp
    exact Real.contDiff_exp.contMDiff

def logCoordsDiffeomorph (m : ℕ) (r : ℕ∞ω := ∞) :
    HUpper (m + 1) ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))), (𝓘(ℝ, Horizontal m)).prod 𝓘(ℝ, ℝ)⟯ Horizontal m × ℝ :=
  (coordsDiffeomorph m r).trans
    ((Diffeomorph.refl (𝓘(ℝ, Horizontal m)) (Horizontal m) r).prodCongr (positiveLogDiffeomorph r))

@[simp] theorem logCoordsDiffeomorph_apply (m : ℕ) (r : ℕ∞ω) (x : HUpper (m + 1)) :
    logCoordsDiffeomorph m r x = (horizontal x, Real.log (height x)) := rfl

@[simp] theorem logCoordsDiffeomorph_symm_apply (m : ℕ) (r : ℕ∞ω) (x : Horizontal m × ℝ) :
    (logCoordsDiffeomorph m r).symm x = ofCoords x.1 (Real.exp x.2) (Real.exp_pos x.2) := rfl

end DifferentialGeometry.Horospherical

namespace DifferentialGeometry.Hyperboloid

open Horospherical

def horosphericalLogDiffeomorph (m : ℕ) (r : ℕ∞ω := ∞) :
    Hyperboloid (EuclideanSpace ℝ (Fin (m + 1)))
      ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))),
        𝓘(ℝ, Horizontal m × ℝ)⟯ Horizontal m × ℝ where
  toEquiv := ((hUpperDiffeomorph (m + 1) r).symm.trans (logCoordsDiffeomorph m r)).toEquiv
  contMDiff_toFun := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact ((hUpperDiffeomorph (m + 1) r).symm.trans (logCoordsDiffeomorph m r)).contMDiff
  contMDiff_invFun := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact ((hUpperDiffeomorph (m + 1) r).symm.trans (logCoordsDiffeomorph m r)).symm.contMDiff

@[simp] theorem horosphericalLogDiffeomorph_apply (m : ℕ) (r : ℕ∞ω)
    (x : Hyperboloid (EuclideanSpace ℝ (Fin (m + 1)))) :
    horosphericalLogDiffeomorph m r x =
      logCoordsDiffeomorph m r ((hUpperDiffeomorph (m + 1) r).symm x) := rfl

@[simp] theorem horosphericalLogDiffeomorph_symm_apply (m : ℕ) (r : ℕ∞ω)
    (p : Horizontal m × ℝ) :
    (horosphericalLogDiffeomorph m r).symm p =
      hUpperDiffeomorph (m + 1) r (ofCoords p.1 (Real.exp p.2) (Real.exp_pos p.2)) := rfl

private theorem horosphericalLogDiffeomorph_symm_time (m : ℕ) (p : Horizontal m × ℝ) :
    ((horosphericalLogDiffeomorph m).symm p).time =
      Real.exp (-p.2) * ((‖p.1‖ ^ 2 + 1) / 2) + Real.exp p.2 / 2 := by
  change (hUpperIsometryEquiv (m + 1)
    (ofCoords p.1 (Real.exp p.2) (Real.exp_pos p.2))).time = _
  rw [hUpperIsometryEquiv_time]
  change Hyperbolic.tc (ofCoordsVec p.1 (Real.exp p.2)) = _
  simp only [ofCoordsVec, Hyperbolic.tc_add, Hyperbolic.tc_smul,
    MobiusBoundary.tc_horoVec, MobiusBoundary.ptInfty.tc_eq, mul_one,
    normSq_horizontal, Real.exp_neg]

private theorem horosphericalLogDiffeomorph_symm_space_castSucc (m : ℕ)
    (p : Horizontal m × ℝ) (i : Fin m) :
    ((horosphericalLogDiffeomorph m).symm p).space i.castSucc = Real.exp (-p.2) * p.1 i := by
  change (hUpperIsometryEquiv (m + 1)
    (ofCoords p.1 (Real.exp p.2) (Real.exp_pos p.2))).space i.castSucc = _
  rw [hUpperIsometryEquiv_space_apply]
  simp only [ofCoords, ofCoordsVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    MobiusBoundary.horoVec_castSucc, MobiusBoundary.ptInfty_val_castSucc,
    mul_zero, add_zero, Real.exp_neg]

private theorem horosphericalLogDiffeomorph_symm_space_last (m : ℕ) (p : Horizontal m × ℝ) :
    ((horosphericalLogDiffeomorph m).symm p).space (Fin.last m) =
      Real.exp (-p.2) * ((‖p.1‖ ^ 2 - 1) / 2) + Real.exp p.2 / 2 := by
  change (hUpperIsometryEquiv (m + 1)
    (ofCoords p.1 (Real.exp p.2) (Real.exp_pos p.2))).space (Fin.last m) = _
  rw [hUpperIsometryEquiv_space_apply]
  simp only [ofCoords, ofCoordsVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    MobiusBoundary.horoVec_last, MobiusBoundary.ptInfty_val_last, mul_one,
    normSq_horizontal, Real.exp_neg]

private theorem fderiv_horosphericalLogDiffeomorph_symm_space_castSucc (m : ℕ)
    (p v : Horizontal m × ℝ) (i : Fin m) :
    fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space i.castSucc) p v =
      Real.exp (-p.2) * (v.1 i - v.2 * p.1 i) := by
  have he : (fun q => ((horosphericalLogDiffeomorph m).symm q).space i.castSucc) =
      (fun q : Horizontal m × ℝ => Real.exp (-q.2) * q.1 i) :=
    funext (fun q => horosphericalLogDiffeomorph_symm_space_castSucc m q i)
  rw [he]
  let L : Horizontal m × ℝ →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ (Horizontal m) ℝ))
  have hL : (L : Horizontal m × ℝ → ℝ) = fun q => q.1 i := by
    funext q
    rfl
  have h := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).neg.exp).mul (L.hasFDerivAt)
  simp only [hL, Pi.neg_apply] at h
  change HasFDerivAt (fun q : Horizontal m × ℝ => Real.exp (-q.2) * q.1 i) _ p at h
  rw [h.fderiv]
  change Real.exp (-p.2) * v.1 i + p.1 i * (Real.exp (-p.2) * -v.2) = _
  ring

private theorem fderiv_horosphericalLogDiffeomorph_symm_space_last (m : ℕ)
    (p v : Horizontal m × ℝ) :
    fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space (Fin.last m)) p v =
      Real.exp (-p.2) * inner ℝ p.1 v.1 +
        v.2 * (Real.exp p.2 - Real.exp (-p.2) * (‖p.1‖ ^ 2 - 1)) / 2 := by
  have he : (fun q => ((horosphericalLogDiffeomorph m).symm q).space (Fin.last m)) =
      (fun q : Horizontal m × ℝ =>
        Real.exp (-q.2) * ((‖q.1‖ ^ 2 - 1) / 2) + Real.exp q.2 / 2) :=
    funext (horosphericalLogDiffeomorph_symm_space_last m)
  rw [he]
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  have hn := (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h := (hs.neg.exp.mul ((hn.sub_const 1).mul_const (2 : ℝ)⁻¹)).add (hs.exp.mul_const (2 : ℝ)⁻¹)
  change HasFDerivAt (fun q : Horizontal m × ℝ =>
    Real.exp (-q.2) * ((‖q.1‖ ^ 2 - 1) * (2 : ℝ)⁻¹) + Real.exp q.2 * (2 : ℝ)⁻¹) _ p at h
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

private theorem fderiv_horosphericalLogDiffeomorph_symm_time (m : ℕ)
    (p v : Horizontal m × ℝ) :
    fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).time) p v =
      Real.exp (-p.2) * inner ℝ p.1 v.1 +
        v.2 * (Real.exp p.2 - Real.exp (-p.2) * (‖p.1‖ ^ 2 + 1)) / 2 := by
  have he : (fun q => ((horosphericalLogDiffeomorph m).symm q).time) =
      (fun q : Horizontal m × ℝ =>
        Real.exp (-q.2) * ((‖q.1‖ ^ 2 + 1) / 2) + Real.exp q.2 / 2) :=
    funext (horosphericalLogDiffeomorph_symm_time m)
  rw [he]
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  have hn := (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h := (hs.neg.exp.mul ((hn.add_const 1).mul_const (2 : ℝ)⁻¹)).add (hs.exp.mul_const (2 : ℝ)⁻¹)
  change HasFDerivAt (fun q : Horizontal m × ℝ =>
    Real.exp (-q.2) * ((‖q.1‖ ^ 2 + 1) * (2 : ℝ)⁻¹) + Real.exp q.2 * (2 : ℝ)⁻¹) _ p at h
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

private theorem fderiv_horosphericalLogDiffeomorph_symm_space_apply (m : ℕ)
    (p v : Horizontal m × ℝ) (i : Fin (m + 1)) :
    (fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space) p v) i =
      fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space i) p v := by
  let L : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  have hs : DifferentiableAt ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space) p :=
    (contMDiff_space.comp (horosphericalLogDiffeomorph m).symm.contMDiff).mdifferentiableAt
      (by simp) |>.differentiableAt
  have h := L.hasFDerivAt.comp p hs.hasFDerivAt
  change HasFDerivAt (fun q => ((horosphericalLogDiffeomorph m).symm q).space i) _ p at h
  rw [h.fderiv]
  rfl

private theorem mvfderiv_space_horosphericalLogDiffeomorph_symm (m : ℕ)
    (p v : Horizontal m × ℝ) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) spaceDiffeomorph
      ((horosphericalLogDiffeomorph m).symm p)
      (mfderiv (𝓘(ℝ, Horizontal m × ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (horosphericalLogDiffeomorph m).symm p ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v)) =
      fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space) p v := by
  rw [← mvfderiv_comp_apply p (spaceDiffeomorph.contMDiff.mdifferentiableAt (by simp))
    ((horosphericalLogDiffeomorph m).symm.contMDiff.mdifferentiableAt (by simp))
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v), mvfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

private theorem mvfderiv_time_horosphericalLogDiffeomorph_symm (m : ℕ)
    (p v : Horizontal m × ℝ) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) time
      ((horosphericalLogDiffeomorph m).symm p)
      (mfderiv (𝓘(ℝ, Horizontal m × ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (horosphericalLogDiffeomorph m).symm p ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v)) =
      fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).time) p v := by
  rw [← mvfderiv_comp_apply p ((contMDiff_time (n := ∞)).mdifferentiableAt (by simp))
    ((horosphericalLogDiffeomorph m).symm.contMDiff.mdifferentiableAt (by simp))
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v), mvfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem riemannianMetric_inner_horosphericalLogDiffeomorph_symm (m : ℕ)
    (p : Horizontal m × ℝ)
    (v w : Horizontal m × ℝ) :
    riemannianMetric.inner ((horosphericalLogDiffeomorph m).symm p)
      (mfderiv (𝓘(ℝ, Horizontal m × ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (horosphericalLogDiffeomorph m).symm p ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v))
      (mfderiv (𝓘(ℝ, Horizontal m × ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (horosphericalLogDiffeomorph m).symm p ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm w)) =
      Real.exp (-2 * p.2) * inner ℝ v.1 w.1 + v.2 * w.2 := by
  rw [riemannianMetric_inner, ← ((horosphericalLogDiffeomorph m).symm p).time_sq,
    pow_two, ← div_mul_div_comm, ← mfderiv_time_apply, ← mfderiv_time_apply]
  change inner ℝ (mvfderiv _ spaceDiffeomorph _ (mfderiv _ _ _ _ ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v)))
    (mvfderiv _ spaceDiffeomorph _ (mfderiv _ _ _ _ ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm w))) -
    mvfderiv _ time _ (mfderiv _ _ _ _ ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm v)) * mvfderiv _ time _ (mfderiv _ _ _ _ ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p).symm w)) = _
  rw [mvfderiv_space_horosphericalLogDiffeomorph_symm,
    mvfderiv_space_horosphericalLogDiffeomorph_symm,
    mvfderiv_time_horosphericalLogDiffeomorph_symm,
    mvfderiv_time_horosphericalLogDiffeomorph_symm,
    fderiv_horosphericalLogDiffeomorph_symm_time,
    fderiv_horosphericalLogDiffeomorph_symm_time]
  have hinner : inner ℝ
      (fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space) p v)
      (fderiv ℝ (fun q => ((horosphericalLogDiffeomorph m).symm q).space) p w) =
        Real.exp (-p.2) ^ 2 * inner ℝ (v.1 - v.2 • p.1) (w.1 - w.2 • p.1) +
        (Real.exp (-p.2) * inner ℝ p.1 w.1 +
          w.2 * (Real.exp p.2 - Real.exp (-p.2) * (‖p.1‖ ^ 2 - 1)) / 2) *
        (Real.exp (-p.2) * inner ℝ p.1 v.1 +
          v.2 * (Real.exp p.2 - Real.exp (-p.2) * (‖p.1‖ ^ 2 - 1)) / 2) := by
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_castSucc,
      fderiv_horosphericalLogDiffeomorph_symm_space_apply,
      fderiv_horosphericalLogDiffeomorph_symm_space_castSucc,
      fderiv_horosphericalLogDiffeomorph_symm_space_last,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · ring
  rw [hinner]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v.1 p.1]
  rw [show -2 * p.2 = -p.2 + -p.2 by ring, Real.exp_add]
  simp only [Real.exp_neg]
  field_simp [Real.exp_ne_zero p.2]
  ring

end DifferentialGeometry.Hyperboloid
