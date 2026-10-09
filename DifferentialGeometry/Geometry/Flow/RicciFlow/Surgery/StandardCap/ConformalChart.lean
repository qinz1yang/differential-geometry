import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false

noncomputable section
open Bundle Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff InnerProductSpace Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def puncturedSpace : Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩

@[simp] theorem mem_puncturedSpace (x : E3) : x ∈ puncturedSpace ↔ x ≠ 0 := Iff.rfl

def conformalMap (q : S2 × ℝ) : E3 := conformalRadius q.2 • (q.1 : E3)

theorem conformalMap_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ conformalMap :=
  (contDiff_conformalRadius.contMDiff.comp contMDiff_snd).smul
    ((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst)

@[simp] theorem conformalMap_norm (q : S2 × ℝ) : ‖conformalMap q‖ = conformalRadius q.2 := by
  simp only [conformalMap, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere,
    mul_one, abs_of_pos (conformalRadius_pos q.2)]

theorem conformalMap_ne_zero (q : S2 × ℝ) : conformalMap q ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [conformalMap_norm]
  exact (conformalRadius_pos q.2).ne'

private def conformalInverse (x : puncturedSpace) : S2 × ℝ :=
  (((euclideanPolarDiffeomorph (n := 2)).symm (x : E3)).1, conformalCoordinate ‖(x : E3)‖)

private theorem conformalInverse_smooth :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ)) ∞ conformalInverse := by
  have hp : ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (fun x : puncturedSpace => (euclideanPolarDiffeomorph (n := 2)).symm (x : E3)) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := puncturedSpace)).mpr
    exact (euclideanPolarDiffeomorph (n := 2)).symm.contMDiffOn_toFun.contMDiffAt
      (isOpen_compl_singleton.mem_nhds x.property)
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : puncturedSpace => ‖(x : E3)‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := puncturedSpace)).mpr
    exact (contDiffAt_norm ℝ x.property).contMDiffAt
  have hz : ContMDiff (𝓡 3) 𝓘(ℝ) ∞
      (fun x : puncturedSpace => conformalCoordinate ‖(x : E3)‖) := by
    intro x
    have hzAt : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ conformalCoordinate ‖(x : E3)‖ :=
      (contDiffOn_conformalCoordinate.contDiffAt
        (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr x.property))).contMDiffAt
    have hcomp := hzAt.comp (f := fun y : puncturedSpace => ‖(y : E3)‖)
      (g := conformalCoordinate) x (hn x)
    exact hcomp
  exact hp.fst.prodMk hz

private theorem conformalInverse_left (q : S2 × ℝ) :
    conformalInverse ⟨conformalMap q, conformalMap_ne_zero q⟩ = q := by
  have hp := (euclideanPolarDiffeomorph (n := 2)).left_inv'
    (show (q.1, conformalRadius q.2) ∈ (euclideanPolarDiffeomorph (n := 2)).source
      from conformalRadius_pos q.2)
  apply Prod.ext
  · change (((euclideanPolarDiffeomorph (n := 2)).symm (conformalMap q)).1) = q.1
    have hfst := congrArg (fun p : S2 × ℝ => p.1) hp
    exact hfst
  · change conformalCoordinate ‖conformalMap q‖ = q.2
    rw [conformalMap_norm, conformalCoordinate_conformalRadius]

private theorem conformalInverse_right (x : puncturedSpace) :
    conformalMap (conformalInverse x) = (x : E3) := by
  change conformalRadius (conformalCoordinate ‖(x : E3)‖) •
    (((euclideanPolarDiffeomorph (n := 2)).symm (x : E3)).1 : E3) = (x : E3)
  rw [conformalRadius_conformalCoordinate (norm_pos_iff.mpr x.property)]
  have hp := (euclideanPolarDiffeomorph (n := 2)).right_inv' x.property
  change euclideanPolarMap ((euclideanPolarDiffeomorph (n := 2)).symm (x : E3)) = (x : E3) at hp
  simpa only [euclideanPolarMap, euclideanPolarDiffeomorph_symm_snd x.property] using hp

def conformalChart : (S2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), 𝓡 3⟯ puncturedSpace where
  toFun q := ⟨conformalMap q, conformalMap_ne_zero q⟩
  invFun := conformalInverse
  left_inv := conformalInverse_left
  right_inv x := Subtype.ext (conformalInverse_right x)
  contMDiff_toFun _ := codRestr_contMDiffAt
    (fun y => conformalMap_ne_zero y) conformalMap_smooth.contMDiffAt
  contMDiff_invFun := conformalInverse_smooth

@[simp] theorem conformalChart_apply (q : S2 × ℝ) :
    (conformalChart q : E3) = conformalMap q := rfl

theorem conformalChart_symm_fst_val (x : puncturedSpace) :
    ((conformalChart.symm x).1 : E3) = ‖(x : E3)‖⁻¹ • (x : E3) :=
  euclideanPolarDiffeomorph_symm_fst_val x.property

@[simp] theorem conformalChart_symm_snd (x : puncturedSpace) :
    (conformalChart.symm x).2 = conformalCoordinate ‖(x : E3)‖ := rfl

theorem conformalChart_norm (q : S2 × ℝ) : ‖(conformalChart q : E3)‖ = conformalRadius q.2 :=
  conformalMap_norm q

theorem conformalChart_cylindrical (q : S2 × ℝ) (hq : 0 ≤ q.2) :
    (conformalChart q : E3) = (transitionEnd + q.2) • (q.1 : E3) := by
  rw [conformalChart_apply, conformalMap, conformalRadius_cylindrical hq]

private theorem mfderiv_conformalRadius (z t : ℝ) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ) conformalRadius z t =
      (warpingFunction (conformalRadius z) / Real.sqrt 2) * t := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ conformalRadius z t = _
  rw [(hasDerivAt_conformalRadius z).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

private theorem mfderiv_sphere_projection (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun p : S2 × ℝ => (p.1 : E3)) q v =
      dIncl q.1 v.1 := by
  have hcomp := mfderiv_comp (I := ((𝓡 2).prod 𝓘(ℝ))) (I' := 𝓡 2)
    (I'' := 𝓡 3) q
    ((contMDiff_coe_sphere (n := 2)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)) mdifferentiableAt_fst
  have h := congrArg (fun D => D v) hcomp
  rw [mfderiv_fst] at h
  with_unfolding_all exact h

private theorem mfderiv_conformal_radius_projection (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun p : S2 × ℝ => conformalRadius p.2) q v =
      (warpingFunction (conformalRadius q.2) / Real.sqrt 2) * v.2 := by
  have hcomp := mfderiv_comp (I := ((𝓡 2).prod 𝓘(ℝ))) (I' := 𝓘(ℝ))
    (I'' := 𝓘(ℝ)) q
    (contDiff_conformalRadius.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)) mdifferentiableAt_snd
  have h := congrArg (fun D => D v) hcomp
  rw [mfderiv_snd] at h
  have h' :
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) (fun p : S2 × ℝ => conformalRadius p.2) q v =
        mfderiv 𝓘(ℝ) 𝓘(ℝ) conformalRadius q.2 v.2 := by
    with_unfolding_all exact h
  exact h'.trans (mfderiv_conformalRadius q.2 v.2)

private theorem mfderiv_conformalMap_decomposition (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) conformalMap q v =
      mvfderiv ((𝓡 2).prod 𝓘(ℝ))
          (fun p : S2 × ℝ => conformalRadius p.2) q v • (q.1 : E3) +
        conformalRadius q.2 •
          mvfderiv ((𝓡 2).prod 𝓘(ℝ))
            (fun p : S2 × ℝ => (p.1 : E3)) q v := by
  let f : S2 × ℝ → ℝ := fun q => conformalRadius q.2
  let g : S2 × ℝ → E3 := fun q => (q.1 : E3)
  have hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) f q :=
    (contDiff_conformalRadius.contMDiff.comp contMDiff_snd).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hg : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) g q :=
    ((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  calc
    mvfderiv ((𝓡 2).prod 𝓘(ℝ)) conformalMap q v =
        mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (f • g) q v := by
      rw [show conformalMap = f • g by rfl]
    _ = f q • mvfderiv ((𝓡 2).prod 𝓘(ℝ)) g q v +
        mvfderiv ((𝓡 2).prod 𝓘(ℝ)) f q v • g q := by
      rw [mvfderiv_smul hf hg]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    _ = _ := by
      simp only [f, g, add_comm]

theorem conformalMap_mfderiv (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalMap q v =
      ((warpingFunction (conformalRadius q.2) / Real.sqrt 2) * v.2) • (q.1 : E3) +
        conformalRadius q.2 • dIncl q.1 v.1 := by
  change mvfderiv ((𝓡 2).prod 𝓘(ℝ)) conformalMap q v = _
  rw [mfderiv_conformalMap_decomposition,
    mfderiv_conformal_radius_projection, mfderiv_sphere_projection]

theorem conformalChart_mfderiv_eq_ambient (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalMap q v := by
  have h := congrArg (fun D => D v) (mfderiv_comp q
    ((contMDiff_subtype_val (I := 𝓡 3) (U := puncturedSpace)).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0)
      (conformalChart q)) (conformalChart.contMDiff.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q))
  change mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalMap q v =
    mfderiv (𝓡 3) (𝓡 3) (Subtype.val : puncturedSpace → E3) (conformalChart q)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v) at h
  rw [mfderiv_subtype_val_apply] at h
  exact h.symm

theorem conformalChart_mfderiv (q : S2 × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v =
      ((warpingFunction (conformalRadius q.2) / Real.sqrt 2) * v.2) • (q.1 : E3) +
        conformalRadius q.2 • dIncl q.1 v.1 :=
  (conformalChart_mfderiv_eq_ambient q v).trans (conformalMap_mfderiv q v)

theorem conformalChart_metric_inner (q : S2 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (conformalChart q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q w) =
      (warpingFunction (conformalRadius q.2) / Real.sqrt 2) ^ 2 *
        (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [conformalChart_apply, conformalMap, conformalChart_mfderiv, conformalChart_mfderiv,
    metric_inner_polar (norm_eq_of_mem_sphere q.1)
      (dIncl_orth q.1 v.1) (dIncl_orth q.1 w.1) (conformalRadius_pos q.2),
    roundCylinderMetric_inner]
  have hscale : 2 * (warpingFunction (conformalRadius q.2) / Real.sqrt 2) ^ 2 =
      warpingFunction (conformalRadius q.2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [← hscale]
  ring

theorem conformalChart_metric_inner_exp (q : S2 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (conformalChart q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q w) =
      Real.exp (2 * conformalFactor q.2) *
        (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [conformalChart_metric_inner, exp_two_conformalFactor]

theorem conformalChart_metric_inner_cylindrical (q : S2 × ℝ) (hq : 0 ≤ q.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (conformalChart q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) conformalChart q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [conformalChart_metric_inner, conformalRadius_cylindrical hq,
    warpingFunction_eq_sqrt_two (by linarith)]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  simp only [div_self hs, one_pow, one_mul]

theorem conformalChart_linearIsometryEquiv (f : E3 ≃ₗᵢ[ℝ] E3) (q : S2 × ℝ) :
    (conformalChart (⟨f (q.1 : E3), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        (f.norm_map (q.1 : E3)).trans (norm_eq_of_mem_sphere q.1)⟩, q.2) : E3) =
      f (conformalChart q : E3) :=
  (f.map_smul (conformalRadius q.2) (q.1 : E3)).symm

end DifferentialGeometry.PDE.RicciFlow.StandardCap
